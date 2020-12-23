%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:48 EST 2020

% Result     : Theorem 12.81s
% Output     : CNFRefutation 12.90s
% Verified   : 
% Statistics : Number of formulae       :  173 (1114 expanded)
%              Number of leaves         :   52 ( 407 expanded)
%              Depth                    :   24
%              Number of atoms          :  369 (3294 expanded)
%              Number of equality atoms :   69 ( 638 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_2 > #skF_5 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

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

tff(f_215,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ! [E] :
                ( ( v1_funct_1(E)
                  & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                     => ( B = k1_xboole_0
                        | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k7_partfun1(A,E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_178,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ! [E] :
              ( ( v1_funct_1(E)
                & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
             => ! [F] :
                  ( m1_subset_1(F,B)
                 => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                   => ( B = k1_xboole_0
                      | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k1_funct_1(E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_97,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_143,axiom,(
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

tff(f_75,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_154,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_80,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_48,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_190,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(c_84,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_94,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_237,plain,(
    ! [C_150,B_151,A_152] :
      ( v5_relat_1(C_150,B_151)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_152,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_245,plain,(
    v5_relat_1('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_94,c_237])).

tff(c_88,plain,(
    m1_subset_1('#skF_12','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_98,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_96,plain,(
    v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_574,plain,(
    ! [A_203,B_204,C_205] :
      ( k2_relset_1(A_203,B_204,C_205) = k2_relat_1(C_205)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(A_203,B_204))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_582,plain,(
    k2_relset_1('#skF_8','#skF_9','#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_94,c_574])).

tff(c_90,plain,(
    m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_369,plain,(
    ! [A_175,B_176,C_177] :
      ( k1_relset_1(A_175,B_176,C_177) = k1_relat_1(C_177)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(A_175,B_176))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_376,plain,(
    k1_relset_1('#skF_9','#skF_7','#skF_11') = k1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_90,c_369])).

tff(c_86,plain,(
    r1_tarski(k2_relset_1('#skF_8','#skF_9','#skF_10'),k1_relset_1('#skF_9','#skF_7','#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_380,plain,(
    r1_tarski(k2_relset_1('#skF_8','#skF_9','#skF_10'),k1_relat_1('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_86])).

tff(c_588,plain,(
    r1_tarski(k2_relat_1('#skF_10'),k1_relat_1('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_582,c_380])).

tff(c_100,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_92,plain,(
    v1_funct_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_4341,plain,(
    ! [A_460,D_464,F_459,B_461,C_463,E_462] :
      ( k1_funct_1(k8_funct_2(B_461,C_463,A_460,D_464,E_462),F_459) = k1_funct_1(E_462,k1_funct_1(D_464,F_459))
      | k1_xboole_0 = B_461
      | ~ r1_tarski(k2_relset_1(B_461,C_463,D_464),k1_relset_1(C_463,A_460,E_462))
      | ~ m1_subset_1(F_459,B_461)
      | ~ m1_subset_1(E_462,k1_zfmisc_1(k2_zfmisc_1(C_463,A_460)))
      | ~ v1_funct_1(E_462)
      | ~ m1_subset_1(D_464,k1_zfmisc_1(k2_zfmisc_1(B_461,C_463)))
      | ~ v1_funct_2(D_464,B_461,C_463)
      | ~ v1_funct_1(D_464)
      | v1_xboole_0(C_463) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_4357,plain,(
    ! [B_461,D_464,F_459] :
      ( k1_funct_1(k8_funct_2(B_461,'#skF_9','#skF_7',D_464,'#skF_11'),F_459) = k1_funct_1('#skF_11',k1_funct_1(D_464,F_459))
      | k1_xboole_0 = B_461
      | ~ r1_tarski(k2_relset_1(B_461,'#skF_9',D_464),k1_relat_1('#skF_11'))
      | ~ m1_subset_1(F_459,B_461)
      | ~ m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_7')))
      | ~ v1_funct_1('#skF_11')
      | ~ m1_subset_1(D_464,k1_zfmisc_1(k2_zfmisc_1(B_461,'#skF_9')))
      | ~ v1_funct_2(D_464,B_461,'#skF_9')
      | ~ v1_funct_1(D_464)
      | v1_xboole_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_376,c_4341])).

tff(c_4383,plain,(
    ! [B_461,D_464,F_459] :
      ( k1_funct_1(k8_funct_2(B_461,'#skF_9','#skF_7',D_464,'#skF_11'),F_459) = k1_funct_1('#skF_11',k1_funct_1(D_464,F_459))
      | k1_xboole_0 = B_461
      | ~ r1_tarski(k2_relset_1(B_461,'#skF_9',D_464),k1_relat_1('#skF_11'))
      | ~ m1_subset_1(F_459,B_461)
      | ~ m1_subset_1(D_464,k1_zfmisc_1(k2_zfmisc_1(B_461,'#skF_9')))
      | ~ v1_funct_2(D_464,B_461,'#skF_9')
      | ~ v1_funct_1(D_464)
      | v1_xboole_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_4357])).

tff(c_4678,plain,(
    ! [B_489,D_490,F_491] :
      ( k1_funct_1(k8_funct_2(B_489,'#skF_9','#skF_7',D_490,'#skF_11'),F_491) = k1_funct_1('#skF_11',k1_funct_1(D_490,F_491))
      | k1_xboole_0 = B_489
      | ~ r1_tarski(k2_relset_1(B_489,'#skF_9',D_490),k1_relat_1('#skF_11'))
      | ~ m1_subset_1(F_491,B_489)
      | ~ m1_subset_1(D_490,k1_zfmisc_1(k2_zfmisc_1(B_489,'#skF_9')))
      | ~ v1_funct_2(D_490,B_489,'#skF_9')
      | ~ v1_funct_1(D_490) ) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_4383])).

tff(c_4683,plain,(
    ! [F_491] :
      ( k1_funct_1(k8_funct_2('#skF_8','#skF_9','#skF_7','#skF_10','#skF_11'),F_491) = k1_funct_1('#skF_11',k1_funct_1('#skF_10',F_491))
      | k1_xboole_0 = '#skF_8'
      | ~ r1_tarski(k2_relat_1('#skF_10'),k1_relat_1('#skF_11'))
      | ~ m1_subset_1(F_491,'#skF_8')
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9')))
      | ~ v1_funct_2('#skF_10','#skF_8','#skF_9')
      | ~ v1_funct_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_582,c_4678])).

tff(c_4688,plain,(
    ! [F_491] :
      ( k1_funct_1(k8_funct_2('#skF_8','#skF_9','#skF_7','#skF_10','#skF_11'),F_491) = k1_funct_1('#skF_11',k1_funct_1('#skF_10',F_491))
      | k1_xboole_0 = '#skF_8'
      | ~ m1_subset_1(F_491,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_94,c_588,c_4683])).

tff(c_4689,plain,(
    ! [F_491] :
      ( k1_funct_1(k8_funct_2('#skF_8','#skF_9','#skF_7','#skF_10','#skF_11'),F_491) = k1_funct_1('#skF_11',k1_funct_1('#skF_10',F_491))
      | ~ m1_subset_1(F_491,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_4688])).

tff(c_344,plain,(
    ! [C_166,A_167,B_168] :
      ( v1_xboole_0(C_166)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(A_167,B_168)))
      | ~ v1_xboole_0(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_352,plain,
    ( v1_xboole_0('#skF_10')
    | ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_94,c_344])).

tff(c_353,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_352])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( r2_hidden(A_13,B_14)
      | v1_xboole_0(B_14)
      | ~ m1_subset_1(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_244,plain,(
    v5_relat_1('#skF_11','#skF_7') ),
    inference(resolution,[status(thm)],[c_90,c_237])).

tff(c_144,plain,(
    ! [C_130,A_131,B_132] :
      ( v1_relat_1(C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_151,plain,(
    v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_90,c_144])).

tff(c_152,plain,(
    v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_94,c_144])).

tff(c_377,plain,(
    k1_relset_1('#skF_8','#skF_9','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_94,c_369])).

tff(c_3021,plain,(
    ! [B_384,A_385,C_386] :
      ( k1_xboole_0 = B_384
      | k1_relset_1(A_385,B_384,C_386) = A_385
      | ~ v1_funct_2(C_386,A_385,B_384)
      | ~ m1_subset_1(C_386,k1_zfmisc_1(k2_zfmisc_1(A_385,B_384))) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_3030,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relset_1('#skF_8','#skF_9','#skF_10') = '#skF_8'
    | ~ v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_94,c_3021])).

tff(c_3037,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relat_1('#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_377,c_3030])).

tff(c_3038,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_3037])).

tff(c_22,plain,(
    ! [A_17,D_56] :
      ( r2_hidden(k1_funct_1(A_17,D_56),k2_relat_1(A_17))
      | ~ r2_hidden(D_56,k1_relat_1(A_17))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_162,plain,(
    ! [A_135,B_136] :
      ( ~ r2_hidden('#skF_2'(A_135,B_136),B_136)
      | r1_tarski(A_135,B_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_172,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_10,c_162])).

tff(c_26,plain,(
    ! [A_17,C_53] :
      ( r2_hidden('#skF_6'(A_17,k2_relat_1(A_17),C_53),k1_relat_1(A_17))
      | ~ r2_hidden(C_53,k2_relat_1(A_17))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3065,plain,(
    ! [C_53] :
      ( r2_hidden('#skF_6'('#skF_10',k2_relat_1('#skF_10'),C_53),'#skF_8')
      | ~ r2_hidden(C_53,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3038,c_26])).

tff(c_3626,plain,(
    ! [C_406] :
      ( r2_hidden('#skF_6'('#skF_10',k2_relat_1('#skF_10'),C_406),'#skF_8')
      | ~ r2_hidden(C_406,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_98,c_3065])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3635,plain,(
    ! [C_406,B_6] :
      ( r2_hidden('#skF_6'('#skF_10',k2_relat_1('#skF_10'),C_406),B_6)
      | ~ r1_tarski('#skF_8',B_6)
      | ~ r2_hidden(C_406,k2_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_3626,c_6])).

tff(c_24,plain,(
    ! [A_17,C_53] :
      ( k1_funct_1(A_17,'#skF_6'(A_17,k2_relat_1(A_17),C_53)) = C_53
      | ~ r2_hidden(C_53,k2_relat_1(A_17))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1807,plain,(
    ! [A_284,D_285] :
      ( r2_hidden(k1_funct_1(A_284,D_285),k2_relat_1(A_284))
      | ~ r2_hidden(D_285,k1_relat_1(A_284))
      | ~ v1_funct_1(A_284)
      | ~ v1_relat_1(A_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_5347,plain,(
    ! [A_534,D_535,B_536] :
      ( r2_hidden(k1_funct_1(A_534,D_535),B_536)
      | ~ r1_tarski(k2_relat_1(A_534),B_536)
      | ~ r2_hidden(D_535,k1_relat_1(A_534))
      | ~ v1_funct_1(A_534)
      | ~ v1_relat_1(A_534) ) ),
    inference(resolution,[status(thm)],[c_1807,c_6])).

tff(c_14529,plain,(
    ! [A_1016,D_1017,B_1018,B_1019] :
      ( r2_hidden(k1_funct_1(A_1016,D_1017),B_1018)
      | ~ r1_tarski(B_1019,B_1018)
      | ~ r1_tarski(k2_relat_1(A_1016),B_1019)
      | ~ r2_hidden(D_1017,k1_relat_1(A_1016))
      | ~ v1_funct_1(A_1016)
      | ~ v1_relat_1(A_1016) ) ),
    inference(resolution,[status(thm)],[c_5347,c_6])).

tff(c_14579,plain,(
    ! [A_1024,D_1025] :
      ( r2_hidden(k1_funct_1(A_1024,D_1025),k1_relat_1('#skF_11'))
      | ~ r1_tarski(k2_relat_1(A_1024),k2_relat_1('#skF_10'))
      | ~ r2_hidden(D_1025,k1_relat_1(A_1024))
      | ~ v1_funct_1(A_1024)
      | ~ v1_relat_1(A_1024) ) ),
    inference(resolution,[status(thm)],[c_588,c_14529])).

tff(c_15624,plain,(
    ! [C_1059,A_1060] :
      ( r2_hidden(C_1059,k1_relat_1('#skF_11'))
      | ~ r1_tarski(k2_relat_1(A_1060),k2_relat_1('#skF_10'))
      | ~ r2_hidden('#skF_6'(A_1060,k2_relat_1(A_1060),C_1059),k1_relat_1(A_1060))
      | ~ v1_funct_1(A_1060)
      | ~ v1_relat_1(A_1060)
      | ~ r2_hidden(C_1059,k2_relat_1(A_1060))
      | ~ v1_funct_1(A_1060)
      | ~ v1_relat_1(A_1060) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_14579])).

tff(c_15632,plain,(
    ! [C_406] :
      ( r2_hidden(C_406,k1_relat_1('#skF_11'))
      | ~ r1_tarski(k2_relat_1('#skF_10'),k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r1_tarski('#skF_8',k1_relat_1('#skF_10'))
      | ~ r2_hidden(C_406,k2_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_3635,c_15624])).

tff(c_15652,plain,(
    ! [C_1061] :
      ( r2_hidden(C_1061,k1_relat_1('#skF_11'))
      | ~ r2_hidden(C_1061,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_3038,c_152,c_98,c_172,c_15632])).

tff(c_15810,plain,(
    ! [D_56] :
      ( r2_hidden(k1_funct_1('#skF_10',D_56),k1_relat_1('#skF_11'))
      | ~ r2_hidden(D_56,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_22,c_15652])).

tff(c_15961,plain,(
    ! [D_1062] :
      ( r2_hidden(k1_funct_1('#skF_10',D_1062),k1_relat_1('#skF_11'))
      | ~ r2_hidden(D_1062,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_98,c_3038,c_15810])).

tff(c_72,plain,(
    ! [A_82,B_83,C_85] :
      ( k7_partfun1(A_82,B_83,C_85) = k1_funct_1(B_83,C_85)
      | ~ r2_hidden(C_85,k1_relat_1(B_83))
      | ~ v1_funct_1(B_83)
      | ~ v5_relat_1(B_83,A_82)
      | ~ v1_relat_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_15974,plain,(
    ! [A_82,D_1062] :
      ( k7_partfun1(A_82,'#skF_11',k1_funct_1('#skF_10',D_1062)) = k1_funct_1('#skF_11',k1_funct_1('#skF_10',D_1062))
      | ~ v1_funct_1('#skF_11')
      | ~ v5_relat_1('#skF_11',A_82)
      | ~ v1_relat_1('#skF_11')
      | ~ r2_hidden(D_1062,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_15961,c_72])).

tff(c_19376,plain,(
    ! [A_1183,D_1184] :
      ( k7_partfun1(A_1183,'#skF_11',k1_funct_1('#skF_10',D_1184)) = k1_funct_1('#skF_11',k1_funct_1('#skF_10',D_1184))
      | ~ v5_relat_1('#skF_11',A_1183)
      | ~ r2_hidden(D_1184,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_92,c_15974])).

tff(c_82,plain,(
    k7_partfun1('#skF_7','#skF_11',k1_funct_1('#skF_10','#skF_12')) != k1_funct_1(k8_funct_2('#skF_8','#skF_9','#skF_7','#skF_10','#skF_11'),'#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_19382,plain,
    ( k1_funct_1(k8_funct_2('#skF_8','#skF_9','#skF_7','#skF_10','#skF_11'),'#skF_12') != k1_funct_1('#skF_11',k1_funct_1('#skF_10','#skF_12'))
    | ~ v5_relat_1('#skF_11','#skF_7')
    | ~ r2_hidden('#skF_12','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_19376,c_82])).

tff(c_19406,plain,
    ( k1_funct_1(k8_funct_2('#skF_8','#skF_9','#skF_7','#skF_10','#skF_11'),'#skF_12') != k1_funct_1('#skF_11',k1_funct_1('#skF_10','#skF_12'))
    | ~ r2_hidden('#skF_12','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_19382])).

tff(c_19464,plain,(
    ~ r2_hidden('#skF_12','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_19406])).

tff(c_19467,plain,
    ( v1_xboole_0('#skF_8')
    | ~ m1_subset_1('#skF_12','#skF_8') ),
    inference(resolution,[status(thm)],[c_16,c_19464])).

tff(c_19470,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_19467])).

tff(c_19472,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_353,c_19470])).

tff(c_19473,plain,(
    k1_funct_1(k8_funct_2('#skF_8','#skF_9','#skF_7','#skF_10','#skF_11'),'#skF_12') != k1_funct_1('#skF_11',k1_funct_1('#skF_10','#skF_12')) ),
    inference(splitRight,[status(thm)],[c_19406])).

tff(c_19491,plain,(
    ~ m1_subset_1('#skF_12','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_4689,c_19473])).

tff(c_19495,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_19491])).

tff(c_19496,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_3037])).

tff(c_20,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k2_relat_1(B_16),A_15)
      | ~ v5_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_12,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_256,plain,(
    ! [C_156,B_157,A_158] :
      ( r2_hidden(C_156,B_157)
      | ~ r2_hidden(C_156,A_158)
      | ~ r1_tarski(A_158,B_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_266,plain,(
    ! [A_159,B_160] :
      ( r2_hidden('#skF_1'(A_159),B_160)
      | ~ r1_tarski(A_159,B_160)
      | v1_xboole_0(A_159) ) ),
    inference(resolution,[status(thm)],[c_4,c_256])).

tff(c_40,plain,(
    ! [B_58,A_57] :
      ( ~ r1_tarski(B_58,A_57)
      | ~ r2_hidden(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_300,plain,(
    ! [B_163,A_164] :
      ( ~ r1_tarski(B_163,'#skF_1'(A_164))
      | ~ r1_tarski(A_164,B_163)
      | v1_xboole_0(A_164) ) ),
    inference(resolution,[status(thm)],[c_266,c_40])).

tff(c_321,plain,(
    ! [A_165] :
      ( ~ r1_tarski(A_165,k1_xboole_0)
      | v1_xboole_0(A_165) ) ),
    inference(resolution,[status(thm)],[c_12,c_300])).

tff(c_338,plain,(
    ! [B_16] :
      ( v1_xboole_0(k2_relat_1(B_16))
      | ~ v5_relat_1(B_16,k1_xboole_0)
      | ~ v1_relat_1(B_16) ) ),
    inference(resolution,[status(thm)],[c_20,c_321])).

tff(c_108,plain,(
    ! [B_120,A_121] :
      ( ~ r1_tarski(B_120,A_121)
      | ~ r2_hidden(A_121,B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_114,plain,(
    ! [A_124] :
      ( ~ r1_tarski(A_124,'#skF_1'(A_124))
      | v1_xboole_0(A_124) ) ),
    inference(resolution,[status(thm)],[c_4,c_108])).

tff(c_119,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_114])).

tff(c_421,plain,(
    ! [A_184,B_185,B_186] :
      ( r2_hidden(A_184,B_185)
      | ~ r1_tarski(B_186,B_185)
      | v1_xboole_0(B_186)
      | ~ m1_subset_1(A_184,B_186) ) ),
    inference(resolution,[status(thm)],[c_16,c_256])).

tff(c_432,plain,(
    ! [A_184] :
      ( r2_hidden(A_184,k1_relat_1('#skF_11'))
      | v1_xboole_0(k2_relset_1('#skF_8','#skF_9','#skF_10'))
      | ~ m1_subset_1(A_184,k2_relset_1('#skF_8','#skF_9','#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_380,c_421])).

tff(c_613,plain,(
    ! [A_184] :
      ( r2_hidden(A_184,k1_relat_1('#skF_11'))
      | v1_xboole_0(k2_relat_1('#skF_10'))
      | ~ m1_subset_1(A_184,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_582,c_582,c_432])).

tff(c_614,plain,(
    v1_xboole_0(k2_relat_1('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_613])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( ~ v1_xboole_0(B_12)
      | B_12 = A_11
      | ~ v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_122,plain,(
    ! [A_11] :
      ( k1_xboole_0 = A_11
      | ~ v1_xboole_0(A_11) ) ),
    inference(resolution,[status(thm)],[c_119,c_14])).

tff(c_628,plain,(
    k2_relat_1('#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_614,c_122])).

tff(c_766,plain,(
    ! [A_214,D_215] :
      ( r2_hidden(k1_funct_1(A_214,D_215),k2_relat_1(A_214))
      | ~ r2_hidden(D_215,k1_relat_1(A_214))
      | ~ v1_funct_1(A_214)
      | ~ v1_relat_1(A_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_777,plain,(
    ! [D_215] :
      ( r2_hidden(k1_funct_1('#skF_10',D_215),k1_xboole_0)
      | ~ r2_hidden(D_215,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_628,c_766])).

tff(c_783,plain,(
    ! [D_216] :
      ( r2_hidden(k1_funct_1('#skF_10',D_216),k1_xboole_0)
      | ~ r2_hidden(D_216,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_98,c_777])).

tff(c_788,plain,(
    ! [D_216] :
      ( ~ r1_tarski(k1_xboole_0,k1_funct_1('#skF_10',D_216))
      | ~ r2_hidden(D_216,k1_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_783,c_40])).

tff(c_801,plain,(
    ! [D_217] : ~ r2_hidden(D_217,k1_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_788])).

tff(c_826,plain,(
    v1_xboole_0(k1_relat_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_4,c_801])).

tff(c_835,plain,(
    k1_relat_1('#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_826,c_122])).

tff(c_1089,plain,(
    ! [B_244,A_245] :
      ( m1_subset_1(B_244,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_244),A_245)))
      | ~ r1_tarski(k2_relat_1(B_244),A_245)
      | ~ v1_funct_1(B_244)
      | ~ v1_relat_1(B_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_1118,plain,(
    ! [A_245] :
      ( m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A_245)))
      | ~ r1_tarski(k2_relat_1('#skF_10'),A_245)
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_835,c_1089])).

tff(c_1129,plain,(
    ! [A_246] : m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A_246))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_98,c_12,c_628,c_1118])).

tff(c_48,plain,(
    ! [C_68,A_65,B_66] :
      ( v1_xboole_0(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66)))
      | ~ v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1148,plain,
    ( v1_xboole_0('#skF_10')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1129,c_48])).

tff(c_1173,plain,(
    v1_xboole_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_1148])).

tff(c_1190,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_1173,c_122])).

tff(c_1220,plain,(
    '#skF_10' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1190,c_84])).

tff(c_839,plain,(
    k1_relset_1('#skF_8','#skF_9','#skF_10') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_835,c_377])).

tff(c_1200,plain,(
    k1_relset_1('#skF_8','#skF_9','#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1190,c_839])).

tff(c_70,plain,(
    ! [B_80,A_79,C_81] :
      ( k1_xboole_0 = B_80
      | k1_relset_1(A_79,B_80,C_81) = A_79
      | ~ v1_funct_2(C_81,A_79,B_80)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1662,plain,(
    ! [B_272,A_273,C_274] :
      ( B_272 = '#skF_10'
      | k1_relset_1(A_273,B_272,C_274) = A_273
      | ~ v1_funct_2(C_274,A_273,B_272)
      | ~ m1_subset_1(C_274,k1_zfmisc_1(k2_zfmisc_1(A_273,B_272))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1190,c_70])).

tff(c_1674,plain,
    ( '#skF_10' = '#skF_9'
    | k1_relset_1('#skF_8','#skF_9','#skF_10') = '#skF_8'
    | ~ v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_94,c_1662])).

tff(c_1684,plain,
    ( '#skF_10' = '#skF_9'
    | '#skF_10' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_1200,c_1674])).

tff(c_1685,plain,(
    '#skF_10' = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_1220,c_1684])).

tff(c_1710,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1685,c_1173])).

tff(c_1719,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_1710])).

tff(c_1721,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_613])).

tff(c_1724,plain,
    ( ~ v5_relat_1('#skF_10',k1_xboole_0)
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_338,c_1721])).

tff(c_1727,plain,(
    ~ v5_relat_1('#skF_10',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_1724])).

tff(c_19516,plain,(
    ~ v5_relat_1('#skF_10','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19496,c_1727])).

tff(c_19531,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_19516])).

tff(c_19533,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_352])).

tff(c_19543,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_19533,c_122])).

tff(c_19549,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_19543])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:43:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.81/5.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.90/5.31  
% 12.90/5.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.90/5.31  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_2 > #skF_5 > #skF_12 > #skF_4
% 12.90/5.31  
% 12.90/5.31  %Foreground sorts:
% 12.90/5.31  
% 12.90/5.31  
% 12.90/5.31  %Background operators:
% 12.90/5.31  
% 12.90/5.31  
% 12.90/5.31  %Foreground operators:
% 12.90/5.31  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 12.90/5.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.90/5.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.90/5.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.90/5.31  tff('#skF_11', type, '#skF_11': $i).
% 12.90/5.31  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 12.90/5.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 12.90/5.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.90/5.31  tff('#skF_7', type, '#skF_7': $i).
% 12.90/5.31  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 12.90/5.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.90/5.31  tff('#skF_10', type, '#skF_10': $i).
% 12.90/5.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.90/5.31  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 12.90/5.31  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.90/5.31  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 12.90/5.31  tff('#skF_9', type, '#skF_9': $i).
% 12.90/5.31  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 12.90/5.31  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 12.90/5.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.90/5.31  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 12.90/5.31  tff('#skF_8', type, '#skF_8': $i).
% 12.90/5.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.90/5.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.90/5.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.90/5.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.90/5.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 12.90/5.31  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 12.90/5.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.90/5.31  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 12.90/5.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.90/5.31  tff('#skF_12', type, '#skF_12': $i).
% 12.90/5.31  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 12.90/5.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.90/5.31  
% 12.90/5.34  tff(f_215, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 12.90/5.34  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 12.90/5.34  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 12.90/5.34  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 12.90/5.34  tff(f_178, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 12.90/5.34  tff(f_97, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 12.90/5.34  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 12.90/5.34  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 12.90/5.34  tff(f_143, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 12.90/5.34  tff(f_75, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 12.90/5.34  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 12.90/5.34  tff(f_154, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 12.90/5.34  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 12.90/5.34  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 12.90/5.34  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 12.90/5.34  tff(f_80, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 12.90/5.34  tff(f_48, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 12.90/5.34  tff(f_190, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 12.90/5.34  tff(c_84, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_215])).
% 12.90/5.34  tff(c_94, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(cnfTransformation, [status(thm)], [f_215])).
% 12.90/5.34  tff(c_237, plain, (![C_150, B_151, A_152]: (v5_relat_1(C_150, B_151) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_152, B_151))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 12.90/5.34  tff(c_245, plain, (v5_relat_1('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_94, c_237])).
% 12.90/5.34  tff(c_88, plain, (m1_subset_1('#skF_12', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_215])).
% 12.90/5.34  tff(c_98, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_215])).
% 12.90/5.34  tff(c_96, plain, (v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_215])).
% 12.90/5.34  tff(c_574, plain, (![A_203, B_204, C_205]: (k2_relset_1(A_203, B_204, C_205)=k2_relat_1(C_205) | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(A_203, B_204))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 12.90/5.34  tff(c_582, plain, (k2_relset_1('#skF_8', '#skF_9', '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_94, c_574])).
% 12.90/5.34  tff(c_90, plain, (m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_215])).
% 12.90/5.34  tff(c_369, plain, (![A_175, B_176, C_177]: (k1_relset_1(A_175, B_176, C_177)=k1_relat_1(C_177) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(A_175, B_176))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 12.90/5.34  tff(c_376, plain, (k1_relset_1('#skF_9', '#skF_7', '#skF_11')=k1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_90, c_369])).
% 12.90/5.34  tff(c_86, plain, (r1_tarski(k2_relset_1('#skF_8', '#skF_9', '#skF_10'), k1_relset_1('#skF_9', '#skF_7', '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_215])).
% 12.90/5.34  tff(c_380, plain, (r1_tarski(k2_relset_1('#skF_8', '#skF_9', '#skF_10'), k1_relat_1('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_376, c_86])).
% 12.90/5.34  tff(c_588, plain, (r1_tarski(k2_relat_1('#skF_10'), k1_relat_1('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_582, c_380])).
% 12.90/5.34  tff(c_100, plain, (~v1_xboole_0('#skF_9')), inference(cnfTransformation, [status(thm)], [f_215])).
% 12.90/5.34  tff(c_92, plain, (v1_funct_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_215])).
% 12.90/5.34  tff(c_4341, plain, (![A_460, D_464, F_459, B_461, C_463, E_462]: (k1_funct_1(k8_funct_2(B_461, C_463, A_460, D_464, E_462), F_459)=k1_funct_1(E_462, k1_funct_1(D_464, F_459)) | k1_xboole_0=B_461 | ~r1_tarski(k2_relset_1(B_461, C_463, D_464), k1_relset_1(C_463, A_460, E_462)) | ~m1_subset_1(F_459, B_461) | ~m1_subset_1(E_462, k1_zfmisc_1(k2_zfmisc_1(C_463, A_460))) | ~v1_funct_1(E_462) | ~m1_subset_1(D_464, k1_zfmisc_1(k2_zfmisc_1(B_461, C_463))) | ~v1_funct_2(D_464, B_461, C_463) | ~v1_funct_1(D_464) | v1_xboole_0(C_463))), inference(cnfTransformation, [status(thm)], [f_178])).
% 12.90/5.34  tff(c_4357, plain, (![B_461, D_464, F_459]: (k1_funct_1(k8_funct_2(B_461, '#skF_9', '#skF_7', D_464, '#skF_11'), F_459)=k1_funct_1('#skF_11', k1_funct_1(D_464, F_459)) | k1_xboole_0=B_461 | ~r1_tarski(k2_relset_1(B_461, '#skF_9', D_464), k1_relat_1('#skF_11')) | ~m1_subset_1(F_459, B_461) | ~m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_7'))) | ~v1_funct_1('#skF_11') | ~m1_subset_1(D_464, k1_zfmisc_1(k2_zfmisc_1(B_461, '#skF_9'))) | ~v1_funct_2(D_464, B_461, '#skF_9') | ~v1_funct_1(D_464) | v1_xboole_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_376, c_4341])).
% 12.90/5.34  tff(c_4383, plain, (![B_461, D_464, F_459]: (k1_funct_1(k8_funct_2(B_461, '#skF_9', '#skF_7', D_464, '#skF_11'), F_459)=k1_funct_1('#skF_11', k1_funct_1(D_464, F_459)) | k1_xboole_0=B_461 | ~r1_tarski(k2_relset_1(B_461, '#skF_9', D_464), k1_relat_1('#skF_11')) | ~m1_subset_1(F_459, B_461) | ~m1_subset_1(D_464, k1_zfmisc_1(k2_zfmisc_1(B_461, '#skF_9'))) | ~v1_funct_2(D_464, B_461, '#skF_9') | ~v1_funct_1(D_464) | v1_xboole_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_4357])).
% 12.90/5.34  tff(c_4678, plain, (![B_489, D_490, F_491]: (k1_funct_1(k8_funct_2(B_489, '#skF_9', '#skF_7', D_490, '#skF_11'), F_491)=k1_funct_1('#skF_11', k1_funct_1(D_490, F_491)) | k1_xboole_0=B_489 | ~r1_tarski(k2_relset_1(B_489, '#skF_9', D_490), k1_relat_1('#skF_11')) | ~m1_subset_1(F_491, B_489) | ~m1_subset_1(D_490, k1_zfmisc_1(k2_zfmisc_1(B_489, '#skF_9'))) | ~v1_funct_2(D_490, B_489, '#skF_9') | ~v1_funct_1(D_490))), inference(negUnitSimplification, [status(thm)], [c_100, c_4383])).
% 12.90/5.34  tff(c_4683, plain, (![F_491]: (k1_funct_1(k8_funct_2('#skF_8', '#skF_9', '#skF_7', '#skF_10', '#skF_11'), F_491)=k1_funct_1('#skF_11', k1_funct_1('#skF_10', F_491)) | k1_xboole_0='#skF_8' | ~r1_tarski(k2_relat_1('#skF_10'), k1_relat_1('#skF_11')) | ~m1_subset_1(F_491, '#skF_8') | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9'))) | ~v1_funct_2('#skF_10', '#skF_8', '#skF_9') | ~v1_funct_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_582, c_4678])).
% 12.90/5.34  tff(c_4688, plain, (![F_491]: (k1_funct_1(k8_funct_2('#skF_8', '#skF_9', '#skF_7', '#skF_10', '#skF_11'), F_491)=k1_funct_1('#skF_11', k1_funct_1('#skF_10', F_491)) | k1_xboole_0='#skF_8' | ~m1_subset_1(F_491, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_94, c_588, c_4683])).
% 12.90/5.34  tff(c_4689, plain, (![F_491]: (k1_funct_1(k8_funct_2('#skF_8', '#skF_9', '#skF_7', '#skF_10', '#skF_11'), F_491)=k1_funct_1('#skF_11', k1_funct_1('#skF_10', F_491)) | ~m1_subset_1(F_491, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_84, c_4688])).
% 12.90/5.34  tff(c_344, plain, (![C_166, A_167, B_168]: (v1_xboole_0(C_166) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(A_167, B_168))) | ~v1_xboole_0(A_167))), inference(cnfTransformation, [status(thm)], [f_97])).
% 12.90/5.34  tff(c_352, plain, (v1_xboole_0('#skF_10') | ~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_94, c_344])).
% 12.90/5.34  tff(c_353, plain, (~v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_352])).
% 12.90/5.34  tff(c_16, plain, (![A_13, B_14]: (r2_hidden(A_13, B_14) | v1_xboole_0(B_14) | ~m1_subset_1(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.90/5.34  tff(c_244, plain, (v5_relat_1('#skF_11', '#skF_7')), inference(resolution, [status(thm)], [c_90, c_237])).
% 12.90/5.34  tff(c_144, plain, (![C_130, A_131, B_132]: (v1_relat_1(C_130) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 12.90/5.34  tff(c_151, plain, (v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_90, c_144])).
% 12.90/5.34  tff(c_152, plain, (v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_94, c_144])).
% 12.90/5.34  tff(c_377, plain, (k1_relset_1('#skF_8', '#skF_9', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_94, c_369])).
% 12.90/5.34  tff(c_3021, plain, (![B_384, A_385, C_386]: (k1_xboole_0=B_384 | k1_relset_1(A_385, B_384, C_386)=A_385 | ~v1_funct_2(C_386, A_385, B_384) | ~m1_subset_1(C_386, k1_zfmisc_1(k2_zfmisc_1(A_385, B_384))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 12.90/5.34  tff(c_3030, plain, (k1_xboole_0='#skF_9' | k1_relset_1('#skF_8', '#skF_9', '#skF_10')='#skF_8' | ~v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_94, c_3021])).
% 12.90/5.34  tff(c_3037, plain, (k1_xboole_0='#skF_9' | k1_relat_1('#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_377, c_3030])).
% 12.90/5.34  tff(c_3038, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(splitLeft, [status(thm)], [c_3037])).
% 12.90/5.34  tff(c_22, plain, (![A_17, D_56]: (r2_hidden(k1_funct_1(A_17, D_56), k2_relat_1(A_17)) | ~r2_hidden(D_56, k1_relat_1(A_17)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.90/5.34  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.90/5.34  tff(c_162, plain, (![A_135, B_136]: (~r2_hidden('#skF_2'(A_135, B_136), B_136) | r1_tarski(A_135, B_136))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.90/5.34  tff(c_172, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_10, c_162])).
% 12.90/5.34  tff(c_26, plain, (![A_17, C_53]: (r2_hidden('#skF_6'(A_17, k2_relat_1(A_17), C_53), k1_relat_1(A_17)) | ~r2_hidden(C_53, k2_relat_1(A_17)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.90/5.34  tff(c_3065, plain, (![C_53]: (r2_hidden('#skF_6'('#skF_10', k2_relat_1('#skF_10'), C_53), '#skF_8') | ~r2_hidden(C_53, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_3038, c_26])).
% 12.90/5.34  tff(c_3626, plain, (![C_406]: (r2_hidden('#skF_6'('#skF_10', k2_relat_1('#skF_10'), C_406), '#skF_8') | ~r2_hidden(C_406, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_98, c_3065])).
% 12.90/5.34  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.90/5.34  tff(c_3635, plain, (![C_406, B_6]: (r2_hidden('#skF_6'('#skF_10', k2_relat_1('#skF_10'), C_406), B_6) | ~r1_tarski('#skF_8', B_6) | ~r2_hidden(C_406, k2_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_3626, c_6])).
% 12.90/5.34  tff(c_24, plain, (![A_17, C_53]: (k1_funct_1(A_17, '#skF_6'(A_17, k2_relat_1(A_17), C_53))=C_53 | ~r2_hidden(C_53, k2_relat_1(A_17)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.90/5.34  tff(c_1807, plain, (![A_284, D_285]: (r2_hidden(k1_funct_1(A_284, D_285), k2_relat_1(A_284)) | ~r2_hidden(D_285, k1_relat_1(A_284)) | ~v1_funct_1(A_284) | ~v1_relat_1(A_284))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.90/5.34  tff(c_5347, plain, (![A_534, D_535, B_536]: (r2_hidden(k1_funct_1(A_534, D_535), B_536) | ~r1_tarski(k2_relat_1(A_534), B_536) | ~r2_hidden(D_535, k1_relat_1(A_534)) | ~v1_funct_1(A_534) | ~v1_relat_1(A_534))), inference(resolution, [status(thm)], [c_1807, c_6])).
% 12.90/5.34  tff(c_14529, plain, (![A_1016, D_1017, B_1018, B_1019]: (r2_hidden(k1_funct_1(A_1016, D_1017), B_1018) | ~r1_tarski(B_1019, B_1018) | ~r1_tarski(k2_relat_1(A_1016), B_1019) | ~r2_hidden(D_1017, k1_relat_1(A_1016)) | ~v1_funct_1(A_1016) | ~v1_relat_1(A_1016))), inference(resolution, [status(thm)], [c_5347, c_6])).
% 12.90/5.34  tff(c_14579, plain, (![A_1024, D_1025]: (r2_hidden(k1_funct_1(A_1024, D_1025), k1_relat_1('#skF_11')) | ~r1_tarski(k2_relat_1(A_1024), k2_relat_1('#skF_10')) | ~r2_hidden(D_1025, k1_relat_1(A_1024)) | ~v1_funct_1(A_1024) | ~v1_relat_1(A_1024))), inference(resolution, [status(thm)], [c_588, c_14529])).
% 12.90/5.34  tff(c_15624, plain, (![C_1059, A_1060]: (r2_hidden(C_1059, k1_relat_1('#skF_11')) | ~r1_tarski(k2_relat_1(A_1060), k2_relat_1('#skF_10')) | ~r2_hidden('#skF_6'(A_1060, k2_relat_1(A_1060), C_1059), k1_relat_1(A_1060)) | ~v1_funct_1(A_1060) | ~v1_relat_1(A_1060) | ~r2_hidden(C_1059, k2_relat_1(A_1060)) | ~v1_funct_1(A_1060) | ~v1_relat_1(A_1060))), inference(superposition, [status(thm), theory('equality')], [c_24, c_14579])).
% 12.90/5.34  tff(c_15632, plain, (![C_406]: (r2_hidden(C_406, k1_relat_1('#skF_11')) | ~r1_tarski(k2_relat_1('#skF_10'), k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r1_tarski('#skF_8', k1_relat_1('#skF_10')) | ~r2_hidden(C_406, k2_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_3635, c_15624])).
% 12.90/5.34  tff(c_15652, plain, (![C_1061]: (r2_hidden(C_1061, k1_relat_1('#skF_11')) | ~r2_hidden(C_1061, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_3038, c_152, c_98, c_172, c_15632])).
% 12.90/5.34  tff(c_15810, plain, (![D_56]: (r2_hidden(k1_funct_1('#skF_10', D_56), k1_relat_1('#skF_11')) | ~r2_hidden(D_56, k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_22, c_15652])).
% 12.90/5.34  tff(c_15961, plain, (![D_1062]: (r2_hidden(k1_funct_1('#skF_10', D_1062), k1_relat_1('#skF_11')) | ~r2_hidden(D_1062, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_98, c_3038, c_15810])).
% 12.90/5.34  tff(c_72, plain, (![A_82, B_83, C_85]: (k7_partfun1(A_82, B_83, C_85)=k1_funct_1(B_83, C_85) | ~r2_hidden(C_85, k1_relat_1(B_83)) | ~v1_funct_1(B_83) | ~v5_relat_1(B_83, A_82) | ~v1_relat_1(B_83))), inference(cnfTransformation, [status(thm)], [f_154])).
% 12.90/5.34  tff(c_15974, plain, (![A_82, D_1062]: (k7_partfun1(A_82, '#skF_11', k1_funct_1('#skF_10', D_1062))=k1_funct_1('#skF_11', k1_funct_1('#skF_10', D_1062)) | ~v1_funct_1('#skF_11') | ~v5_relat_1('#skF_11', A_82) | ~v1_relat_1('#skF_11') | ~r2_hidden(D_1062, '#skF_8'))), inference(resolution, [status(thm)], [c_15961, c_72])).
% 12.90/5.34  tff(c_19376, plain, (![A_1183, D_1184]: (k7_partfun1(A_1183, '#skF_11', k1_funct_1('#skF_10', D_1184))=k1_funct_1('#skF_11', k1_funct_1('#skF_10', D_1184)) | ~v5_relat_1('#skF_11', A_1183) | ~r2_hidden(D_1184, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_92, c_15974])).
% 12.90/5.34  tff(c_82, plain, (k7_partfun1('#skF_7', '#skF_11', k1_funct_1('#skF_10', '#skF_12'))!=k1_funct_1(k8_funct_2('#skF_8', '#skF_9', '#skF_7', '#skF_10', '#skF_11'), '#skF_12')), inference(cnfTransformation, [status(thm)], [f_215])).
% 12.90/5.34  tff(c_19382, plain, (k1_funct_1(k8_funct_2('#skF_8', '#skF_9', '#skF_7', '#skF_10', '#skF_11'), '#skF_12')!=k1_funct_1('#skF_11', k1_funct_1('#skF_10', '#skF_12')) | ~v5_relat_1('#skF_11', '#skF_7') | ~r2_hidden('#skF_12', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_19376, c_82])).
% 12.90/5.34  tff(c_19406, plain, (k1_funct_1(k8_funct_2('#skF_8', '#skF_9', '#skF_7', '#skF_10', '#skF_11'), '#skF_12')!=k1_funct_1('#skF_11', k1_funct_1('#skF_10', '#skF_12')) | ~r2_hidden('#skF_12', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_244, c_19382])).
% 12.90/5.34  tff(c_19464, plain, (~r2_hidden('#skF_12', '#skF_8')), inference(splitLeft, [status(thm)], [c_19406])).
% 12.90/5.34  tff(c_19467, plain, (v1_xboole_0('#skF_8') | ~m1_subset_1('#skF_12', '#skF_8')), inference(resolution, [status(thm)], [c_16, c_19464])).
% 12.90/5.34  tff(c_19470, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_19467])).
% 12.90/5.34  tff(c_19472, plain, $false, inference(negUnitSimplification, [status(thm)], [c_353, c_19470])).
% 12.90/5.34  tff(c_19473, plain, (k1_funct_1(k8_funct_2('#skF_8', '#skF_9', '#skF_7', '#skF_10', '#skF_11'), '#skF_12')!=k1_funct_1('#skF_11', k1_funct_1('#skF_10', '#skF_12'))), inference(splitRight, [status(thm)], [c_19406])).
% 12.90/5.34  tff(c_19491, plain, (~m1_subset_1('#skF_12', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_4689, c_19473])).
% 12.90/5.34  tff(c_19495, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_19491])).
% 12.90/5.34  tff(c_19496, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_3037])).
% 12.90/5.34  tff(c_20, plain, (![B_16, A_15]: (r1_tarski(k2_relat_1(B_16), A_15) | ~v5_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.90/5.34  tff(c_12, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 12.90/5.34  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.90/5.34  tff(c_256, plain, (![C_156, B_157, A_158]: (r2_hidden(C_156, B_157) | ~r2_hidden(C_156, A_158) | ~r1_tarski(A_158, B_157))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.90/5.34  tff(c_266, plain, (![A_159, B_160]: (r2_hidden('#skF_1'(A_159), B_160) | ~r1_tarski(A_159, B_160) | v1_xboole_0(A_159))), inference(resolution, [status(thm)], [c_4, c_256])).
% 12.90/5.34  tff(c_40, plain, (![B_58, A_57]: (~r1_tarski(B_58, A_57) | ~r2_hidden(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_80])).
% 12.90/5.34  tff(c_300, plain, (![B_163, A_164]: (~r1_tarski(B_163, '#skF_1'(A_164)) | ~r1_tarski(A_164, B_163) | v1_xboole_0(A_164))), inference(resolution, [status(thm)], [c_266, c_40])).
% 12.90/5.34  tff(c_321, plain, (![A_165]: (~r1_tarski(A_165, k1_xboole_0) | v1_xboole_0(A_165))), inference(resolution, [status(thm)], [c_12, c_300])).
% 12.90/5.34  tff(c_338, plain, (![B_16]: (v1_xboole_0(k2_relat_1(B_16)) | ~v5_relat_1(B_16, k1_xboole_0) | ~v1_relat_1(B_16))), inference(resolution, [status(thm)], [c_20, c_321])).
% 12.90/5.34  tff(c_108, plain, (![B_120, A_121]: (~r1_tarski(B_120, A_121) | ~r2_hidden(A_121, B_120))), inference(cnfTransformation, [status(thm)], [f_80])).
% 12.90/5.34  tff(c_114, plain, (![A_124]: (~r1_tarski(A_124, '#skF_1'(A_124)) | v1_xboole_0(A_124))), inference(resolution, [status(thm)], [c_4, c_108])).
% 12.90/5.34  tff(c_119, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_114])).
% 12.90/5.34  tff(c_421, plain, (![A_184, B_185, B_186]: (r2_hidden(A_184, B_185) | ~r1_tarski(B_186, B_185) | v1_xboole_0(B_186) | ~m1_subset_1(A_184, B_186))), inference(resolution, [status(thm)], [c_16, c_256])).
% 12.90/5.34  tff(c_432, plain, (![A_184]: (r2_hidden(A_184, k1_relat_1('#skF_11')) | v1_xboole_0(k2_relset_1('#skF_8', '#skF_9', '#skF_10')) | ~m1_subset_1(A_184, k2_relset_1('#skF_8', '#skF_9', '#skF_10')))), inference(resolution, [status(thm)], [c_380, c_421])).
% 12.90/5.34  tff(c_613, plain, (![A_184]: (r2_hidden(A_184, k1_relat_1('#skF_11')) | v1_xboole_0(k2_relat_1('#skF_10')) | ~m1_subset_1(A_184, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_582, c_582, c_432])).
% 12.90/5.34  tff(c_614, plain, (v1_xboole_0(k2_relat_1('#skF_10'))), inference(splitLeft, [status(thm)], [c_613])).
% 12.90/5.34  tff(c_14, plain, (![B_12, A_11]: (~v1_xboole_0(B_12) | B_12=A_11 | ~v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.90/5.34  tff(c_122, plain, (![A_11]: (k1_xboole_0=A_11 | ~v1_xboole_0(A_11))), inference(resolution, [status(thm)], [c_119, c_14])).
% 12.90/5.34  tff(c_628, plain, (k2_relat_1('#skF_10')=k1_xboole_0), inference(resolution, [status(thm)], [c_614, c_122])).
% 12.90/5.34  tff(c_766, plain, (![A_214, D_215]: (r2_hidden(k1_funct_1(A_214, D_215), k2_relat_1(A_214)) | ~r2_hidden(D_215, k1_relat_1(A_214)) | ~v1_funct_1(A_214) | ~v1_relat_1(A_214))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.90/5.34  tff(c_777, plain, (![D_215]: (r2_hidden(k1_funct_1('#skF_10', D_215), k1_xboole_0) | ~r2_hidden(D_215, k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_628, c_766])).
% 12.90/5.34  tff(c_783, plain, (![D_216]: (r2_hidden(k1_funct_1('#skF_10', D_216), k1_xboole_0) | ~r2_hidden(D_216, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_98, c_777])).
% 12.90/5.34  tff(c_788, plain, (![D_216]: (~r1_tarski(k1_xboole_0, k1_funct_1('#skF_10', D_216)) | ~r2_hidden(D_216, k1_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_783, c_40])).
% 12.90/5.34  tff(c_801, plain, (![D_217]: (~r2_hidden(D_217, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_788])).
% 12.90/5.34  tff(c_826, plain, (v1_xboole_0(k1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_4, c_801])).
% 12.90/5.34  tff(c_835, plain, (k1_relat_1('#skF_10')=k1_xboole_0), inference(resolution, [status(thm)], [c_826, c_122])).
% 12.90/5.34  tff(c_1089, plain, (![B_244, A_245]: (m1_subset_1(B_244, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_244), A_245))) | ~r1_tarski(k2_relat_1(B_244), A_245) | ~v1_funct_1(B_244) | ~v1_relat_1(B_244))), inference(cnfTransformation, [status(thm)], [f_190])).
% 12.90/5.34  tff(c_1118, plain, (![A_245]: (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A_245))) | ~r1_tarski(k2_relat_1('#skF_10'), A_245) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_835, c_1089])).
% 12.90/5.34  tff(c_1129, plain, (![A_246]: (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A_246))))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_98, c_12, c_628, c_1118])).
% 12.90/5.34  tff(c_48, plain, (![C_68, A_65, B_66]: (v1_xboole_0(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))) | ~v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_97])).
% 12.90/5.34  tff(c_1148, plain, (v1_xboole_0('#skF_10') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_1129, c_48])).
% 12.90/5.34  tff(c_1173, plain, (v1_xboole_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_119, c_1148])).
% 12.90/5.34  tff(c_1190, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_1173, c_122])).
% 12.90/5.34  tff(c_1220, plain, ('#skF_10'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1190, c_84])).
% 12.90/5.34  tff(c_839, plain, (k1_relset_1('#skF_8', '#skF_9', '#skF_10')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_835, c_377])).
% 12.90/5.34  tff(c_1200, plain, (k1_relset_1('#skF_8', '#skF_9', '#skF_10')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1190, c_839])).
% 12.90/5.34  tff(c_70, plain, (![B_80, A_79, C_81]: (k1_xboole_0=B_80 | k1_relset_1(A_79, B_80, C_81)=A_79 | ~v1_funct_2(C_81, A_79, B_80) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 12.90/5.34  tff(c_1662, plain, (![B_272, A_273, C_274]: (B_272='#skF_10' | k1_relset_1(A_273, B_272, C_274)=A_273 | ~v1_funct_2(C_274, A_273, B_272) | ~m1_subset_1(C_274, k1_zfmisc_1(k2_zfmisc_1(A_273, B_272))))), inference(demodulation, [status(thm), theory('equality')], [c_1190, c_70])).
% 12.90/5.34  tff(c_1674, plain, ('#skF_10'='#skF_9' | k1_relset_1('#skF_8', '#skF_9', '#skF_10')='#skF_8' | ~v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_94, c_1662])).
% 12.90/5.34  tff(c_1684, plain, ('#skF_10'='#skF_9' | '#skF_10'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_1200, c_1674])).
% 12.90/5.34  tff(c_1685, plain, ('#skF_10'='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_1220, c_1684])).
% 12.90/5.34  tff(c_1710, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1685, c_1173])).
% 12.90/5.34  tff(c_1719, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_1710])).
% 12.90/5.34  tff(c_1721, plain, (~v1_xboole_0(k2_relat_1('#skF_10'))), inference(splitRight, [status(thm)], [c_613])).
% 12.90/5.34  tff(c_1724, plain, (~v5_relat_1('#skF_10', k1_xboole_0) | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_338, c_1721])).
% 12.90/5.34  tff(c_1727, plain, (~v5_relat_1('#skF_10', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_152, c_1724])).
% 12.90/5.34  tff(c_19516, plain, (~v5_relat_1('#skF_10', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_19496, c_1727])).
% 12.90/5.34  tff(c_19531, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_245, c_19516])).
% 12.90/5.34  tff(c_19533, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_352])).
% 12.90/5.34  tff(c_19543, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_19533, c_122])).
% 12.90/5.34  tff(c_19549, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_19543])).
% 12.90/5.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.90/5.34  
% 12.90/5.34  Inference rules
% 12.90/5.34  ----------------------
% 12.90/5.34  #Ref     : 2
% 12.90/5.34  #Sup     : 4214
% 12.90/5.34  #Fact    : 0
% 12.90/5.34  #Define  : 0
% 12.90/5.34  #Split   : 35
% 12.90/5.34  #Chain   : 0
% 12.90/5.34  #Close   : 0
% 12.90/5.34  
% 12.90/5.34  Ordering : KBO
% 12.90/5.34  
% 12.90/5.34  Simplification rules
% 12.90/5.34  ----------------------
% 12.90/5.34  #Subsume      : 2074
% 12.90/5.34  #Demod        : 2365
% 12.90/5.34  #Tautology    : 471
% 12.90/5.34  #SimpNegUnit  : 167
% 12.90/5.34  #BackRed      : 144
% 12.90/5.34  
% 12.90/5.34  #Partial instantiations: 0
% 12.90/5.34  #Strategies tried      : 1
% 12.90/5.34  
% 12.90/5.34  Timing (in seconds)
% 12.90/5.34  ----------------------
% 12.90/5.34  Preprocessing        : 0.41
% 12.90/5.34  Parsing              : 0.21
% 12.90/5.34  CNF conversion       : 0.04
% 12.90/5.34  Main loop            : 4.08
% 12.90/5.34  Inferencing          : 1.02
% 12.90/5.34  Reduction            : 1.19
% 12.90/5.34  Demodulation         : 0.80
% 12.90/5.34  BG Simplification    : 0.10
% 12.90/5.34  Subsumption          : 1.49
% 12.90/5.34  Abstraction          : 0.13
% 12.90/5.34  MUC search           : 0.00
% 12.90/5.34  Cooper               : 0.00
% 12.90/5.34  Total                : 4.54
% 12.90/5.34  Index Insertion      : 0.00
% 12.90/5.34  Index Deletion       : 0.00
% 12.90/5.34  Index Matching       : 0.00
% 12.90/5.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
