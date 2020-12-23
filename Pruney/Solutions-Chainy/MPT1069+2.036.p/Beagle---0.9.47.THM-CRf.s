%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:50 EST 2020

% Result     : Theorem 8.84s
% Output     : CNFRefutation 8.84s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 522 expanded)
%              Number of leaves         :   49 ( 205 expanded)
%              Depth                    :   19
%              Number of atoms          :  323 (1777 expanded)
%              Number of equality atoms :   62 ( 411 expanded)
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

tff(f_166,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_141,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_106,axiom,(
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

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_65,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_44,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_117,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(c_82,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_70,plain,(
    m1_subset_1('#skF_12','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_80,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_78,plain,(
    v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_76,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_378,plain,(
    ! [A_164,B_165,C_166] :
      ( k2_relset_1(A_164,B_165,C_166) = k2_relat_1(C_166)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_386,plain,(
    k2_relset_1('#skF_8','#skF_9','#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_76,c_378])).

tff(c_72,plain,(
    m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_211,plain,(
    ! [A_137,B_138,C_139] :
      ( k1_relset_1(A_137,B_138,C_139) = k1_relat_1(C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_218,plain,(
    k1_relset_1('#skF_9','#skF_7','#skF_11') = k1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_72,c_211])).

tff(c_68,plain,(
    r1_tarski(k2_relset_1('#skF_8','#skF_9','#skF_10'),k1_relset_1('#skF_9','#skF_7','#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_220,plain,(
    r1_tarski(k2_relset_1('#skF_8','#skF_9','#skF_10'),k1_relat_1('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_68])).

tff(c_392,plain,(
    r1_tarski(k2_relat_1('#skF_10'),k1_relat_1('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_220])).

tff(c_74,plain,(
    v1_funct_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_3067,plain,(
    ! [B_393,C_397,F_392,A_395,D_394,E_396] :
      ( k1_funct_1(k8_funct_2(B_393,C_397,A_395,D_394,E_396),F_392) = k1_funct_1(E_396,k1_funct_1(D_394,F_392))
      | k1_xboole_0 = B_393
      | ~ r1_tarski(k2_relset_1(B_393,C_397,D_394),k1_relset_1(C_397,A_395,E_396))
      | ~ m1_subset_1(F_392,B_393)
      | ~ m1_subset_1(E_396,k1_zfmisc_1(k2_zfmisc_1(C_397,A_395)))
      | ~ v1_funct_1(E_396)
      | ~ m1_subset_1(D_394,k1_zfmisc_1(k2_zfmisc_1(B_393,C_397)))
      | ~ v1_funct_2(D_394,B_393,C_397)
      | ~ v1_funct_1(D_394)
      | v1_xboole_0(C_397) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_3075,plain,(
    ! [B_393,D_394,F_392] :
      ( k1_funct_1(k8_funct_2(B_393,'#skF_9','#skF_7',D_394,'#skF_11'),F_392) = k1_funct_1('#skF_11',k1_funct_1(D_394,F_392))
      | k1_xboole_0 = B_393
      | ~ r1_tarski(k2_relset_1(B_393,'#skF_9',D_394),k1_relat_1('#skF_11'))
      | ~ m1_subset_1(F_392,B_393)
      | ~ m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_7')))
      | ~ v1_funct_1('#skF_11')
      | ~ m1_subset_1(D_394,k1_zfmisc_1(k2_zfmisc_1(B_393,'#skF_9')))
      | ~ v1_funct_2(D_394,B_393,'#skF_9')
      | ~ v1_funct_1(D_394)
      | v1_xboole_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_3067])).

tff(c_3088,plain,(
    ! [B_393,D_394,F_392] :
      ( k1_funct_1(k8_funct_2(B_393,'#skF_9','#skF_7',D_394,'#skF_11'),F_392) = k1_funct_1('#skF_11',k1_funct_1(D_394,F_392))
      | k1_xboole_0 = B_393
      | ~ r1_tarski(k2_relset_1(B_393,'#skF_9',D_394),k1_relat_1('#skF_11'))
      | ~ m1_subset_1(F_392,B_393)
      | ~ m1_subset_1(D_394,k1_zfmisc_1(k2_zfmisc_1(B_393,'#skF_9')))
      | ~ v1_funct_2(D_394,B_393,'#skF_9')
      | ~ v1_funct_1(D_394)
      | v1_xboole_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_3075])).

tff(c_3307,plain,(
    ! [B_411,D_412,F_413] :
      ( k1_funct_1(k8_funct_2(B_411,'#skF_9','#skF_7',D_412,'#skF_11'),F_413) = k1_funct_1('#skF_11',k1_funct_1(D_412,F_413))
      | k1_xboole_0 = B_411
      | ~ r1_tarski(k2_relset_1(B_411,'#skF_9',D_412),k1_relat_1('#skF_11'))
      | ~ m1_subset_1(F_413,B_411)
      | ~ m1_subset_1(D_412,k1_zfmisc_1(k2_zfmisc_1(B_411,'#skF_9')))
      | ~ v1_funct_2(D_412,B_411,'#skF_9')
      | ~ v1_funct_1(D_412) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_3088])).

tff(c_3309,plain,(
    ! [F_413] :
      ( k1_funct_1(k8_funct_2('#skF_8','#skF_9','#skF_7','#skF_10','#skF_11'),F_413) = k1_funct_1('#skF_11',k1_funct_1('#skF_10',F_413))
      | k1_xboole_0 = '#skF_8'
      | ~ r1_tarski(k2_relat_1('#skF_10'),k1_relat_1('#skF_11'))
      | ~ m1_subset_1(F_413,'#skF_8')
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9')))
      | ~ v1_funct_2('#skF_10','#skF_8','#skF_9')
      | ~ v1_funct_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_386,c_3307])).

tff(c_3314,plain,(
    ! [F_413] :
      ( k1_funct_1(k8_funct_2('#skF_8','#skF_9','#skF_7','#skF_10','#skF_11'),F_413) = k1_funct_1('#skF_11',k1_funct_1('#skF_10',F_413))
      | k1_xboole_0 = '#skF_8'
      | ~ m1_subset_1(F_413,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_392,c_3309])).

tff(c_3315,plain,(
    ! [F_413] :
      ( k1_funct_1(k8_funct_2('#skF_8','#skF_9','#skF_7','#skF_10','#skF_11'),F_413) = k1_funct_1('#skF_11',k1_funct_1('#skF_10',F_413))
      | ~ m1_subset_1(F_413,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_3314])).

tff(c_219,plain,(
    k1_relset_1('#skF_8','#skF_9','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_76,c_211])).

tff(c_1377,plain,(
    ! [B_266,A_267,C_268] :
      ( k1_xboole_0 = B_266
      | k1_relset_1(A_267,B_266,C_268) = A_267
      | ~ v1_funct_2(C_268,A_267,B_266)
      | ~ m1_subset_1(C_268,k1_zfmisc_1(k2_zfmisc_1(A_267,B_266))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1383,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relset_1('#skF_8','#skF_9','#skF_10') = '#skF_8'
    | ~ v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_76,c_1377])).

tff(c_1388,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relat_1('#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_219,c_1383])).

tff(c_1389,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1388])).

tff(c_108,plain,(
    ! [C_113,A_114,B_115] :
      ( v1_relat_1(C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_116,plain,(
    v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_76,c_108])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1300,plain,(
    ! [A_261,C_262] :
      ( r2_hidden('#skF_6'(A_261,k2_relat_1(A_261),C_262),k1_relat_1(A_261))
      | ~ r2_hidden(C_262,k2_relat_1(A_261))
      | ~ v1_funct_1(A_261)
      | ~ v1_relat_1(A_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1316,plain,(
    ! [A_263,C_264] :
      ( ~ v1_xboole_0(k1_relat_1(A_263))
      | ~ r2_hidden(C_264,k2_relat_1(A_263))
      | ~ v1_funct_1(A_263)
      | ~ v1_relat_1(A_263) ) ),
    inference(resolution,[status(thm)],[c_1300,c_2])).

tff(c_1356,plain,(
    ! [A_265] :
      ( ~ v1_xboole_0(k1_relat_1(A_265))
      | ~ v1_funct_1(A_265)
      | ~ v1_relat_1(A_265)
      | v1_xboole_0(k2_relat_1(A_265)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1316])).

tff(c_14,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( r2_hidden(A_12,B_13)
      | v1_xboole_0(B_13)
      | ~ m1_subset_1(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_201,plain,(
    ! [C_134,B_135,A_136] :
      ( r2_hidden(C_134,B_135)
      | ~ r2_hidden(C_134,A_136)
      | ~ r1_tarski(A_136,B_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_302,plain,(
    ! [A_150,B_151,B_152] :
      ( r2_hidden(A_150,B_151)
      | ~ r1_tarski(B_152,B_151)
      | v1_xboole_0(B_152)
      | ~ m1_subset_1(A_150,B_152) ) ),
    inference(resolution,[status(thm)],[c_16,c_201])).

tff(c_311,plain,(
    ! [A_150] :
      ( r2_hidden(A_150,k1_relat_1('#skF_11'))
      | v1_xboole_0(k2_relset_1('#skF_8','#skF_9','#skF_10'))
      | ~ m1_subset_1(A_150,k2_relset_1('#skF_8','#skF_9','#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_220,c_302])).

tff(c_411,plain,(
    ! [A_150] :
      ( r2_hidden(A_150,k1_relat_1('#skF_11'))
      | v1_xboole_0(k2_relat_1('#skF_10'))
      | ~ m1_subset_1(A_150,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_386,c_311])).

tff(c_412,plain,(
    v1_xboole_0(k2_relat_1('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_411])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_416,plain,(
    k2_relat_1('#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_412,c_12])).

tff(c_444,plain,(
    ! [A_172,D_173] :
      ( r2_hidden(k1_funct_1(A_172,D_173),k2_relat_1(A_172))
      | ~ r2_hidden(D_173,k1_relat_1(A_172))
      | ~ v1_funct_1(A_172)
      | ~ v1_relat_1(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_455,plain,(
    ! [D_173] :
      ( r2_hidden(k1_funct_1('#skF_10',D_173),k1_xboole_0)
      | ~ r2_hidden(D_173,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_416,c_444])).

tff(c_461,plain,(
    ! [D_174] :
      ( r2_hidden(k1_funct_1('#skF_10',D_174),k1_xboole_0)
      | ~ r2_hidden(D_174,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_80,c_455])).

tff(c_36,plain,(
    ! [B_55,A_54] :
      ( ~ r1_tarski(B_55,A_54)
      | ~ r2_hidden(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_466,plain,(
    ! [D_174] :
      ( ~ r1_tarski(k1_xboole_0,k1_funct_1('#skF_10',D_174))
      | ~ r2_hidden(D_174,k1_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_461,c_36])).

tff(c_479,plain,(
    ! [D_175] : ~ r2_hidden(D_175,k1_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_466])).

tff(c_504,plain,(
    v1_xboole_0(k1_relat_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_4,c_479])).

tff(c_508,plain,(
    k1_relat_1('#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_504,c_12])).

tff(c_511,plain,(
    k1_relset_1('#skF_8','#skF_9','#skF_10') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_508,c_219])).

tff(c_828,plain,(
    ! [B_207,A_208,C_209] :
      ( k1_xboole_0 = B_207
      | k1_relset_1(A_208,B_207,C_209) = A_208
      | ~ v1_funct_2(C_209,A_208,B_207)
      | ~ m1_subset_1(C_209,k1_zfmisc_1(k2_zfmisc_1(A_208,B_207))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_834,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relset_1('#skF_8','#skF_9','#skF_10') = '#skF_8'
    | ~ v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_76,c_828])).

tff(c_839,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_511,c_834])).

tff(c_840,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_839])).

tff(c_91,plain,(
    ! [B_108,A_109] :
      ( ~ r1_tarski(B_108,A_109)
      | ~ r2_hidden(A_109,B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_96,plain,(
    ! [A_110] :
      ( ~ r1_tarski(A_110,'#skF_1'(A_110))
      | v1_xboole_0(A_110) ) ),
    inference(resolution,[status(thm)],[c_4,c_91])).

tff(c_101,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_96])).

tff(c_855,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_840,c_101])).

tff(c_860,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_855])).

tff(c_862,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_411])).

tff(c_1365,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_1356,c_862])).

tff(c_1375,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_80,c_1365])).

tff(c_1390,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1389,c_1375])).

tff(c_164,plain,(
    ! [C_125,B_126,A_127] :
      ( v5_relat_1(C_125,B_126)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_127,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_171,plain,(
    v5_relat_1('#skF_11','#skF_7') ),
    inference(resolution,[status(thm)],[c_72,c_164])).

tff(c_115,plain,(
    v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_72,c_108])).

tff(c_18,plain,(
    ! [A_14,D_53] :
      ( r2_hidden(k1_funct_1(A_14,D_53),k2_relat_1(A_14))
      | ~ r2_hidden(D_53,k1_relat_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_131,plain,(
    ! [A_118,B_119] :
      ( r2_hidden('#skF_2'(A_118,B_119),A_118)
      | r1_tarski(A_118,B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_142,plain,(
    ! [A_118] : r1_tarski(A_118,A_118) ),
    inference(resolution,[status(thm)],[c_131,c_8])).

tff(c_22,plain,(
    ! [A_14,C_50] :
      ( r2_hidden('#skF_6'(A_14,k2_relat_1(A_14),C_50),k1_relat_1(A_14))
      | ~ r2_hidden(C_50,k2_relat_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1395,plain,(
    ! [C_50] :
      ( r2_hidden('#skF_6'('#skF_10',k2_relat_1('#skF_10'),C_50),'#skF_8')
      | ~ r2_hidden(C_50,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1389,c_22])).

tff(c_1504,plain,(
    ! [C_272] :
      ( r2_hidden('#skF_6'('#skF_10',k2_relat_1('#skF_10'),C_272),'#skF_8')
      | ~ r2_hidden(C_272,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_80,c_1395])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1513,plain,(
    ! [C_272,B_6] :
      ( r2_hidden('#skF_6'('#skF_10',k2_relat_1('#skF_10'),C_272),B_6)
      | ~ r1_tarski('#skF_8',B_6)
      | ~ r2_hidden(C_272,k2_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_1504,c_6])).

tff(c_20,plain,(
    ! [A_14,C_50] :
      ( k1_funct_1(A_14,'#skF_6'(A_14,k2_relat_1(A_14),C_50)) = C_50
      | ~ r2_hidden(C_50,k2_relat_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_934,plain,(
    ! [A_222,D_223] :
      ( r2_hidden(k1_funct_1(A_222,D_223),k2_relat_1(A_222))
      | ~ r2_hidden(D_223,k1_relat_1(A_222))
      | ~ v1_funct_1(A_222)
      | ~ v1_relat_1(A_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2059,plain,(
    ! [A_317,D_318,B_319] :
      ( r2_hidden(k1_funct_1(A_317,D_318),B_319)
      | ~ r1_tarski(k2_relat_1(A_317),B_319)
      | ~ r2_hidden(D_318,k1_relat_1(A_317))
      | ~ v1_funct_1(A_317)
      | ~ v1_relat_1(A_317) ) ),
    inference(resolution,[status(thm)],[c_934,c_6])).

tff(c_6825,plain,(
    ! [A_686,D_687,B_688,B_689] :
      ( r2_hidden(k1_funct_1(A_686,D_687),B_688)
      | ~ r1_tarski(B_689,B_688)
      | ~ r1_tarski(k2_relat_1(A_686),B_689)
      | ~ r2_hidden(D_687,k1_relat_1(A_686))
      | ~ v1_funct_1(A_686)
      | ~ v1_relat_1(A_686) ) ),
    inference(resolution,[status(thm)],[c_2059,c_6])).

tff(c_6847,plain,(
    ! [A_690,D_691] :
      ( r2_hidden(k1_funct_1(A_690,D_691),k1_relat_1('#skF_11'))
      | ~ r1_tarski(k2_relat_1(A_690),k2_relat_1('#skF_10'))
      | ~ r2_hidden(D_691,k1_relat_1(A_690))
      | ~ v1_funct_1(A_690)
      | ~ v1_relat_1(A_690) ) ),
    inference(resolution,[status(thm)],[c_392,c_6825])).

tff(c_7750,plain,(
    ! [C_725,A_726] :
      ( r2_hidden(C_725,k1_relat_1('#skF_11'))
      | ~ r1_tarski(k2_relat_1(A_726),k2_relat_1('#skF_10'))
      | ~ r2_hidden('#skF_6'(A_726,k2_relat_1(A_726),C_725),k1_relat_1(A_726))
      | ~ v1_funct_1(A_726)
      | ~ v1_relat_1(A_726)
      | ~ r2_hidden(C_725,k2_relat_1(A_726))
      | ~ v1_funct_1(A_726)
      | ~ v1_relat_1(A_726) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_6847])).

tff(c_7758,plain,(
    ! [C_272] :
      ( r2_hidden(C_272,k1_relat_1('#skF_11'))
      | ~ r1_tarski(k2_relat_1('#skF_10'),k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r1_tarski('#skF_8',k1_relat_1('#skF_10'))
      | ~ r2_hidden(C_272,k2_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_1513,c_7750])).

tff(c_7785,plain,(
    ! [C_727] :
      ( r2_hidden(C_727,k1_relat_1('#skF_11'))
      | ~ r2_hidden(C_727,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_1389,c_116,c_80,c_142,c_7758])).

tff(c_7931,plain,(
    ! [D_53] :
      ( r2_hidden(k1_funct_1('#skF_10',D_53),k1_relat_1('#skF_11'))
      | ~ r2_hidden(D_53,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_18,c_7785])).

tff(c_8039,plain,(
    ! [D_728] :
      ( r2_hidden(k1_funct_1('#skF_10',D_728),k1_relat_1('#skF_11'))
      | ~ r2_hidden(D_728,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_80,c_1389,c_7931])).

tff(c_60,plain,(
    ! [A_71,B_72,C_74] :
      ( k7_partfun1(A_71,B_72,C_74) = k1_funct_1(B_72,C_74)
      | ~ r2_hidden(C_74,k1_relat_1(B_72))
      | ~ v1_funct_1(B_72)
      | ~ v5_relat_1(B_72,A_71)
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_8047,plain,(
    ! [A_71,D_728] :
      ( k7_partfun1(A_71,'#skF_11',k1_funct_1('#skF_10',D_728)) = k1_funct_1('#skF_11',k1_funct_1('#skF_10',D_728))
      | ~ v1_funct_1('#skF_11')
      | ~ v5_relat_1('#skF_11',A_71)
      | ~ v1_relat_1('#skF_11')
      | ~ r2_hidden(D_728,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_8039,c_60])).

tff(c_9155,plain,(
    ! [A_764,D_765] :
      ( k7_partfun1(A_764,'#skF_11',k1_funct_1('#skF_10',D_765)) = k1_funct_1('#skF_11',k1_funct_1('#skF_10',D_765))
      | ~ v5_relat_1('#skF_11',A_764)
      | ~ r2_hidden(D_765,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_74,c_8047])).

tff(c_64,plain,(
    k7_partfun1('#skF_7','#skF_11',k1_funct_1('#skF_10','#skF_12')) != k1_funct_1(k8_funct_2('#skF_8','#skF_9','#skF_7','#skF_10','#skF_11'),'#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_9161,plain,
    ( k1_funct_1(k8_funct_2('#skF_8','#skF_9','#skF_7','#skF_10','#skF_11'),'#skF_12') != k1_funct_1('#skF_11',k1_funct_1('#skF_10','#skF_12'))
    | ~ v5_relat_1('#skF_11','#skF_7')
    | ~ r2_hidden('#skF_12','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_9155,c_64])).

tff(c_9185,plain,
    ( k1_funct_1(k8_funct_2('#skF_8','#skF_9','#skF_7','#skF_10','#skF_11'),'#skF_12') != k1_funct_1('#skF_11',k1_funct_1('#skF_10','#skF_12'))
    | ~ r2_hidden('#skF_12','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_9161])).

tff(c_9194,plain,(
    ~ r2_hidden('#skF_12','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_9185])).

tff(c_9197,plain,
    ( v1_xboole_0('#skF_8')
    | ~ m1_subset_1('#skF_12','#skF_8') ),
    inference(resolution,[status(thm)],[c_16,c_9194])).

tff(c_9200,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_9197])).

tff(c_9202,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1390,c_9200])).

tff(c_9203,plain,(
    k1_funct_1(k8_funct_2('#skF_8','#skF_9','#skF_7','#skF_10','#skF_11'),'#skF_12') != k1_funct_1('#skF_11',k1_funct_1('#skF_10','#skF_12')) ),
    inference(splitRight,[status(thm)],[c_9185])).

tff(c_9394,plain,(
    ~ m1_subset_1('#skF_12','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_3315,c_9203])).

tff(c_9398,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_9394])).

tff(c_9399,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1388])).

tff(c_9409,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9399,c_101])).

tff(c_9414,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_9409])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:41:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.84/3.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.84/3.19  
% 8.84/3.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.84/3.19  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_2 > #skF_5 > #skF_12 > #skF_4
% 8.84/3.19  
% 8.84/3.19  %Foreground sorts:
% 8.84/3.19  
% 8.84/3.19  
% 8.84/3.19  %Background operators:
% 8.84/3.19  
% 8.84/3.19  
% 8.84/3.19  %Foreground operators:
% 8.84/3.19  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.84/3.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.84/3.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.84/3.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.84/3.19  tff('#skF_11', type, '#skF_11': $i).
% 8.84/3.19  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 8.84/3.19  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.84/3.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.84/3.19  tff('#skF_7', type, '#skF_7': $i).
% 8.84/3.19  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.84/3.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.84/3.19  tff('#skF_10', type, '#skF_10': $i).
% 8.84/3.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.84/3.19  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 8.84/3.19  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.84/3.19  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 8.84/3.19  tff('#skF_9', type, '#skF_9': $i).
% 8.84/3.19  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.84/3.19  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.84/3.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.84/3.19  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.84/3.19  tff('#skF_8', type, '#skF_8': $i).
% 8.84/3.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.84/3.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.84/3.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.84/3.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.84/3.19  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.84/3.19  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.84/3.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.84/3.19  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 8.84/3.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.84/3.19  tff('#skF_12', type, '#skF_12': $i).
% 8.84/3.19  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.84/3.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.84/3.19  
% 8.84/3.22  tff(f_166, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t186_funct_2)).
% 8.84/3.22  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.84/3.22  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.84/3.22  tff(f_141, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 8.84/3.22  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 8.84/3.22  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.84/3.22  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.84/3.22  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 8.84/3.22  tff(f_44, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.84/3.22  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 8.84/3.22  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.84/3.22  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 8.84/3.22  tff(f_70, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 8.84/3.22  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.84/3.22  tff(f_117, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 8.84/3.22  tff(c_82, plain, (~v1_xboole_0('#skF_9')), inference(cnfTransformation, [status(thm)], [f_166])).
% 8.84/3.22  tff(c_70, plain, (m1_subset_1('#skF_12', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_166])).
% 8.84/3.22  tff(c_66, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_166])).
% 8.84/3.22  tff(c_80, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_166])).
% 8.84/3.22  tff(c_78, plain, (v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_166])).
% 8.84/3.22  tff(c_76, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(cnfTransformation, [status(thm)], [f_166])).
% 8.84/3.22  tff(c_378, plain, (![A_164, B_165, C_166]: (k2_relset_1(A_164, B_165, C_166)=k2_relat_1(C_166) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(A_164, B_165))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.84/3.22  tff(c_386, plain, (k2_relset_1('#skF_8', '#skF_9', '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_76, c_378])).
% 8.84/3.22  tff(c_72, plain, (m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_166])).
% 8.84/3.22  tff(c_211, plain, (![A_137, B_138, C_139]: (k1_relset_1(A_137, B_138, C_139)=k1_relat_1(C_139) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.84/3.22  tff(c_218, plain, (k1_relset_1('#skF_9', '#skF_7', '#skF_11')=k1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_72, c_211])).
% 8.84/3.22  tff(c_68, plain, (r1_tarski(k2_relset_1('#skF_8', '#skF_9', '#skF_10'), k1_relset_1('#skF_9', '#skF_7', '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_166])).
% 8.84/3.22  tff(c_220, plain, (r1_tarski(k2_relset_1('#skF_8', '#skF_9', '#skF_10'), k1_relat_1('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_218, c_68])).
% 8.84/3.22  tff(c_392, plain, (r1_tarski(k2_relat_1('#skF_10'), k1_relat_1('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_386, c_220])).
% 8.84/3.22  tff(c_74, plain, (v1_funct_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_166])).
% 8.84/3.22  tff(c_3067, plain, (![B_393, C_397, F_392, A_395, D_394, E_396]: (k1_funct_1(k8_funct_2(B_393, C_397, A_395, D_394, E_396), F_392)=k1_funct_1(E_396, k1_funct_1(D_394, F_392)) | k1_xboole_0=B_393 | ~r1_tarski(k2_relset_1(B_393, C_397, D_394), k1_relset_1(C_397, A_395, E_396)) | ~m1_subset_1(F_392, B_393) | ~m1_subset_1(E_396, k1_zfmisc_1(k2_zfmisc_1(C_397, A_395))) | ~v1_funct_1(E_396) | ~m1_subset_1(D_394, k1_zfmisc_1(k2_zfmisc_1(B_393, C_397))) | ~v1_funct_2(D_394, B_393, C_397) | ~v1_funct_1(D_394) | v1_xboole_0(C_397))), inference(cnfTransformation, [status(thm)], [f_141])).
% 8.84/3.22  tff(c_3075, plain, (![B_393, D_394, F_392]: (k1_funct_1(k8_funct_2(B_393, '#skF_9', '#skF_7', D_394, '#skF_11'), F_392)=k1_funct_1('#skF_11', k1_funct_1(D_394, F_392)) | k1_xboole_0=B_393 | ~r1_tarski(k2_relset_1(B_393, '#skF_9', D_394), k1_relat_1('#skF_11')) | ~m1_subset_1(F_392, B_393) | ~m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_7'))) | ~v1_funct_1('#skF_11') | ~m1_subset_1(D_394, k1_zfmisc_1(k2_zfmisc_1(B_393, '#skF_9'))) | ~v1_funct_2(D_394, B_393, '#skF_9') | ~v1_funct_1(D_394) | v1_xboole_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_218, c_3067])).
% 8.84/3.22  tff(c_3088, plain, (![B_393, D_394, F_392]: (k1_funct_1(k8_funct_2(B_393, '#skF_9', '#skF_7', D_394, '#skF_11'), F_392)=k1_funct_1('#skF_11', k1_funct_1(D_394, F_392)) | k1_xboole_0=B_393 | ~r1_tarski(k2_relset_1(B_393, '#skF_9', D_394), k1_relat_1('#skF_11')) | ~m1_subset_1(F_392, B_393) | ~m1_subset_1(D_394, k1_zfmisc_1(k2_zfmisc_1(B_393, '#skF_9'))) | ~v1_funct_2(D_394, B_393, '#skF_9') | ~v1_funct_1(D_394) | v1_xboole_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_3075])).
% 8.84/3.22  tff(c_3307, plain, (![B_411, D_412, F_413]: (k1_funct_1(k8_funct_2(B_411, '#skF_9', '#skF_7', D_412, '#skF_11'), F_413)=k1_funct_1('#skF_11', k1_funct_1(D_412, F_413)) | k1_xboole_0=B_411 | ~r1_tarski(k2_relset_1(B_411, '#skF_9', D_412), k1_relat_1('#skF_11')) | ~m1_subset_1(F_413, B_411) | ~m1_subset_1(D_412, k1_zfmisc_1(k2_zfmisc_1(B_411, '#skF_9'))) | ~v1_funct_2(D_412, B_411, '#skF_9') | ~v1_funct_1(D_412))), inference(negUnitSimplification, [status(thm)], [c_82, c_3088])).
% 8.84/3.22  tff(c_3309, plain, (![F_413]: (k1_funct_1(k8_funct_2('#skF_8', '#skF_9', '#skF_7', '#skF_10', '#skF_11'), F_413)=k1_funct_1('#skF_11', k1_funct_1('#skF_10', F_413)) | k1_xboole_0='#skF_8' | ~r1_tarski(k2_relat_1('#skF_10'), k1_relat_1('#skF_11')) | ~m1_subset_1(F_413, '#skF_8') | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9'))) | ~v1_funct_2('#skF_10', '#skF_8', '#skF_9') | ~v1_funct_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_386, c_3307])).
% 8.84/3.22  tff(c_3314, plain, (![F_413]: (k1_funct_1(k8_funct_2('#skF_8', '#skF_9', '#skF_7', '#skF_10', '#skF_11'), F_413)=k1_funct_1('#skF_11', k1_funct_1('#skF_10', F_413)) | k1_xboole_0='#skF_8' | ~m1_subset_1(F_413, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_392, c_3309])).
% 8.84/3.22  tff(c_3315, plain, (![F_413]: (k1_funct_1(k8_funct_2('#skF_8', '#skF_9', '#skF_7', '#skF_10', '#skF_11'), F_413)=k1_funct_1('#skF_11', k1_funct_1('#skF_10', F_413)) | ~m1_subset_1(F_413, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_66, c_3314])).
% 8.84/3.22  tff(c_219, plain, (k1_relset_1('#skF_8', '#skF_9', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_76, c_211])).
% 8.84/3.22  tff(c_1377, plain, (![B_266, A_267, C_268]: (k1_xboole_0=B_266 | k1_relset_1(A_267, B_266, C_268)=A_267 | ~v1_funct_2(C_268, A_267, B_266) | ~m1_subset_1(C_268, k1_zfmisc_1(k2_zfmisc_1(A_267, B_266))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.84/3.22  tff(c_1383, plain, (k1_xboole_0='#skF_9' | k1_relset_1('#skF_8', '#skF_9', '#skF_10')='#skF_8' | ~v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_76, c_1377])).
% 8.84/3.22  tff(c_1388, plain, (k1_xboole_0='#skF_9' | k1_relat_1('#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_219, c_1383])).
% 8.84/3.22  tff(c_1389, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(splitLeft, [status(thm)], [c_1388])).
% 8.84/3.22  tff(c_108, plain, (![C_113, A_114, B_115]: (v1_relat_1(C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.84/3.22  tff(c_116, plain, (v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_76, c_108])).
% 8.84/3.22  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.84/3.22  tff(c_1300, plain, (![A_261, C_262]: (r2_hidden('#skF_6'(A_261, k2_relat_1(A_261), C_262), k1_relat_1(A_261)) | ~r2_hidden(C_262, k2_relat_1(A_261)) | ~v1_funct_1(A_261) | ~v1_relat_1(A_261))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.84/3.22  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.84/3.22  tff(c_1316, plain, (![A_263, C_264]: (~v1_xboole_0(k1_relat_1(A_263)) | ~r2_hidden(C_264, k2_relat_1(A_263)) | ~v1_funct_1(A_263) | ~v1_relat_1(A_263))), inference(resolution, [status(thm)], [c_1300, c_2])).
% 8.84/3.22  tff(c_1356, plain, (![A_265]: (~v1_xboole_0(k1_relat_1(A_265)) | ~v1_funct_1(A_265) | ~v1_relat_1(A_265) | v1_xboole_0(k2_relat_1(A_265)))), inference(resolution, [status(thm)], [c_4, c_1316])).
% 8.84/3.22  tff(c_14, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.84/3.22  tff(c_16, plain, (![A_12, B_13]: (r2_hidden(A_12, B_13) | v1_xboole_0(B_13) | ~m1_subset_1(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.84/3.22  tff(c_201, plain, (![C_134, B_135, A_136]: (r2_hidden(C_134, B_135) | ~r2_hidden(C_134, A_136) | ~r1_tarski(A_136, B_135))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.84/3.22  tff(c_302, plain, (![A_150, B_151, B_152]: (r2_hidden(A_150, B_151) | ~r1_tarski(B_152, B_151) | v1_xboole_0(B_152) | ~m1_subset_1(A_150, B_152))), inference(resolution, [status(thm)], [c_16, c_201])).
% 8.84/3.22  tff(c_311, plain, (![A_150]: (r2_hidden(A_150, k1_relat_1('#skF_11')) | v1_xboole_0(k2_relset_1('#skF_8', '#skF_9', '#skF_10')) | ~m1_subset_1(A_150, k2_relset_1('#skF_8', '#skF_9', '#skF_10')))), inference(resolution, [status(thm)], [c_220, c_302])).
% 8.84/3.22  tff(c_411, plain, (![A_150]: (r2_hidden(A_150, k1_relat_1('#skF_11')) | v1_xboole_0(k2_relat_1('#skF_10')) | ~m1_subset_1(A_150, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_386, c_386, c_311])).
% 8.84/3.22  tff(c_412, plain, (v1_xboole_0(k2_relat_1('#skF_10'))), inference(splitLeft, [status(thm)], [c_411])).
% 8.84/3.22  tff(c_12, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.84/3.22  tff(c_416, plain, (k2_relat_1('#skF_10')=k1_xboole_0), inference(resolution, [status(thm)], [c_412, c_12])).
% 8.84/3.22  tff(c_444, plain, (![A_172, D_173]: (r2_hidden(k1_funct_1(A_172, D_173), k2_relat_1(A_172)) | ~r2_hidden(D_173, k1_relat_1(A_172)) | ~v1_funct_1(A_172) | ~v1_relat_1(A_172))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.84/3.22  tff(c_455, plain, (![D_173]: (r2_hidden(k1_funct_1('#skF_10', D_173), k1_xboole_0) | ~r2_hidden(D_173, k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_416, c_444])).
% 8.84/3.22  tff(c_461, plain, (![D_174]: (r2_hidden(k1_funct_1('#skF_10', D_174), k1_xboole_0) | ~r2_hidden(D_174, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_80, c_455])).
% 8.84/3.22  tff(c_36, plain, (![B_55, A_54]: (~r1_tarski(B_55, A_54) | ~r2_hidden(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.84/3.22  tff(c_466, plain, (![D_174]: (~r1_tarski(k1_xboole_0, k1_funct_1('#skF_10', D_174)) | ~r2_hidden(D_174, k1_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_461, c_36])).
% 8.84/3.22  tff(c_479, plain, (![D_175]: (~r2_hidden(D_175, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_466])).
% 8.84/3.22  tff(c_504, plain, (v1_xboole_0(k1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_4, c_479])).
% 8.84/3.22  tff(c_508, plain, (k1_relat_1('#skF_10')=k1_xboole_0), inference(resolution, [status(thm)], [c_504, c_12])).
% 8.84/3.22  tff(c_511, plain, (k1_relset_1('#skF_8', '#skF_9', '#skF_10')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_508, c_219])).
% 8.84/3.22  tff(c_828, plain, (![B_207, A_208, C_209]: (k1_xboole_0=B_207 | k1_relset_1(A_208, B_207, C_209)=A_208 | ~v1_funct_2(C_209, A_208, B_207) | ~m1_subset_1(C_209, k1_zfmisc_1(k2_zfmisc_1(A_208, B_207))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.84/3.22  tff(c_834, plain, (k1_xboole_0='#skF_9' | k1_relset_1('#skF_8', '#skF_9', '#skF_10')='#skF_8' | ~v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_76, c_828])).
% 8.84/3.22  tff(c_839, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_511, c_834])).
% 8.84/3.22  tff(c_840, plain, (k1_xboole_0='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_66, c_839])).
% 8.84/3.22  tff(c_91, plain, (![B_108, A_109]: (~r1_tarski(B_108, A_109) | ~r2_hidden(A_109, B_108))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.84/3.22  tff(c_96, plain, (![A_110]: (~r1_tarski(A_110, '#skF_1'(A_110)) | v1_xboole_0(A_110))), inference(resolution, [status(thm)], [c_4, c_91])).
% 8.84/3.22  tff(c_101, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_96])).
% 8.84/3.22  tff(c_855, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_840, c_101])).
% 8.84/3.22  tff(c_860, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_855])).
% 8.84/3.22  tff(c_862, plain, (~v1_xboole_0(k2_relat_1('#skF_10'))), inference(splitRight, [status(thm)], [c_411])).
% 8.84/3.22  tff(c_1365, plain, (~v1_xboole_0(k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_1356, c_862])).
% 8.84/3.22  tff(c_1375, plain, (~v1_xboole_0(k1_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_80, c_1365])).
% 8.84/3.22  tff(c_1390, plain, (~v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1389, c_1375])).
% 8.84/3.22  tff(c_164, plain, (![C_125, B_126, A_127]: (v5_relat_1(C_125, B_126) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_127, B_126))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.84/3.22  tff(c_171, plain, (v5_relat_1('#skF_11', '#skF_7')), inference(resolution, [status(thm)], [c_72, c_164])).
% 8.84/3.22  tff(c_115, plain, (v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_72, c_108])).
% 8.84/3.22  tff(c_18, plain, (![A_14, D_53]: (r2_hidden(k1_funct_1(A_14, D_53), k2_relat_1(A_14)) | ~r2_hidden(D_53, k1_relat_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.84/3.22  tff(c_131, plain, (![A_118, B_119]: (r2_hidden('#skF_2'(A_118, B_119), A_118) | r1_tarski(A_118, B_119))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.84/3.22  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.84/3.22  tff(c_142, plain, (![A_118]: (r1_tarski(A_118, A_118))), inference(resolution, [status(thm)], [c_131, c_8])).
% 8.84/3.22  tff(c_22, plain, (![A_14, C_50]: (r2_hidden('#skF_6'(A_14, k2_relat_1(A_14), C_50), k1_relat_1(A_14)) | ~r2_hidden(C_50, k2_relat_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.84/3.22  tff(c_1395, plain, (![C_50]: (r2_hidden('#skF_6'('#skF_10', k2_relat_1('#skF_10'), C_50), '#skF_8') | ~r2_hidden(C_50, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_1389, c_22])).
% 8.84/3.22  tff(c_1504, plain, (![C_272]: (r2_hidden('#skF_6'('#skF_10', k2_relat_1('#skF_10'), C_272), '#skF_8') | ~r2_hidden(C_272, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_80, c_1395])).
% 8.84/3.22  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.84/3.22  tff(c_1513, plain, (![C_272, B_6]: (r2_hidden('#skF_6'('#skF_10', k2_relat_1('#skF_10'), C_272), B_6) | ~r1_tarski('#skF_8', B_6) | ~r2_hidden(C_272, k2_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_1504, c_6])).
% 8.84/3.22  tff(c_20, plain, (![A_14, C_50]: (k1_funct_1(A_14, '#skF_6'(A_14, k2_relat_1(A_14), C_50))=C_50 | ~r2_hidden(C_50, k2_relat_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.84/3.22  tff(c_934, plain, (![A_222, D_223]: (r2_hidden(k1_funct_1(A_222, D_223), k2_relat_1(A_222)) | ~r2_hidden(D_223, k1_relat_1(A_222)) | ~v1_funct_1(A_222) | ~v1_relat_1(A_222))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.84/3.22  tff(c_2059, plain, (![A_317, D_318, B_319]: (r2_hidden(k1_funct_1(A_317, D_318), B_319) | ~r1_tarski(k2_relat_1(A_317), B_319) | ~r2_hidden(D_318, k1_relat_1(A_317)) | ~v1_funct_1(A_317) | ~v1_relat_1(A_317))), inference(resolution, [status(thm)], [c_934, c_6])).
% 8.84/3.22  tff(c_6825, plain, (![A_686, D_687, B_688, B_689]: (r2_hidden(k1_funct_1(A_686, D_687), B_688) | ~r1_tarski(B_689, B_688) | ~r1_tarski(k2_relat_1(A_686), B_689) | ~r2_hidden(D_687, k1_relat_1(A_686)) | ~v1_funct_1(A_686) | ~v1_relat_1(A_686))), inference(resolution, [status(thm)], [c_2059, c_6])).
% 8.84/3.22  tff(c_6847, plain, (![A_690, D_691]: (r2_hidden(k1_funct_1(A_690, D_691), k1_relat_1('#skF_11')) | ~r1_tarski(k2_relat_1(A_690), k2_relat_1('#skF_10')) | ~r2_hidden(D_691, k1_relat_1(A_690)) | ~v1_funct_1(A_690) | ~v1_relat_1(A_690))), inference(resolution, [status(thm)], [c_392, c_6825])).
% 8.84/3.22  tff(c_7750, plain, (![C_725, A_726]: (r2_hidden(C_725, k1_relat_1('#skF_11')) | ~r1_tarski(k2_relat_1(A_726), k2_relat_1('#skF_10')) | ~r2_hidden('#skF_6'(A_726, k2_relat_1(A_726), C_725), k1_relat_1(A_726)) | ~v1_funct_1(A_726) | ~v1_relat_1(A_726) | ~r2_hidden(C_725, k2_relat_1(A_726)) | ~v1_funct_1(A_726) | ~v1_relat_1(A_726))), inference(superposition, [status(thm), theory('equality')], [c_20, c_6847])).
% 8.84/3.22  tff(c_7758, plain, (![C_272]: (r2_hidden(C_272, k1_relat_1('#skF_11')) | ~r1_tarski(k2_relat_1('#skF_10'), k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r1_tarski('#skF_8', k1_relat_1('#skF_10')) | ~r2_hidden(C_272, k2_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_1513, c_7750])).
% 8.84/3.22  tff(c_7785, plain, (![C_727]: (r2_hidden(C_727, k1_relat_1('#skF_11')) | ~r2_hidden(C_727, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_1389, c_116, c_80, c_142, c_7758])).
% 8.84/3.22  tff(c_7931, plain, (![D_53]: (r2_hidden(k1_funct_1('#skF_10', D_53), k1_relat_1('#skF_11')) | ~r2_hidden(D_53, k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_18, c_7785])).
% 8.84/3.22  tff(c_8039, plain, (![D_728]: (r2_hidden(k1_funct_1('#skF_10', D_728), k1_relat_1('#skF_11')) | ~r2_hidden(D_728, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_80, c_1389, c_7931])).
% 8.84/3.22  tff(c_60, plain, (![A_71, B_72, C_74]: (k7_partfun1(A_71, B_72, C_74)=k1_funct_1(B_72, C_74) | ~r2_hidden(C_74, k1_relat_1(B_72)) | ~v1_funct_1(B_72) | ~v5_relat_1(B_72, A_71) | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.84/3.22  tff(c_8047, plain, (![A_71, D_728]: (k7_partfun1(A_71, '#skF_11', k1_funct_1('#skF_10', D_728))=k1_funct_1('#skF_11', k1_funct_1('#skF_10', D_728)) | ~v1_funct_1('#skF_11') | ~v5_relat_1('#skF_11', A_71) | ~v1_relat_1('#skF_11') | ~r2_hidden(D_728, '#skF_8'))), inference(resolution, [status(thm)], [c_8039, c_60])).
% 8.84/3.22  tff(c_9155, plain, (![A_764, D_765]: (k7_partfun1(A_764, '#skF_11', k1_funct_1('#skF_10', D_765))=k1_funct_1('#skF_11', k1_funct_1('#skF_10', D_765)) | ~v5_relat_1('#skF_11', A_764) | ~r2_hidden(D_765, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_74, c_8047])).
% 8.84/3.22  tff(c_64, plain, (k7_partfun1('#skF_7', '#skF_11', k1_funct_1('#skF_10', '#skF_12'))!=k1_funct_1(k8_funct_2('#skF_8', '#skF_9', '#skF_7', '#skF_10', '#skF_11'), '#skF_12')), inference(cnfTransformation, [status(thm)], [f_166])).
% 8.84/3.22  tff(c_9161, plain, (k1_funct_1(k8_funct_2('#skF_8', '#skF_9', '#skF_7', '#skF_10', '#skF_11'), '#skF_12')!=k1_funct_1('#skF_11', k1_funct_1('#skF_10', '#skF_12')) | ~v5_relat_1('#skF_11', '#skF_7') | ~r2_hidden('#skF_12', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_9155, c_64])).
% 8.84/3.22  tff(c_9185, plain, (k1_funct_1(k8_funct_2('#skF_8', '#skF_9', '#skF_7', '#skF_10', '#skF_11'), '#skF_12')!=k1_funct_1('#skF_11', k1_funct_1('#skF_10', '#skF_12')) | ~r2_hidden('#skF_12', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_171, c_9161])).
% 8.84/3.22  tff(c_9194, plain, (~r2_hidden('#skF_12', '#skF_8')), inference(splitLeft, [status(thm)], [c_9185])).
% 8.84/3.22  tff(c_9197, plain, (v1_xboole_0('#skF_8') | ~m1_subset_1('#skF_12', '#skF_8')), inference(resolution, [status(thm)], [c_16, c_9194])).
% 8.84/3.22  tff(c_9200, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_9197])).
% 8.84/3.22  tff(c_9202, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1390, c_9200])).
% 8.84/3.22  tff(c_9203, plain, (k1_funct_1(k8_funct_2('#skF_8', '#skF_9', '#skF_7', '#skF_10', '#skF_11'), '#skF_12')!=k1_funct_1('#skF_11', k1_funct_1('#skF_10', '#skF_12'))), inference(splitRight, [status(thm)], [c_9185])).
% 8.84/3.22  tff(c_9394, plain, (~m1_subset_1('#skF_12', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_3315, c_9203])).
% 8.84/3.22  tff(c_9398, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_9394])).
% 8.84/3.22  tff(c_9399, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_1388])).
% 8.84/3.22  tff(c_9409, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_9399, c_101])).
% 8.84/3.22  tff(c_9414, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_9409])).
% 8.84/3.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.84/3.22  
% 8.84/3.22  Inference rules
% 8.84/3.22  ----------------------
% 8.84/3.22  #Ref     : 2
% 8.84/3.22  #Sup     : 2028
% 8.84/3.22  #Fact    : 0
% 8.84/3.22  #Define  : 0
% 8.84/3.22  #Split   : 27
% 8.84/3.22  #Chain   : 0
% 8.84/3.22  #Close   : 0
% 8.84/3.22  
% 8.84/3.22  Ordering : KBO
% 8.84/3.22  
% 8.84/3.22  Simplification rules
% 8.84/3.22  ----------------------
% 8.84/3.22  #Subsume      : 1069
% 8.84/3.22  #Demod        : 861
% 8.84/3.22  #Tautology    : 173
% 8.84/3.22  #SimpNegUnit  : 83
% 8.84/3.22  #BackRed      : 71
% 8.84/3.22  
% 8.84/3.22  #Partial instantiations: 0
% 8.84/3.22  #Strategies tried      : 1
% 8.84/3.22  
% 8.84/3.22  Timing (in seconds)
% 8.84/3.22  ----------------------
% 9.20/3.22  Preprocessing        : 0.39
% 9.20/3.22  Parsing              : 0.20
% 9.20/3.22  CNF conversion       : 0.04
% 9.20/3.22  Main loop            : 2.04
% 9.20/3.22  Inferencing          : 0.60
% 9.20/3.22  Reduction            : 0.58
% 9.20/3.22  Demodulation         : 0.38
% 9.20/3.22  BG Simplification    : 0.06
% 9.20/3.22  Subsumption          : 0.65
% 9.20/3.22  Abstraction          : 0.08
% 9.20/3.22  MUC search           : 0.00
% 9.20/3.22  Cooper               : 0.00
% 9.20/3.22  Total                : 2.48
% 9.20/3.22  Index Insertion      : 0.00
% 9.20/3.22  Index Deletion       : 0.00
% 9.20/3.22  Index Matching       : 0.00
% 9.20/3.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
