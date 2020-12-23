%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:49 EST 2020

% Result     : Theorem 6.43s
% Output     : CNFRefutation 6.77s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 545 expanded)
%              Number of leaves         :   48 ( 213 expanded)
%              Depth                    :   23
%              Number of atoms          :  323 (1853 expanded)
%              Number of equality atoms :   61 ( 417 expanded)
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

tff(f_162,negated_conjecture,(
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

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_137,axiom,(
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

tff(f_102,axiom,(
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

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_66,axiom,(
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

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(c_84,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_72,plain,(
    m1_subset_1('#skF_12','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_76,plain,(
    v1_funct_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_74,plain,(
    m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_276,plain,(
    ! [A_150,B_151,C_152] :
      ( k1_relset_1(A_150,B_151,C_152) = k1_relat_1(C_152)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_284,plain,(
    k1_relset_1('#skF_9','#skF_7','#skF_11') = k1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_74,c_276])).

tff(c_78,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_212,plain,(
    ! [A_138,B_139,C_140] :
      ( k2_relset_1(A_138,B_139,C_140) = k2_relat_1(C_140)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_219,plain,(
    k2_relset_1('#skF_8','#skF_9','#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_78,c_212])).

tff(c_70,plain,(
    r1_tarski(k2_relset_1('#skF_8','#skF_9','#skF_10'),k1_relset_1('#skF_9','#skF_7','#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_221,plain,(
    r1_tarski(k2_relat_1('#skF_10'),k1_relset_1('#skF_9','#skF_7','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_70])).

tff(c_290,plain,(
    r1_tarski(k2_relat_1('#skF_10'),k1_relat_1('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_221])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_82,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_80,plain,(
    v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_2892,plain,(
    ! [C_421,A_426,E_425,B_424,D_423,F_422] :
      ( k1_funct_1(k8_funct_2(B_424,C_421,A_426,D_423,E_425),F_422) = k1_funct_1(E_425,k1_funct_1(D_423,F_422))
      | k1_xboole_0 = B_424
      | ~ r1_tarski(k2_relset_1(B_424,C_421,D_423),k1_relset_1(C_421,A_426,E_425))
      | ~ m1_subset_1(F_422,B_424)
      | ~ m1_subset_1(E_425,k1_zfmisc_1(k2_zfmisc_1(C_421,A_426)))
      | ~ v1_funct_1(E_425)
      | ~ m1_subset_1(D_423,k1_zfmisc_1(k2_zfmisc_1(B_424,C_421)))
      | ~ v1_funct_2(D_423,B_424,C_421)
      | ~ v1_funct_1(D_423)
      | v1_xboole_0(C_421) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_2900,plain,(
    ! [A_426,E_425,F_422] :
      ( k1_funct_1(k8_funct_2('#skF_8','#skF_9',A_426,'#skF_10',E_425),F_422) = k1_funct_1(E_425,k1_funct_1('#skF_10',F_422))
      | k1_xboole_0 = '#skF_8'
      | ~ r1_tarski(k2_relat_1('#skF_10'),k1_relset_1('#skF_9',A_426,E_425))
      | ~ m1_subset_1(F_422,'#skF_8')
      | ~ m1_subset_1(E_425,k1_zfmisc_1(k2_zfmisc_1('#skF_9',A_426)))
      | ~ v1_funct_1(E_425)
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9')))
      | ~ v1_funct_2('#skF_10','#skF_8','#skF_9')
      | ~ v1_funct_1('#skF_10')
      | v1_xboole_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_2892])).

tff(c_2913,plain,(
    ! [A_426,E_425,F_422] :
      ( k1_funct_1(k8_funct_2('#skF_8','#skF_9',A_426,'#skF_10',E_425),F_422) = k1_funct_1(E_425,k1_funct_1('#skF_10',F_422))
      | k1_xboole_0 = '#skF_8'
      | ~ r1_tarski(k2_relat_1('#skF_10'),k1_relset_1('#skF_9',A_426,E_425))
      | ~ m1_subset_1(F_422,'#skF_8')
      | ~ m1_subset_1(E_425,k1_zfmisc_1(k2_zfmisc_1('#skF_9',A_426)))
      | ~ v1_funct_1(E_425)
      | v1_xboole_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_2900])).

tff(c_2916,plain,(
    ! [A_427,E_428,F_429] :
      ( k1_funct_1(k8_funct_2('#skF_8','#skF_9',A_427,'#skF_10',E_428),F_429) = k1_funct_1(E_428,k1_funct_1('#skF_10',F_429))
      | ~ r1_tarski(k2_relat_1('#skF_10'),k1_relset_1('#skF_9',A_427,E_428))
      | ~ m1_subset_1(F_429,'#skF_8')
      | ~ m1_subset_1(E_428,k1_zfmisc_1(k2_zfmisc_1('#skF_9',A_427)))
      | ~ v1_funct_1(E_428) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_68,c_2913])).

tff(c_2921,plain,(
    ! [F_429] :
      ( k1_funct_1(k8_funct_2('#skF_8','#skF_9','#skF_7','#skF_10','#skF_11'),F_429) = k1_funct_1('#skF_11',k1_funct_1('#skF_10',F_429))
      | ~ r1_tarski(k2_relat_1('#skF_10'),k1_relat_1('#skF_11'))
      | ~ m1_subset_1(F_429,'#skF_8')
      | ~ m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_7')))
      | ~ v1_funct_1('#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_2916])).

tff(c_2929,plain,(
    ! [F_429] :
      ( k1_funct_1(k8_funct_2('#skF_8','#skF_9','#skF_7','#skF_10','#skF_11'),F_429) = k1_funct_1('#skF_11',k1_funct_1('#skF_10',F_429))
      | ~ m1_subset_1(F_429,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_290,c_2921])).

tff(c_283,plain,(
    k1_relset_1('#skF_8','#skF_9','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_78,c_276])).

tff(c_1578,plain,(
    ! [B_284,A_285,C_286] :
      ( k1_xboole_0 = B_284
      | k1_relset_1(A_285,B_284,C_286) = A_285
      | ~ v1_funct_2(C_286,A_285,B_284)
      | ~ m1_subset_1(C_286,k1_zfmisc_1(k2_zfmisc_1(A_285,B_284))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1581,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relset_1('#skF_8','#skF_9','#skF_10') = '#skF_8'
    | ~ v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_78,c_1578])).

tff(c_1587,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relat_1('#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_283,c_1581])).

tff(c_1591,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1587])).

tff(c_99,plain,(
    ! [C_109,A_110,B_111] :
      ( v1_relat_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_106,plain,(
    v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_78,c_99])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1389,plain,(
    ! [A_268,C_269] :
      ( r2_hidden('#skF_6'(A_268,k2_relat_1(A_268),C_269),k1_relat_1(A_268))
      | ~ r2_hidden(C_269,k2_relat_1(A_268))
      | ~ v1_funct_1(A_268)
      | ~ v1_relat_1(A_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1401,plain,(
    ! [A_270,C_271] :
      ( ~ v1_xboole_0(k1_relat_1(A_270))
      | ~ r2_hidden(C_271,k2_relat_1(A_270))
      | ~ v1_funct_1(A_270)
      | ~ v1_relat_1(A_270) ) ),
    inference(resolution,[status(thm)],[c_1389,c_2])).

tff(c_1441,plain,(
    ! [A_272] :
      ( ~ v1_xboole_0(k1_relat_1(A_272))
      | ~ v1_funct_1(A_272)
      | ~ v1_relat_1(A_272)
      | v1_xboole_0(k2_relat_1(A_272)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1401])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( r2_hidden(A_12,B_13)
      | v1_xboole_0(B_13)
      | ~ m1_subset_1(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_162,plain,(
    ! [C_123,B_124,A_125] :
      ( r2_hidden(C_123,B_124)
      | ~ r2_hidden(C_123,A_125)
      | ~ r1_tarski(A_125,B_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_169,plain,(
    ! [A_12,B_124,B_13] :
      ( r2_hidden(A_12,B_124)
      | ~ r1_tarski(B_13,B_124)
      | v1_xboole_0(B_13)
      | ~ m1_subset_1(A_12,B_13) ) ),
    inference(resolution,[status(thm)],[c_20,c_162])).

tff(c_309,plain,(
    ! [A_12] :
      ( r2_hidden(A_12,k1_relat_1('#skF_11'))
      | v1_xboole_0(k2_relat_1('#skF_10'))
      | ~ m1_subset_1(A_12,k2_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_290,c_169])).

tff(c_318,plain,(
    v1_xboole_0(k2_relat_1('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_309])).

tff(c_93,plain,(
    ! [A_105,B_106] :
      ( r2_hidden('#skF_2'(A_105,B_106),A_105)
      | r1_tarski(A_105,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_97,plain,(
    ! [A_105,B_106] :
      ( ~ v1_xboole_0(A_105)
      | r1_tarski(A_105,B_106) ) ),
    inference(resolution,[status(thm)],[c_93,c_2])).

tff(c_125,plain,(
    ! [B_116,A_117] :
      ( B_116 = A_117
      | ~ r1_tarski(B_116,A_117)
      | ~ r1_tarski(A_117,B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_138,plain,(
    ! [B_118,A_119] :
      ( B_118 = A_119
      | ~ r1_tarski(B_118,A_119)
      | ~ v1_xboole_0(A_119) ) ),
    inference(resolution,[status(thm)],[c_97,c_125])).

tff(c_152,plain,(
    ! [B_120,A_121] :
      ( B_120 = A_121
      | ~ v1_xboole_0(B_120)
      | ~ v1_xboole_0(A_121) ) ),
    inference(resolution,[status(thm)],[c_97,c_138])).

tff(c_155,plain,(
    ! [A_121] :
      ( k1_xboole_0 = A_121
      | ~ v1_xboole_0(A_121) ) ),
    inference(resolution,[status(thm)],[c_12,c_152])).

tff(c_324,plain,(
    k2_relat_1('#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_318,c_155])).

tff(c_368,plain,(
    ! [A_154,D_155] :
      ( r2_hidden(k1_funct_1(A_154,D_155),k2_relat_1(A_154))
      | ~ r2_hidden(D_155,k1_relat_1(A_154))
      | ~ v1_funct_1(A_154)
      | ~ v1_relat_1(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_376,plain,(
    ! [D_155] :
      ( r2_hidden(k1_funct_1('#skF_10',D_155),k1_xboole_0)
      | ~ r2_hidden(D_155,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_368])).

tff(c_381,plain,(
    ! [D_156] :
      ( r2_hidden(k1_funct_1('#skF_10',D_156),k1_xboole_0)
      | ~ r2_hidden(D_156,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_82,c_376])).

tff(c_386,plain,(
    ! [D_156] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(D_156,k1_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_381,c_2])).

tff(c_391,plain,(
    ! [D_157] : ~ r2_hidden(D_157,k1_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_386])).

tff(c_416,plain,(
    v1_xboole_0(k1_relat_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_4,c_391])).

tff(c_422,plain,(
    k1_relat_1('#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_416,c_155])).

tff(c_427,plain,(
    k1_relset_1('#skF_8','#skF_9','#skF_10') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_283])).

tff(c_1013,plain,(
    ! [B_213,A_214,C_215] :
      ( k1_xboole_0 = B_213
      | k1_relset_1(A_214,B_213,C_215) = A_214
      | ~ v1_funct_2(C_215,A_214,B_213)
      | ~ m1_subset_1(C_215,k1_zfmisc_1(k2_zfmisc_1(A_214,B_213))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1016,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relset_1('#skF_8','#skF_9','#skF_10') = '#skF_8'
    | ~ v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_78,c_1013])).

tff(c_1022,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_427,c_1016])).

tff(c_1023,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1022])).

tff(c_1044,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1023,c_12])).

tff(c_1047,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_1044])).

tff(c_1049,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_309])).

tff(c_1455,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_1441,c_1049])).

tff(c_1469,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_82,c_1455])).

tff(c_1592,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1591,c_1469])).

tff(c_172,plain,(
    ! [C_126,B_127,A_128] :
      ( v5_relat_1(C_126,B_127)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_128,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_180,plain,(
    v5_relat_1('#skF_11','#skF_7') ),
    inference(resolution,[status(thm)],[c_74,c_172])).

tff(c_107,plain,(
    v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_74,c_99])).

tff(c_22,plain,(
    ! [A_14,D_53] :
      ( r2_hidden(k1_funct_1(A_14,D_53),k2_relat_1(A_14))
      | ~ r2_hidden(D_53,k1_relat_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_18,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1399,plain,(
    ! [A_268,C_269,B_6] :
      ( r2_hidden('#skF_6'(A_268,k2_relat_1(A_268),C_269),B_6)
      | ~ r1_tarski(k1_relat_1(A_268),B_6)
      | ~ r2_hidden(C_269,k2_relat_1(A_268))
      | ~ v1_funct_1(A_268)
      | ~ v1_relat_1(A_268) ) ),
    inference(resolution,[status(thm)],[c_1389,c_6])).

tff(c_24,plain,(
    ! [A_14,C_50] :
      ( k1_funct_1(A_14,'#skF_6'(A_14,k2_relat_1(A_14),C_50)) = C_50
      | ~ r2_hidden(C_50,k2_relat_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1097,plain,(
    ! [A_225,D_226] :
      ( r2_hidden(k1_funct_1(A_225,D_226),k2_relat_1(A_225))
      | ~ r2_hidden(D_226,k1_relat_1(A_225))
      | ~ v1_funct_1(A_225)
      | ~ v1_relat_1(A_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1961,plain,(
    ! [A_310,D_311,B_312] :
      ( r2_hidden(k1_funct_1(A_310,D_311),B_312)
      | ~ r1_tarski(k2_relat_1(A_310),B_312)
      | ~ r2_hidden(D_311,k1_relat_1(A_310))
      | ~ v1_funct_1(A_310)
      | ~ v1_relat_1(A_310) ) ),
    inference(resolution,[status(thm)],[c_1097,c_6])).

tff(c_2974,plain,(
    ! [A_431,D_432,B_433,B_434] :
      ( r2_hidden(k1_funct_1(A_431,D_432),B_433)
      | ~ r1_tarski(B_434,B_433)
      | ~ r1_tarski(k2_relat_1(A_431),B_434)
      | ~ r2_hidden(D_432,k1_relat_1(A_431))
      | ~ v1_funct_1(A_431)
      | ~ v1_relat_1(A_431) ) ),
    inference(resolution,[status(thm)],[c_1961,c_6])).

tff(c_2990,plain,(
    ! [A_435,D_436] :
      ( r2_hidden(k1_funct_1(A_435,D_436),k1_relat_1('#skF_11'))
      | ~ r1_tarski(k2_relat_1(A_435),k2_relat_1('#skF_10'))
      | ~ r2_hidden(D_436,k1_relat_1(A_435))
      | ~ v1_funct_1(A_435)
      | ~ v1_relat_1(A_435) ) ),
    inference(resolution,[status(thm)],[c_290,c_2974])).

tff(c_3757,plain,(
    ! [A_541,D_542,B_543] :
      ( r2_hidden(k1_funct_1(A_541,D_542),B_543)
      | ~ r1_tarski(k1_relat_1('#skF_11'),B_543)
      | ~ r1_tarski(k2_relat_1(A_541),k2_relat_1('#skF_10'))
      | ~ r2_hidden(D_542,k1_relat_1(A_541))
      | ~ v1_funct_1(A_541)
      | ~ v1_relat_1(A_541) ) ),
    inference(resolution,[status(thm)],[c_2990,c_6])).

tff(c_3766,plain,(
    ! [D_542,B_543] :
      ( r2_hidden(k1_funct_1('#skF_10',D_542),B_543)
      | ~ r1_tarski(k1_relat_1('#skF_11'),B_543)
      | ~ r2_hidden(D_542,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_18,c_3757])).

tff(c_3772,plain,(
    ! [D_544,B_545] :
      ( r2_hidden(k1_funct_1('#skF_10',D_544),B_545)
      | ~ r1_tarski(k1_relat_1('#skF_11'),B_545)
      | ~ r2_hidden(D_544,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_82,c_1591,c_3766])).

tff(c_3803,plain,(
    ! [C_50,B_545] :
      ( r2_hidden(C_50,B_545)
      | ~ r1_tarski(k1_relat_1('#skF_11'),B_545)
      | ~ r2_hidden('#skF_6'('#skF_10',k2_relat_1('#skF_10'),C_50),'#skF_8')
      | ~ r2_hidden(C_50,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_3772])).

tff(c_3830,plain,(
    ! [C_549,B_550] :
      ( r2_hidden(C_549,B_550)
      | ~ r1_tarski(k1_relat_1('#skF_11'),B_550)
      | ~ r2_hidden('#skF_6'('#skF_10',k2_relat_1('#skF_10'),C_549),'#skF_8')
      | ~ r2_hidden(C_549,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_82,c_3803])).

tff(c_3845,plain,(
    ! [C_551] :
      ( r2_hidden(C_551,k1_relat_1('#skF_11'))
      | ~ r2_hidden('#skF_6'('#skF_10',k2_relat_1('#skF_10'),C_551),'#skF_8')
      | ~ r2_hidden(C_551,k2_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_18,c_3830])).

tff(c_3849,plain,(
    ! [C_269] :
      ( r2_hidden(C_269,k1_relat_1('#skF_11'))
      | ~ r1_tarski(k1_relat_1('#skF_10'),'#skF_8')
      | ~ r2_hidden(C_269,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_1399,c_3845])).

tff(c_3870,plain,(
    ! [C_552] :
      ( r2_hidden(C_552,k1_relat_1('#skF_11'))
      | ~ r2_hidden(C_552,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_82,c_18,c_1591,c_3849])).

tff(c_3970,plain,(
    ! [D_53] :
      ( r2_hidden(k1_funct_1('#skF_10',D_53),k1_relat_1('#skF_11'))
      | ~ r2_hidden(D_53,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_22,c_3870])).

tff(c_4104,plain,(
    ! [D_559] :
      ( r2_hidden(k1_funct_1('#skF_10',D_559),k1_relat_1('#skF_11'))
      | ~ r2_hidden(D_559,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_82,c_1591,c_3970])).

tff(c_62,plain,(
    ! [A_69,B_70,C_72] :
      ( k7_partfun1(A_69,B_70,C_72) = k1_funct_1(B_70,C_72)
      | ~ r2_hidden(C_72,k1_relat_1(B_70))
      | ~ v1_funct_1(B_70)
      | ~ v5_relat_1(B_70,A_69)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_4106,plain,(
    ! [A_69,D_559] :
      ( k7_partfun1(A_69,'#skF_11',k1_funct_1('#skF_10',D_559)) = k1_funct_1('#skF_11',k1_funct_1('#skF_10',D_559))
      | ~ v1_funct_1('#skF_11')
      | ~ v5_relat_1('#skF_11',A_69)
      | ~ v1_relat_1('#skF_11')
      | ~ r2_hidden(D_559,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_4104,c_62])).

tff(c_4502,plain,(
    ! [A_575,D_576] :
      ( k7_partfun1(A_575,'#skF_11',k1_funct_1('#skF_10',D_576)) = k1_funct_1('#skF_11',k1_funct_1('#skF_10',D_576))
      | ~ v5_relat_1('#skF_11',A_575)
      | ~ r2_hidden(D_576,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_76,c_4106])).

tff(c_66,plain,(
    k7_partfun1('#skF_7','#skF_11',k1_funct_1('#skF_10','#skF_12')) != k1_funct_1(k8_funct_2('#skF_8','#skF_9','#skF_7','#skF_10','#skF_11'),'#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_4508,plain,
    ( k1_funct_1(k8_funct_2('#skF_8','#skF_9','#skF_7','#skF_10','#skF_11'),'#skF_12') != k1_funct_1('#skF_11',k1_funct_1('#skF_10','#skF_12'))
    | ~ v5_relat_1('#skF_11','#skF_7')
    | ~ r2_hidden('#skF_12','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_4502,c_66])).

tff(c_4526,plain,
    ( k1_funct_1(k8_funct_2('#skF_8','#skF_9','#skF_7','#skF_10','#skF_11'),'#skF_12') != k1_funct_1('#skF_11',k1_funct_1('#skF_10','#skF_12'))
    | ~ r2_hidden('#skF_12','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_4508])).

tff(c_4532,plain,(
    ~ r2_hidden('#skF_12','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_4526])).

tff(c_4535,plain,
    ( v1_xboole_0('#skF_8')
    | ~ m1_subset_1('#skF_12','#skF_8') ),
    inference(resolution,[status(thm)],[c_20,c_4532])).

tff(c_4538,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4535])).

tff(c_4540,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1592,c_4538])).

tff(c_4541,plain,(
    k1_funct_1(k8_funct_2('#skF_8','#skF_9','#skF_7','#skF_10','#skF_11'),'#skF_12') != k1_funct_1('#skF_11',k1_funct_1('#skF_10','#skF_12')) ),
    inference(splitRight,[status(thm)],[c_4526])).

tff(c_4665,plain,(
    ~ m1_subset_1('#skF_12','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_2929,c_4541])).

tff(c_4669,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4665])).

tff(c_4670,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1587])).

tff(c_4681,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4670,c_12])).

tff(c_4684,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_4681])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:41:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.43/2.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.43/2.30  
% 6.43/2.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.43/2.31  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_2 > #skF_5 > #skF_12 > #skF_4
% 6.43/2.31  
% 6.43/2.31  %Foreground sorts:
% 6.43/2.31  
% 6.43/2.31  
% 6.43/2.31  %Background operators:
% 6.43/2.31  
% 6.43/2.31  
% 6.43/2.31  %Foreground operators:
% 6.43/2.31  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.43/2.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.43/2.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.43/2.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.43/2.31  tff('#skF_11', type, '#skF_11': $i).
% 6.43/2.31  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 6.43/2.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.43/2.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.43/2.31  tff('#skF_7', type, '#skF_7': $i).
% 6.43/2.31  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.43/2.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.43/2.31  tff('#skF_10', type, '#skF_10': $i).
% 6.43/2.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.43/2.31  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 6.43/2.31  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.43/2.31  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 6.43/2.31  tff('#skF_9', type, '#skF_9': $i).
% 6.43/2.31  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.43/2.31  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.43/2.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.43/2.31  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.43/2.31  tff('#skF_8', type, '#skF_8': $i).
% 6.43/2.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.43/2.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.43/2.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.43/2.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.43/2.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.43/2.31  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.43/2.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.43/2.31  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 6.43/2.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.43/2.31  tff('#skF_12', type, '#skF_12': $i).
% 6.43/2.31  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.43/2.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.43/2.31  
% 6.77/2.33  tff(f_162, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 6.77/2.33  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.77/2.33  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.77/2.33  tff(f_137, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 6.77/2.33  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 6.77/2.33  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.77/2.33  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.77/2.33  tff(f_66, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 6.77/2.33  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.77/2.33  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 6.77/2.33  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.77/2.33  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.77/2.33  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.77/2.33  tff(f_113, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 6.77/2.33  tff(c_84, plain, (~v1_xboole_0('#skF_9')), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.77/2.33  tff(c_72, plain, (m1_subset_1('#skF_12', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.77/2.33  tff(c_76, plain, (v1_funct_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.77/2.33  tff(c_74, plain, (m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.77/2.33  tff(c_276, plain, (![A_150, B_151, C_152]: (k1_relset_1(A_150, B_151, C_152)=k1_relat_1(C_152) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.77/2.33  tff(c_284, plain, (k1_relset_1('#skF_9', '#skF_7', '#skF_11')=k1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_74, c_276])).
% 6.77/2.33  tff(c_78, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.77/2.33  tff(c_212, plain, (![A_138, B_139, C_140]: (k2_relset_1(A_138, B_139, C_140)=k2_relat_1(C_140) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.77/2.33  tff(c_219, plain, (k2_relset_1('#skF_8', '#skF_9', '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_78, c_212])).
% 6.77/2.33  tff(c_70, plain, (r1_tarski(k2_relset_1('#skF_8', '#skF_9', '#skF_10'), k1_relset_1('#skF_9', '#skF_7', '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.77/2.33  tff(c_221, plain, (r1_tarski(k2_relat_1('#skF_10'), k1_relset_1('#skF_9', '#skF_7', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_219, c_70])).
% 6.77/2.33  tff(c_290, plain, (r1_tarski(k2_relat_1('#skF_10'), k1_relat_1('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_284, c_221])).
% 6.77/2.33  tff(c_68, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.77/2.33  tff(c_82, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.77/2.33  tff(c_80, plain, (v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.77/2.33  tff(c_2892, plain, (![C_421, A_426, E_425, B_424, D_423, F_422]: (k1_funct_1(k8_funct_2(B_424, C_421, A_426, D_423, E_425), F_422)=k1_funct_1(E_425, k1_funct_1(D_423, F_422)) | k1_xboole_0=B_424 | ~r1_tarski(k2_relset_1(B_424, C_421, D_423), k1_relset_1(C_421, A_426, E_425)) | ~m1_subset_1(F_422, B_424) | ~m1_subset_1(E_425, k1_zfmisc_1(k2_zfmisc_1(C_421, A_426))) | ~v1_funct_1(E_425) | ~m1_subset_1(D_423, k1_zfmisc_1(k2_zfmisc_1(B_424, C_421))) | ~v1_funct_2(D_423, B_424, C_421) | ~v1_funct_1(D_423) | v1_xboole_0(C_421))), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.77/2.33  tff(c_2900, plain, (![A_426, E_425, F_422]: (k1_funct_1(k8_funct_2('#skF_8', '#skF_9', A_426, '#skF_10', E_425), F_422)=k1_funct_1(E_425, k1_funct_1('#skF_10', F_422)) | k1_xboole_0='#skF_8' | ~r1_tarski(k2_relat_1('#skF_10'), k1_relset_1('#skF_9', A_426, E_425)) | ~m1_subset_1(F_422, '#skF_8') | ~m1_subset_1(E_425, k1_zfmisc_1(k2_zfmisc_1('#skF_9', A_426))) | ~v1_funct_1(E_425) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9'))) | ~v1_funct_2('#skF_10', '#skF_8', '#skF_9') | ~v1_funct_1('#skF_10') | v1_xboole_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_219, c_2892])).
% 6.77/2.33  tff(c_2913, plain, (![A_426, E_425, F_422]: (k1_funct_1(k8_funct_2('#skF_8', '#skF_9', A_426, '#skF_10', E_425), F_422)=k1_funct_1(E_425, k1_funct_1('#skF_10', F_422)) | k1_xboole_0='#skF_8' | ~r1_tarski(k2_relat_1('#skF_10'), k1_relset_1('#skF_9', A_426, E_425)) | ~m1_subset_1(F_422, '#skF_8') | ~m1_subset_1(E_425, k1_zfmisc_1(k2_zfmisc_1('#skF_9', A_426))) | ~v1_funct_1(E_425) | v1_xboole_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_2900])).
% 6.77/2.33  tff(c_2916, plain, (![A_427, E_428, F_429]: (k1_funct_1(k8_funct_2('#skF_8', '#skF_9', A_427, '#skF_10', E_428), F_429)=k1_funct_1(E_428, k1_funct_1('#skF_10', F_429)) | ~r1_tarski(k2_relat_1('#skF_10'), k1_relset_1('#skF_9', A_427, E_428)) | ~m1_subset_1(F_429, '#skF_8') | ~m1_subset_1(E_428, k1_zfmisc_1(k2_zfmisc_1('#skF_9', A_427))) | ~v1_funct_1(E_428))), inference(negUnitSimplification, [status(thm)], [c_84, c_68, c_2913])).
% 6.77/2.33  tff(c_2921, plain, (![F_429]: (k1_funct_1(k8_funct_2('#skF_8', '#skF_9', '#skF_7', '#skF_10', '#skF_11'), F_429)=k1_funct_1('#skF_11', k1_funct_1('#skF_10', F_429)) | ~r1_tarski(k2_relat_1('#skF_10'), k1_relat_1('#skF_11')) | ~m1_subset_1(F_429, '#skF_8') | ~m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_7'))) | ~v1_funct_1('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_284, c_2916])).
% 6.77/2.33  tff(c_2929, plain, (![F_429]: (k1_funct_1(k8_funct_2('#skF_8', '#skF_9', '#skF_7', '#skF_10', '#skF_11'), F_429)=k1_funct_1('#skF_11', k1_funct_1('#skF_10', F_429)) | ~m1_subset_1(F_429, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_290, c_2921])).
% 6.77/2.33  tff(c_283, plain, (k1_relset_1('#skF_8', '#skF_9', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_78, c_276])).
% 6.77/2.33  tff(c_1578, plain, (![B_284, A_285, C_286]: (k1_xboole_0=B_284 | k1_relset_1(A_285, B_284, C_286)=A_285 | ~v1_funct_2(C_286, A_285, B_284) | ~m1_subset_1(C_286, k1_zfmisc_1(k2_zfmisc_1(A_285, B_284))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.77/2.33  tff(c_1581, plain, (k1_xboole_0='#skF_9' | k1_relset_1('#skF_8', '#skF_9', '#skF_10')='#skF_8' | ~v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_78, c_1578])).
% 6.77/2.33  tff(c_1587, plain, (k1_xboole_0='#skF_9' | k1_relat_1('#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_283, c_1581])).
% 6.77/2.33  tff(c_1591, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(splitLeft, [status(thm)], [c_1587])).
% 6.77/2.33  tff(c_99, plain, (![C_109, A_110, B_111]: (v1_relat_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.77/2.33  tff(c_106, plain, (v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_78, c_99])).
% 6.77/2.33  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.77/2.33  tff(c_1389, plain, (![A_268, C_269]: (r2_hidden('#skF_6'(A_268, k2_relat_1(A_268), C_269), k1_relat_1(A_268)) | ~r2_hidden(C_269, k2_relat_1(A_268)) | ~v1_funct_1(A_268) | ~v1_relat_1(A_268))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.77/2.33  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.77/2.33  tff(c_1401, plain, (![A_270, C_271]: (~v1_xboole_0(k1_relat_1(A_270)) | ~r2_hidden(C_271, k2_relat_1(A_270)) | ~v1_funct_1(A_270) | ~v1_relat_1(A_270))), inference(resolution, [status(thm)], [c_1389, c_2])).
% 6.77/2.33  tff(c_1441, plain, (![A_272]: (~v1_xboole_0(k1_relat_1(A_272)) | ~v1_funct_1(A_272) | ~v1_relat_1(A_272) | v1_xboole_0(k2_relat_1(A_272)))), inference(resolution, [status(thm)], [c_4, c_1401])).
% 6.77/2.33  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.77/2.33  tff(c_20, plain, (![A_12, B_13]: (r2_hidden(A_12, B_13) | v1_xboole_0(B_13) | ~m1_subset_1(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.77/2.33  tff(c_162, plain, (![C_123, B_124, A_125]: (r2_hidden(C_123, B_124) | ~r2_hidden(C_123, A_125) | ~r1_tarski(A_125, B_124))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.77/2.33  tff(c_169, plain, (![A_12, B_124, B_13]: (r2_hidden(A_12, B_124) | ~r1_tarski(B_13, B_124) | v1_xboole_0(B_13) | ~m1_subset_1(A_12, B_13))), inference(resolution, [status(thm)], [c_20, c_162])).
% 6.77/2.33  tff(c_309, plain, (![A_12]: (r2_hidden(A_12, k1_relat_1('#skF_11')) | v1_xboole_0(k2_relat_1('#skF_10')) | ~m1_subset_1(A_12, k2_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_290, c_169])).
% 6.77/2.33  tff(c_318, plain, (v1_xboole_0(k2_relat_1('#skF_10'))), inference(splitLeft, [status(thm)], [c_309])).
% 6.77/2.33  tff(c_93, plain, (![A_105, B_106]: (r2_hidden('#skF_2'(A_105, B_106), A_105) | r1_tarski(A_105, B_106))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.77/2.33  tff(c_97, plain, (![A_105, B_106]: (~v1_xboole_0(A_105) | r1_tarski(A_105, B_106))), inference(resolution, [status(thm)], [c_93, c_2])).
% 6.77/2.33  tff(c_125, plain, (![B_116, A_117]: (B_116=A_117 | ~r1_tarski(B_116, A_117) | ~r1_tarski(A_117, B_116))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.77/2.33  tff(c_138, plain, (![B_118, A_119]: (B_118=A_119 | ~r1_tarski(B_118, A_119) | ~v1_xboole_0(A_119))), inference(resolution, [status(thm)], [c_97, c_125])).
% 6.77/2.33  tff(c_152, plain, (![B_120, A_121]: (B_120=A_121 | ~v1_xboole_0(B_120) | ~v1_xboole_0(A_121))), inference(resolution, [status(thm)], [c_97, c_138])).
% 6.77/2.33  tff(c_155, plain, (![A_121]: (k1_xboole_0=A_121 | ~v1_xboole_0(A_121))), inference(resolution, [status(thm)], [c_12, c_152])).
% 6.77/2.33  tff(c_324, plain, (k2_relat_1('#skF_10')=k1_xboole_0), inference(resolution, [status(thm)], [c_318, c_155])).
% 6.77/2.33  tff(c_368, plain, (![A_154, D_155]: (r2_hidden(k1_funct_1(A_154, D_155), k2_relat_1(A_154)) | ~r2_hidden(D_155, k1_relat_1(A_154)) | ~v1_funct_1(A_154) | ~v1_relat_1(A_154))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.77/2.33  tff(c_376, plain, (![D_155]: (r2_hidden(k1_funct_1('#skF_10', D_155), k1_xboole_0) | ~r2_hidden(D_155, k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_324, c_368])).
% 6.77/2.33  tff(c_381, plain, (![D_156]: (r2_hidden(k1_funct_1('#skF_10', D_156), k1_xboole_0) | ~r2_hidden(D_156, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_82, c_376])).
% 6.77/2.33  tff(c_386, plain, (![D_156]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(D_156, k1_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_381, c_2])).
% 6.77/2.33  tff(c_391, plain, (![D_157]: (~r2_hidden(D_157, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_386])).
% 6.77/2.33  tff(c_416, plain, (v1_xboole_0(k1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_4, c_391])).
% 6.77/2.33  tff(c_422, plain, (k1_relat_1('#skF_10')=k1_xboole_0), inference(resolution, [status(thm)], [c_416, c_155])).
% 6.77/2.33  tff(c_427, plain, (k1_relset_1('#skF_8', '#skF_9', '#skF_10')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_422, c_283])).
% 6.77/2.33  tff(c_1013, plain, (![B_213, A_214, C_215]: (k1_xboole_0=B_213 | k1_relset_1(A_214, B_213, C_215)=A_214 | ~v1_funct_2(C_215, A_214, B_213) | ~m1_subset_1(C_215, k1_zfmisc_1(k2_zfmisc_1(A_214, B_213))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.77/2.33  tff(c_1016, plain, (k1_xboole_0='#skF_9' | k1_relset_1('#skF_8', '#skF_9', '#skF_10')='#skF_8' | ~v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_78, c_1013])).
% 6.77/2.33  tff(c_1022, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_427, c_1016])).
% 6.77/2.33  tff(c_1023, plain, (k1_xboole_0='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_68, c_1022])).
% 6.77/2.33  tff(c_1044, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1023, c_12])).
% 6.77/2.33  tff(c_1047, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_1044])).
% 6.77/2.33  tff(c_1049, plain, (~v1_xboole_0(k2_relat_1('#skF_10'))), inference(splitRight, [status(thm)], [c_309])).
% 6.77/2.33  tff(c_1455, plain, (~v1_xboole_0(k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_1441, c_1049])).
% 6.77/2.33  tff(c_1469, plain, (~v1_xboole_0(k1_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_82, c_1455])).
% 6.77/2.33  tff(c_1592, plain, (~v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1591, c_1469])).
% 6.77/2.33  tff(c_172, plain, (![C_126, B_127, A_128]: (v5_relat_1(C_126, B_127) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_128, B_127))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.77/2.33  tff(c_180, plain, (v5_relat_1('#skF_11', '#skF_7')), inference(resolution, [status(thm)], [c_74, c_172])).
% 6.77/2.33  tff(c_107, plain, (v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_74, c_99])).
% 6.77/2.33  tff(c_22, plain, (![A_14, D_53]: (r2_hidden(k1_funct_1(A_14, D_53), k2_relat_1(A_14)) | ~r2_hidden(D_53, k1_relat_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.77/2.33  tff(c_18, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.77/2.33  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.77/2.33  tff(c_1399, plain, (![A_268, C_269, B_6]: (r2_hidden('#skF_6'(A_268, k2_relat_1(A_268), C_269), B_6) | ~r1_tarski(k1_relat_1(A_268), B_6) | ~r2_hidden(C_269, k2_relat_1(A_268)) | ~v1_funct_1(A_268) | ~v1_relat_1(A_268))), inference(resolution, [status(thm)], [c_1389, c_6])).
% 6.77/2.33  tff(c_24, plain, (![A_14, C_50]: (k1_funct_1(A_14, '#skF_6'(A_14, k2_relat_1(A_14), C_50))=C_50 | ~r2_hidden(C_50, k2_relat_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.77/2.33  tff(c_1097, plain, (![A_225, D_226]: (r2_hidden(k1_funct_1(A_225, D_226), k2_relat_1(A_225)) | ~r2_hidden(D_226, k1_relat_1(A_225)) | ~v1_funct_1(A_225) | ~v1_relat_1(A_225))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.77/2.33  tff(c_1961, plain, (![A_310, D_311, B_312]: (r2_hidden(k1_funct_1(A_310, D_311), B_312) | ~r1_tarski(k2_relat_1(A_310), B_312) | ~r2_hidden(D_311, k1_relat_1(A_310)) | ~v1_funct_1(A_310) | ~v1_relat_1(A_310))), inference(resolution, [status(thm)], [c_1097, c_6])).
% 6.77/2.33  tff(c_2974, plain, (![A_431, D_432, B_433, B_434]: (r2_hidden(k1_funct_1(A_431, D_432), B_433) | ~r1_tarski(B_434, B_433) | ~r1_tarski(k2_relat_1(A_431), B_434) | ~r2_hidden(D_432, k1_relat_1(A_431)) | ~v1_funct_1(A_431) | ~v1_relat_1(A_431))), inference(resolution, [status(thm)], [c_1961, c_6])).
% 6.77/2.33  tff(c_2990, plain, (![A_435, D_436]: (r2_hidden(k1_funct_1(A_435, D_436), k1_relat_1('#skF_11')) | ~r1_tarski(k2_relat_1(A_435), k2_relat_1('#skF_10')) | ~r2_hidden(D_436, k1_relat_1(A_435)) | ~v1_funct_1(A_435) | ~v1_relat_1(A_435))), inference(resolution, [status(thm)], [c_290, c_2974])).
% 6.77/2.33  tff(c_3757, plain, (![A_541, D_542, B_543]: (r2_hidden(k1_funct_1(A_541, D_542), B_543) | ~r1_tarski(k1_relat_1('#skF_11'), B_543) | ~r1_tarski(k2_relat_1(A_541), k2_relat_1('#skF_10')) | ~r2_hidden(D_542, k1_relat_1(A_541)) | ~v1_funct_1(A_541) | ~v1_relat_1(A_541))), inference(resolution, [status(thm)], [c_2990, c_6])).
% 6.77/2.33  tff(c_3766, plain, (![D_542, B_543]: (r2_hidden(k1_funct_1('#skF_10', D_542), B_543) | ~r1_tarski(k1_relat_1('#skF_11'), B_543) | ~r2_hidden(D_542, k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_18, c_3757])).
% 6.77/2.33  tff(c_3772, plain, (![D_544, B_545]: (r2_hidden(k1_funct_1('#skF_10', D_544), B_545) | ~r1_tarski(k1_relat_1('#skF_11'), B_545) | ~r2_hidden(D_544, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_82, c_1591, c_3766])).
% 6.77/2.33  tff(c_3803, plain, (![C_50, B_545]: (r2_hidden(C_50, B_545) | ~r1_tarski(k1_relat_1('#skF_11'), B_545) | ~r2_hidden('#skF_6'('#skF_10', k2_relat_1('#skF_10'), C_50), '#skF_8') | ~r2_hidden(C_50, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_24, c_3772])).
% 6.77/2.33  tff(c_3830, plain, (![C_549, B_550]: (r2_hidden(C_549, B_550) | ~r1_tarski(k1_relat_1('#skF_11'), B_550) | ~r2_hidden('#skF_6'('#skF_10', k2_relat_1('#skF_10'), C_549), '#skF_8') | ~r2_hidden(C_549, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_82, c_3803])).
% 6.77/2.33  tff(c_3845, plain, (![C_551]: (r2_hidden(C_551, k1_relat_1('#skF_11')) | ~r2_hidden('#skF_6'('#skF_10', k2_relat_1('#skF_10'), C_551), '#skF_8') | ~r2_hidden(C_551, k2_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_18, c_3830])).
% 6.77/2.33  tff(c_3849, plain, (![C_269]: (r2_hidden(C_269, k1_relat_1('#skF_11')) | ~r1_tarski(k1_relat_1('#skF_10'), '#skF_8') | ~r2_hidden(C_269, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_1399, c_3845])).
% 6.77/2.33  tff(c_3870, plain, (![C_552]: (r2_hidden(C_552, k1_relat_1('#skF_11')) | ~r2_hidden(C_552, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_82, c_18, c_1591, c_3849])).
% 6.77/2.33  tff(c_3970, plain, (![D_53]: (r2_hidden(k1_funct_1('#skF_10', D_53), k1_relat_1('#skF_11')) | ~r2_hidden(D_53, k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_22, c_3870])).
% 6.77/2.33  tff(c_4104, plain, (![D_559]: (r2_hidden(k1_funct_1('#skF_10', D_559), k1_relat_1('#skF_11')) | ~r2_hidden(D_559, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_82, c_1591, c_3970])).
% 6.77/2.33  tff(c_62, plain, (![A_69, B_70, C_72]: (k7_partfun1(A_69, B_70, C_72)=k1_funct_1(B_70, C_72) | ~r2_hidden(C_72, k1_relat_1(B_70)) | ~v1_funct_1(B_70) | ~v5_relat_1(B_70, A_69) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.77/2.33  tff(c_4106, plain, (![A_69, D_559]: (k7_partfun1(A_69, '#skF_11', k1_funct_1('#skF_10', D_559))=k1_funct_1('#skF_11', k1_funct_1('#skF_10', D_559)) | ~v1_funct_1('#skF_11') | ~v5_relat_1('#skF_11', A_69) | ~v1_relat_1('#skF_11') | ~r2_hidden(D_559, '#skF_8'))), inference(resolution, [status(thm)], [c_4104, c_62])).
% 6.77/2.33  tff(c_4502, plain, (![A_575, D_576]: (k7_partfun1(A_575, '#skF_11', k1_funct_1('#skF_10', D_576))=k1_funct_1('#skF_11', k1_funct_1('#skF_10', D_576)) | ~v5_relat_1('#skF_11', A_575) | ~r2_hidden(D_576, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_76, c_4106])).
% 6.77/2.33  tff(c_66, plain, (k7_partfun1('#skF_7', '#skF_11', k1_funct_1('#skF_10', '#skF_12'))!=k1_funct_1(k8_funct_2('#skF_8', '#skF_9', '#skF_7', '#skF_10', '#skF_11'), '#skF_12')), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.77/2.33  tff(c_4508, plain, (k1_funct_1(k8_funct_2('#skF_8', '#skF_9', '#skF_7', '#skF_10', '#skF_11'), '#skF_12')!=k1_funct_1('#skF_11', k1_funct_1('#skF_10', '#skF_12')) | ~v5_relat_1('#skF_11', '#skF_7') | ~r2_hidden('#skF_12', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_4502, c_66])).
% 6.77/2.33  tff(c_4526, plain, (k1_funct_1(k8_funct_2('#skF_8', '#skF_9', '#skF_7', '#skF_10', '#skF_11'), '#skF_12')!=k1_funct_1('#skF_11', k1_funct_1('#skF_10', '#skF_12')) | ~r2_hidden('#skF_12', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_180, c_4508])).
% 6.77/2.33  tff(c_4532, plain, (~r2_hidden('#skF_12', '#skF_8')), inference(splitLeft, [status(thm)], [c_4526])).
% 6.77/2.33  tff(c_4535, plain, (v1_xboole_0('#skF_8') | ~m1_subset_1('#skF_12', '#skF_8')), inference(resolution, [status(thm)], [c_20, c_4532])).
% 6.77/2.33  tff(c_4538, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_4535])).
% 6.77/2.33  tff(c_4540, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1592, c_4538])).
% 6.77/2.33  tff(c_4541, plain, (k1_funct_1(k8_funct_2('#skF_8', '#skF_9', '#skF_7', '#skF_10', '#skF_11'), '#skF_12')!=k1_funct_1('#skF_11', k1_funct_1('#skF_10', '#skF_12'))), inference(splitRight, [status(thm)], [c_4526])).
% 6.77/2.33  tff(c_4665, plain, (~m1_subset_1('#skF_12', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_2929, c_4541])).
% 6.77/2.33  tff(c_4669, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_4665])).
% 6.77/2.33  tff(c_4670, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_1587])).
% 6.77/2.33  tff(c_4681, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_4670, c_12])).
% 6.77/2.33  tff(c_4684, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_4681])).
% 6.77/2.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.77/2.33  
% 6.77/2.33  Inference rules
% 6.77/2.33  ----------------------
% 6.77/2.33  #Ref     : 0
% 6.77/2.33  #Sup     : 1029
% 6.77/2.33  #Fact    : 0
% 6.77/2.33  #Define  : 0
% 6.77/2.33  #Split   : 16
% 6.77/2.33  #Chain   : 0
% 6.77/2.33  #Close   : 0
% 6.77/2.33  
% 6.77/2.33  Ordering : KBO
% 6.77/2.33  
% 6.77/2.33  Simplification rules
% 6.77/2.33  ----------------------
% 6.77/2.33  #Subsume      : 501
% 6.77/2.33  #Demod        : 516
% 6.77/2.33  #Tautology    : 133
% 6.77/2.33  #SimpNegUnit  : 40
% 6.77/2.33  #BackRed      : 43
% 6.77/2.33  
% 6.77/2.33  #Partial instantiations: 0
% 6.77/2.33  #Strategies tried      : 1
% 6.77/2.33  
% 6.77/2.33  Timing (in seconds)
% 6.77/2.33  ----------------------
% 6.77/2.33  Preprocessing        : 0.36
% 6.77/2.33  Parsing              : 0.18
% 6.77/2.33  CNF conversion       : 0.03
% 6.77/2.33  Main loop            : 1.21
% 6.77/2.33  Inferencing          : 0.37
% 6.77/2.33  Reduction            : 0.35
% 6.77/2.33  Demodulation         : 0.24
% 6.77/2.33  BG Simplification    : 0.04
% 6.77/2.33  Subsumption          : 0.36
% 6.77/2.33  Abstraction          : 0.05
% 6.77/2.33  MUC search           : 0.00
% 6.77/2.33  Cooper               : 0.00
% 6.77/2.33  Total                : 1.61
% 6.77/2.33  Index Insertion      : 0.00
% 6.77/2.33  Index Deletion       : 0.00
% 6.77/2.33  Index Matching       : 0.00
% 6.77/2.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
