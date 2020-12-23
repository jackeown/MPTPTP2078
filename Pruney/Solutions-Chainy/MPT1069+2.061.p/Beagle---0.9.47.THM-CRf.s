%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:54 EST 2020

% Result     : Theorem 9.25s
% Output     : CNFRefutation 9.25s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 541 expanded)
%              Number of leaves         :   50 ( 211 expanded)
%              Depth                    :   19
%              Number of atoms          :  320 (1793 expanded)
%              Number of equality atoms :   58 ( 397 expanded)
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

tff(f_171,negated_conjecture,(
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

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_146,axiom,(
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

tff(f_111,axiom,(
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

tff(f_59,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_74,axiom,(
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

tff(f_44,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_50,axiom,(
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

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_79,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_122,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_72,plain,(
    m1_subset_1('#skF_12','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_76,plain,(
    v1_funct_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_74,plain,(
    m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_287,plain,(
    ! [A_149,B_150,C_151] :
      ( k1_relset_1(A_149,B_150,C_151) = k1_relat_1(C_151)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_295,plain,(
    k1_relset_1('#skF_9','#skF_7','#skF_11') = k1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_74,c_287])).

tff(c_78,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_218,plain,(
    ! [A_140,B_141,C_142] :
      ( k2_relset_1(A_140,B_141,C_142) = k2_relat_1(C_142)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_225,plain,(
    k2_relset_1('#skF_8','#skF_9','#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_78,c_218])).

tff(c_70,plain,(
    r1_tarski(k2_relset_1('#skF_8','#skF_9','#skF_10'),k1_relset_1('#skF_9','#skF_7','#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_227,plain,(
    r1_tarski(k2_relat_1('#skF_10'),k1_relset_1('#skF_9','#skF_7','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_70])).

tff(c_319,plain,(
    r1_tarski(k2_relat_1('#skF_10'),k1_relat_1('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_227])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_82,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_80,plain,(
    v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_2680,plain,(
    ! [F_383,B_385,C_387,A_384,E_388,D_386] :
      ( k1_funct_1(k8_funct_2(B_385,C_387,A_384,D_386,E_388),F_383) = k1_funct_1(E_388,k1_funct_1(D_386,F_383))
      | k1_xboole_0 = B_385
      | ~ r1_tarski(k2_relset_1(B_385,C_387,D_386),k1_relset_1(C_387,A_384,E_388))
      | ~ m1_subset_1(F_383,B_385)
      | ~ m1_subset_1(E_388,k1_zfmisc_1(k2_zfmisc_1(C_387,A_384)))
      | ~ v1_funct_1(E_388)
      | ~ m1_subset_1(D_386,k1_zfmisc_1(k2_zfmisc_1(B_385,C_387)))
      | ~ v1_funct_2(D_386,B_385,C_387)
      | ~ v1_funct_1(D_386)
      | v1_xboole_0(C_387) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_2688,plain,(
    ! [A_384,E_388,F_383] :
      ( k1_funct_1(k8_funct_2('#skF_8','#skF_9',A_384,'#skF_10',E_388),F_383) = k1_funct_1(E_388,k1_funct_1('#skF_10',F_383))
      | k1_xboole_0 = '#skF_8'
      | ~ r1_tarski(k2_relat_1('#skF_10'),k1_relset_1('#skF_9',A_384,E_388))
      | ~ m1_subset_1(F_383,'#skF_8')
      | ~ m1_subset_1(E_388,k1_zfmisc_1(k2_zfmisc_1('#skF_9',A_384)))
      | ~ v1_funct_1(E_388)
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9')))
      | ~ v1_funct_2('#skF_10','#skF_8','#skF_9')
      | ~ v1_funct_1('#skF_10')
      | v1_xboole_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_2680])).

tff(c_2701,plain,(
    ! [A_384,E_388,F_383] :
      ( k1_funct_1(k8_funct_2('#skF_8','#skF_9',A_384,'#skF_10',E_388),F_383) = k1_funct_1(E_388,k1_funct_1('#skF_10',F_383))
      | k1_xboole_0 = '#skF_8'
      | ~ r1_tarski(k2_relat_1('#skF_10'),k1_relset_1('#skF_9',A_384,E_388))
      | ~ m1_subset_1(F_383,'#skF_8')
      | ~ m1_subset_1(E_388,k1_zfmisc_1(k2_zfmisc_1('#skF_9',A_384)))
      | ~ v1_funct_1(E_388)
      | v1_xboole_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_2688])).

tff(c_2745,plain,(
    ! [A_393,E_394,F_395] :
      ( k1_funct_1(k8_funct_2('#skF_8','#skF_9',A_393,'#skF_10',E_394),F_395) = k1_funct_1(E_394,k1_funct_1('#skF_10',F_395))
      | ~ r1_tarski(k2_relat_1('#skF_10'),k1_relset_1('#skF_9',A_393,E_394))
      | ~ m1_subset_1(F_395,'#skF_8')
      | ~ m1_subset_1(E_394,k1_zfmisc_1(k2_zfmisc_1('#skF_9',A_393)))
      | ~ v1_funct_1(E_394) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_68,c_2701])).

tff(c_2750,plain,(
    ! [F_395] :
      ( k1_funct_1(k8_funct_2('#skF_8','#skF_9','#skF_7','#skF_10','#skF_11'),F_395) = k1_funct_1('#skF_11',k1_funct_1('#skF_10',F_395))
      | ~ r1_tarski(k2_relat_1('#skF_10'),k1_relat_1('#skF_11'))
      | ~ m1_subset_1(F_395,'#skF_8')
      | ~ m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_7')))
      | ~ v1_funct_1('#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_2745])).

tff(c_2758,plain,(
    ! [F_395] :
      ( k1_funct_1(k8_funct_2('#skF_8','#skF_9','#skF_7','#skF_10','#skF_11'),F_395) = k1_funct_1('#skF_11',k1_funct_1('#skF_10',F_395))
      | ~ m1_subset_1(F_395,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_319,c_2750])).

tff(c_294,plain,(
    k1_relset_1('#skF_8','#skF_9','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_78,c_287])).

tff(c_1732,plain,(
    ! [B_305,A_306,C_307] :
      ( k1_xboole_0 = B_305
      | k1_relset_1(A_306,B_305,C_307) = A_306
      | ~ v1_funct_2(C_307,A_306,B_305)
      | ~ m1_subset_1(C_307,k1_zfmisc_1(k2_zfmisc_1(A_306,B_305))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1735,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relset_1('#skF_8','#skF_9','#skF_10') = '#skF_8'
    | ~ v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_78,c_1732])).

tff(c_1741,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relat_1('#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_294,c_1735])).

tff(c_1744,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1741])).

tff(c_20,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_132,plain,(
    ! [B_122,A_123] :
      ( v1_relat_1(B_122)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(A_123))
      | ~ v1_relat_1(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_135,plain,
    ( v1_relat_1('#skF_10')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_78,c_132])).

tff(c_141,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_135])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1442,plain,(
    ! [A_277,C_278] :
      ( r2_hidden('#skF_6'(A_277,k2_relat_1(A_277),C_278),k1_relat_1(A_277))
      | ~ r2_hidden(C_278,k2_relat_1(A_277))
      | ~ v1_funct_1(A_277)
      | ~ v1_relat_1(A_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1480,plain,(
    ! [A_282,C_283] :
      ( ~ v1_xboole_0(k1_relat_1(A_282))
      | ~ r2_hidden(C_283,k2_relat_1(A_282))
      | ~ v1_funct_1(A_282)
      | ~ v1_relat_1(A_282) ) ),
    inference(resolution,[status(thm)],[c_1442,c_2])).

tff(c_1520,plain,(
    ! [A_284] :
      ( ~ v1_xboole_0(k1_relat_1(A_284))
      | ~ v1_funct_1(A_284)
      | ~ v1_relat_1(A_284)
      | v1_xboole_0(k2_relat_1(A_284)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1480])).

tff(c_14,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( r2_hidden(A_12,B_13)
      | v1_xboole_0(B_13)
      | ~ m1_subset_1(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_159,plain,(
    ! [C_126,B_127,A_128] :
      ( r2_hidden(C_126,B_127)
      | ~ r2_hidden(C_126,A_128)
      | ~ r1_tarski(A_128,B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_337,plain,(
    ! [A_156,B_157,B_158] :
      ( r2_hidden(A_156,B_157)
      | ~ r1_tarski(B_158,B_157)
      | v1_xboole_0(B_158)
      | ~ m1_subset_1(A_156,B_158) ) ),
    inference(resolution,[status(thm)],[c_16,c_159])).

tff(c_346,plain,(
    ! [A_156] :
      ( r2_hidden(A_156,k1_relat_1('#skF_11'))
      | v1_xboole_0(k2_relat_1('#skF_10'))
      | ~ m1_subset_1(A_156,k2_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_319,c_337])).

tff(c_368,plain,(
    v1_xboole_0(k2_relat_1('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_346])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_372,plain,(
    k2_relat_1('#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_368,c_12])).

tff(c_398,plain,(
    ! [A_165,D_166] :
      ( r2_hidden(k1_funct_1(A_165,D_166),k2_relat_1(A_165))
      | ~ r2_hidden(D_166,k1_relat_1(A_165))
      | ~ v1_funct_1(A_165)
      | ~ v1_relat_1(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_409,plain,(
    ! [D_166] :
      ( r2_hidden(k1_funct_1('#skF_10',D_166),k1_xboole_0)
      | ~ r2_hidden(D_166,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_398])).

tff(c_415,plain,(
    ! [D_167] :
      ( r2_hidden(k1_funct_1('#skF_10',D_167),k1_xboole_0)
      | ~ r2_hidden(D_167,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_82,c_409])).

tff(c_40,plain,(
    ! [B_60,A_59] :
      ( ~ r1_tarski(B_60,A_59)
      | ~ r2_hidden(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_420,plain,(
    ! [D_167] :
      ( ~ r1_tarski(k1_xboole_0,k1_funct_1('#skF_10',D_167))
      | ~ r2_hidden(D_167,k1_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_415,c_40])).

tff(c_433,plain,(
    ! [D_168] : ~ r2_hidden(D_168,k1_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_420])).

tff(c_458,plain,(
    v1_xboole_0(k1_relat_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_4,c_433])).

tff(c_462,plain,(
    k1_relat_1('#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_458,c_12])).

tff(c_465,plain,(
    k1_relset_1('#skF_8','#skF_9','#skF_10') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_462,c_294])).

tff(c_962,plain,(
    ! [B_220,A_221,C_222] :
      ( k1_xboole_0 = B_220
      | k1_relset_1(A_221,B_220,C_222) = A_221
      | ~ v1_funct_2(C_222,A_221,B_220)
      | ~ m1_subset_1(C_222,k1_zfmisc_1(k2_zfmisc_1(A_221,B_220))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_965,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relset_1('#skF_8','#skF_9','#skF_10') = '#skF_8'
    | ~ v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_78,c_962])).

tff(c_971,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_465,c_965])).

tff(c_972,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_971])).

tff(c_94,plain,(
    ! [B_112,A_113] :
      ( ~ r1_tarski(B_112,A_113)
      | ~ r2_hidden(A_113,B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_99,plain,(
    ! [A_114] :
      ( ~ r1_tarski(A_114,'#skF_1'(A_114))
      | v1_xboole_0(A_114) ) ),
    inference(resolution,[status(thm)],[c_4,c_94])).

tff(c_104,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_99])).

tff(c_991,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_972,c_104])).

tff(c_996,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_991])).

tff(c_998,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_346])).

tff(c_1529,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_1520,c_998])).

tff(c_1539,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_82,c_1529])).

tff(c_1745,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1744,c_1539])).

tff(c_209,plain,(
    ! [C_137,B_138,A_139] :
      ( v5_relat_1(C_137,B_138)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_139,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_217,plain,(
    v5_relat_1('#skF_11','#skF_7') ),
    inference(resolution,[status(thm)],[c_74,c_209])).

tff(c_138,plain,
    ( v1_relat_1('#skF_11')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_9','#skF_7')) ),
    inference(resolution,[status(thm)],[c_74,c_132])).

tff(c_144,plain,(
    v1_relat_1('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_138])).

tff(c_22,plain,(
    ! [A_19,D_58] :
      ( r2_hidden(k1_funct_1(A_19,D_58),k2_relat_1(A_19))
      | ~ r2_hidden(D_58,k1_relat_1(A_19))
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_125,plain,(
    ! [A_119,B_120] :
      ( ~ r2_hidden('#skF_2'(A_119,B_120),B_120)
      | r1_tarski(A_119,B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_130,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_10,c_125])).

tff(c_26,plain,(
    ! [A_19,C_55] :
      ( r2_hidden('#skF_6'(A_19,k2_relat_1(A_19),C_55),k1_relat_1(A_19))
      | ~ r2_hidden(C_55,k2_relat_1(A_19))
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1756,plain,(
    ! [C_55] :
      ( r2_hidden('#skF_6'('#skF_10',k2_relat_1('#skF_10'),C_55),'#skF_8')
      | ~ r2_hidden(C_55,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1744,c_26])).

tff(c_1843,plain,(
    ! [C_311] :
      ( r2_hidden('#skF_6'('#skF_10',k2_relat_1('#skF_10'),C_311),'#skF_8')
      | ~ r2_hidden(C_311,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_82,c_1756])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1852,plain,(
    ! [C_311,B_6] :
      ( r2_hidden('#skF_6'('#skF_10',k2_relat_1('#skF_10'),C_311),B_6)
      | ~ r1_tarski('#skF_8',B_6)
      | ~ r2_hidden(C_311,k2_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_1843,c_6])).

tff(c_24,plain,(
    ! [A_19,C_55] :
      ( k1_funct_1(A_19,'#skF_6'(A_19,k2_relat_1(A_19),C_55)) = C_55
      | ~ r2_hidden(C_55,k2_relat_1(A_19))
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1041,plain,(
    ! [A_228,D_229] :
      ( r2_hidden(k1_funct_1(A_228,D_229),k2_relat_1(A_228))
      | ~ r2_hidden(D_229,k1_relat_1(A_228))
      | ~ v1_funct_1(A_228)
      | ~ v1_relat_1(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2907,plain,(
    ! [A_406,D_407,B_408] :
      ( r2_hidden(k1_funct_1(A_406,D_407),B_408)
      | ~ r1_tarski(k2_relat_1(A_406),B_408)
      | ~ r2_hidden(D_407,k1_relat_1(A_406))
      | ~ v1_funct_1(A_406)
      | ~ v1_relat_1(A_406) ) ),
    inference(resolution,[status(thm)],[c_1041,c_6])).

tff(c_6776,plain,(
    ! [A_703,D_704,B_705,B_706] :
      ( r2_hidden(k1_funct_1(A_703,D_704),B_705)
      | ~ r1_tarski(B_706,B_705)
      | ~ r1_tarski(k2_relat_1(A_703),B_706)
      | ~ r2_hidden(D_704,k1_relat_1(A_703))
      | ~ v1_funct_1(A_703)
      | ~ v1_relat_1(A_703) ) ),
    inference(resolution,[status(thm)],[c_2907,c_6])).

tff(c_6798,plain,(
    ! [A_707,D_708] :
      ( r2_hidden(k1_funct_1(A_707,D_708),k1_relat_1('#skF_11'))
      | ~ r1_tarski(k2_relat_1(A_707),k2_relat_1('#skF_10'))
      | ~ r2_hidden(D_708,k1_relat_1(A_707))
      | ~ v1_funct_1(A_707)
      | ~ v1_relat_1(A_707) ) ),
    inference(resolution,[status(thm)],[c_319,c_6776])).

tff(c_7734,plain,(
    ! [C_747,A_748] :
      ( r2_hidden(C_747,k1_relat_1('#skF_11'))
      | ~ r1_tarski(k2_relat_1(A_748),k2_relat_1('#skF_10'))
      | ~ r2_hidden('#skF_6'(A_748,k2_relat_1(A_748),C_747),k1_relat_1(A_748))
      | ~ v1_funct_1(A_748)
      | ~ v1_relat_1(A_748)
      | ~ r2_hidden(C_747,k2_relat_1(A_748))
      | ~ v1_funct_1(A_748)
      | ~ v1_relat_1(A_748) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_6798])).

tff(c_7742,plain,(
    ! [C_311] :
      ( r2_hidden(C_311,k1_relat_1('#skF_11'))
      | ~ r1_tarski(k2_relat_1('#skF_10'),k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r1_tarski('#skF_8',k1_relat_1('#skF_10'))
      | ~ r2_hidden(C_311,k2_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_1852,c_7734])).

tff(c_7769,plain,(
    ! [C_749] :
      ( r2_hidden(C_749,k1_relat_1('#skF_11'))
      | ~ r2_hidden(C_749,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_1744,c_141,c_82,c_130,c_7742])).

tff(c_7915,plain,(
    ! [D_58] :
      ( r2_hidden(k1_funct_1('#skF_10',D_58),k1_relat_1('#skF_11'))
      | ~ r2_hidden(D_58,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_22,c_7769])).

tff(c_8023,plain,(
    ! [D_750] :
      ( r2_hidden(k1_funct_1('#skF_10',D_750),k1_relat_1('#skF_11'))
      | ~ r2_hidden(D_750,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_82,c_1744,c_7915])).

tff(c_62,plain,(
    ! [A_73,B_74,C_76] :
      ( k7_partfun1(A_73,B_74,C_76) = k1_funct_1(B_74,C_76)
      | ~ r2_hidden(C_76,k1_relat_1(B_74))
      | ~ v1_funct_1(B_74)
      | ~ v5_relat_1(B_74,A_73)
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_8031,plain,(
    ! [A_73,D_750] :
      ( k7_partfun1(A_73,'#skF_11',k1_funct_1('#skF_10',D_750)) = k1_funct_1('#skF_11',k1_funct_1('#skF_10',D_750))
      | ~ v1_funct_1('#skF_11')
      | ~ v5_relat_1('#skF_11',A_73)
      | ~ v1_relat_1('#skF_11')
      | ~ r2_hidden(D_750,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_8023,c_62])).

tff(c_9085,plain,(
    ! [A_780,D_781] :
      ( k7_partfun1(A_780,'#skF_11',k1_funct_1('#skF_10',D_781)) = k1_funct_1('#skF_11',k1_funct_1('#skF_10',D_781))
      | ~ v5_relat_1('#skF_11',A_780)
      | ~ r2_hidden(D_781,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_76,c_8031])).

tff(c_66,plain,(
    k7_partfun1('#skF_7','#skF_11',k1_funct_1('#skF_10','#skF_12')) != k1_funct_1(k8_funct_2('#skF_8','#skF_9','#skF_7','#skF_10','#skF_11'),'#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_9091,plain,
    ( k1_funct_1(k8_funct_2('#skF_8','#skF_9','#skF_7','#skF_10','#skF_11'),'#skF_12') != k1_funct_1('#skF_11',k1_funct_1('#skF_10','#skF_12'))
    | ~ v5_relat_1('#skF_11','#skF_7')
    | ~ r2_hidden('#skF_12','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_9085,c_66])).

tff(c_9115,plain,
    ( k1_funct_1(k8_funct_2('#skF_8','#skF_9','#skF_7','#skF_10','#skF_11'),'#skF_12') != k1_funct_1('#skF_11',k1_funct_1('#skF_10','#skF_12'))
    | ~ r2_hidden('#skF_12','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_9091])).

tff(c_9171,plain,(
    ~ r2_hidden('#skF_12','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_9115])).

tff(c_9174,plain,
    ( v1_xboole_0('#skF_8')
    | ~ m1_subset_1('#skF_12','#skF_8') ),
    inference(resolution,[status(thm)],[c_16,c_9171])).

tff(c_9177,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_9174])).

tff(c_9179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1745,c_9177])).

tff(c_9180,plain,(
    k1_funct_1(k8_funct_2('#skF_8','#skF_9','#skF_7','#skF_10','#skF_11'),'#skF_12') != k1_funct_1('#skF_11',k1_funct_1('#skF_10','#skF_12')) ),
    inference(splitRight,[status(thm)],[c_9115])).

tff(c_9198,plain,(
    ~ m1_subset_1('#skF_12','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_2758,c_9180])).

tff(c_9202,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_9198])).

tff(c_9203,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1741])).

tff(c_9215,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9203,c_104])).

tff(c_9220,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_9215])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:33:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.25/3.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.25/3.22  
% 9.25/3.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.25/3.22  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_2 > #skF_5 > #skF_12 > #skF_4
% 9.25/3.22  
% 9.25/3.22  %Foreground sorts:
% 9.25/3.22  
% 9.25/3.22  
% 9.25/3.22  %Background operators:
% 9.25/3.22  
% 9.25/3.22  
% 9.25/3.22  %Foreground operators:
% 9.25/3.22  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.25/3.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.25/3.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.25/3.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.25/3.22  tff('#skF_11', type, '#skF_11': $i).
% 9.25/3.22  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 9.25/3.22  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.25/3.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.25/3.22  tff('#skF_7', type, '#skF_7': $i).
% 9.25/3.22  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.25/3.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.25/3.22  tff('#skF_10', type, '#skF_10': $i).
% 9.25/3.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.25/3.22  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 9.25/3.22  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.25/3.22  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 9.25/3.22  tff('#skF_9', type, '#skF_9': $i).
% 9.25/3.22  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.25/3.22  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.25/3.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.25/3.22  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.25/3.22  tff('#skF_8', type, '#skF_8': $i).
% 9.25/3.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.25/3.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.25/3.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.25/3.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.25/3.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.25/3.22  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.25/3.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.25/3.22  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 9.25/3.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.25/3.22  tff('#skF_12', type, '#skF_12': $i).
% 9.25/3.22  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.25/3.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.25/3.22  
% 9.25/3.25  tff(f_171, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 9.25/3.25  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.25/3.25  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.25/3.25  tff(f_146, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 9.25/3.25  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 9.25/3.25  tff(f_59, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.25/3.25  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.25/3.25  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.25/3.25  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 9.25/3.25  tff(f_44, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.25/3.25  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 9.25/3.25  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 9.25/3.25  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 9.25/3.25  tff(f_79, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 9.25/3.25  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.25/3.25  tff(f_122, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 9.25/3.25  tff(c_84, plain, (~v1_xboole_0('#skF_9')), inference(cnfTransformation, [status(thm)], [f_171])).
% 9.25/3.25  tff(c_72, plain, (m1_subset_1('#skF_12', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_171])).
% 9.25/3.25  tff(c_76, plain, (v1_funct_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_171])).
% 9.25/3.25  tff(c_74, plain, (m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_171])).
% 9.25/3.25  tff(c_287, plain, (![A_149, B_150, C_151]: (k1_relset_1(A_149, B_150, C_151)=k1_relat_1(C_151) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.25/3.25  tff(c_295, plain, (k1_relset_1('#skF_9', '#skF_7', '#skF_11')=k1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_74, c_287])).
% 9.25/3.25  tff(c_78, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(cnfTransformation, [status(thm)], [f_171])).
% 9.25/3.25  tff(c_218, plain, (![A_140, B_141, C_142]: (k2_relset_1(A_140, B_141, C_142)=k2_relat_1(C_142) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.25/3.25  tff(c_225, plain, (k2_relset_1('#skF_8', '#skF_9', '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_78, c_218])).
% 9.25/3.25  tff(c_70, plain, (r1_tarski(k2_relset_1('#skF_8', '#skF_9', '#skF_10'), k1_relset_1('#skF_9', '#skF_7', '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_171])).
% 9.25/3.25  tff(c_227, plain, (r1_tarski(k2_relat_1('#skF_10'), k1_relset_1('#skF_9', '#skF_7', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_225, c_70])).
% 9.25/3.25  tff(c_319, plain, (r1_tarski(k2_relat_1('#skF_10'), k1_relat_1('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_295, c_227])).
% 9.25/3.25  tff(c_68, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_171])).
% 9.25/3.25  tff(c_82, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_171])).
% 9.25/3.25  tff(c_80, plain, (v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_171])).
% 9.25/3.25  tff(c_2680, plain, (![F_383, B_385, C_387, A_384, E_388, D_386]: (k1_funct_1(k8_funct_2(B_385, C_387, A_384, D_386, E_388), F_383)=k1_funct_1(E_388, k1_funct_1(D_386, F_383)) | k1_xboole_0=B_385 | ~r1_tarski(k2_relset_1(B_385, C_387, D_386), k1_relset_1(C_387, A_384, E_388)) | ~m1_subset_1(F_383, B_385) | ~m1_subset_1(E_388, k1_zfmisc_1(k2_zfmisc_1(C_387, A_384))) | ~v1_funct_1(E_388) | ~m1_subset_1(D_386, k1_zfmisc_1(k2_zfmisc_1(B_385, C_387))) | ~v1_funct_2(D_386, B_385, C_387) | ~v1_funct_1(D_386) | v1_xboole_0(C_387))), inference(cnfTransformation, [status(thm)], [f_146])).
% 9.25/3.25  tff(c_2688, plain, (![A_384, E_388, F_383]: (k1_funct_1(k8_funct_2('#skF_8', '#skF_9', A_384, '#skF_10', E_388), F_383)=k1_funct_1(E_388, k1_funct_1('#skF_10', F_383)) | k1_xboole_0='#skF_8' | ~r1_tarski(k2_relat_1('#skF_10'), k1_relset_1('#skF_9', A_384, E_388)) | ~m1_subset_1(F_383, '#skF_8') | ~m1_subset_1(E_388, k1_zfmisc_1(k2_zfmisc_1('#skF_9', A_384))) | ~v1_funct_1(E_388) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9'))) | ~v1_funct_2('#skF_10', '#skF_8', '#skF_9') | ~v1_funct_1('#skF_10') | v1_xboole_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_225, c_2680])).
% 9.25/3.25  tff(c_2701, plain, (![A_384, E_388, F_383]: (k1_funct_1(k8_funct_2('#skF_8', '#skF_9', A_384, '#skF_10', E_388), F_383)=k1_funct_1(E_388, k1_funct_1('#skF_10', F_383)) | k1_xboole_0='#skF_8' | ~r1_tarski(k2_relat_1('#skF_10'), k1_relset_1('#skF_9', A_384, E_388)) | ~m1_subset_1(F_383, '#skF_8') | ~m1_subset_1(E_388, k1_zfmisc_1(k2_zfmisc_1('#skF_9', A_384))) | ~v1_funct_1(E_388) | v1_xboole_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_2688])).
% 9.25/3.25  tff(c_2745, plain, (![A_393, E_394, F_395]: (k1_funct_1(k8_funct_2('#skF_8', '#skF_9', A_393, '#skF_10', E_394), F_395)=k1_funct_1(E_394, k1_funct_1('#skF_10', F_395)) | ~r1_tarski(k2_relat_1('#skF_10'), k1_relset_1('#skF_9', A_393, E_394)) | ~m1_subset_1(F_395, '#skF_8') | ~m1_subset_1(E_394, k1_zfmisc_1(k2_zfmisc_1('#skF_9', A_393))) | ~v1_funct_1(E_394))), inference(negUnitSimplification, [status(thm)], [c_84, c_68, c_2701])).
% 9.25/3.25  tff(c_2750, plain, (![F_395]: (k1_funct_1(k8_funct_2('#skF_8', '#skF_9', '#skF_7', '#skF_10', '#skF_11'), F_395)=k1_funct_1('#skF_11', k1_funct_1('#skF_10', F_395)) | ~r1_tarski(k2_relat_1('#skF_10'), k1_relat_1('#skF_11')) | ~m1_subset_1(F_395, '#skF_8') | ~m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_7'))) | ~v1_funct_1('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_295, c_2745])).
% 9.25/3.25  tff(c_2758, plain, (![F_395]: (k1_funct_1(k8_funct_2('#skF_8', '#skF_9', '#skF_7', '#skF_10', '#skF_11'), F_395)=k1_funct_1('#skF_11', k1_funct_1('#skF_10', F_395)) | ~m1_subset_1(F_395, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_319, c_2750])).
% 9.25/3.25  tff(c_294, plain, (k1_relset_1('#skF_8', '#skF_9', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_78, c_287])).
% 9.25/3.25  tff(c_1732, plain, (![B_305, A_306, C_307]: (k1_xboole_0=B_305 | k1_relset_1(A_306, B_305, C_307)=A_306 | ~v1_funct_2(C_307, A_306, B_305) | ~m1_subset_1(C_307, k1_zfmisc_1(k2_zfmisc_1(A_306, B_305))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.25/3.25  tff(c_1735, plain, (k1_xboole_0='#skF_9' | k1_relset_1('#skF_8', '#skF_9', '#skF_10')='#skF_8' | ~v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_78, c_1732])).
% 9.25/3.25  tff(c_1741, plain, (k1_xboole_0='#skF_9' | k1_relat_1('#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_294, c_1735])).
% 9.25/3.25  tff(c_1744, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(splitLeft, [status(thm)], [c_1741])).
% 9.25/3.25  tff(c_20, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.25/3.25  tff(c_132, plain, (![B_122, A_123]: (v1_relat_1(B_122) | ~m1_subset_1(B_122, k1_zfmisc_1(A_123)) | ~v1_relat_1(A_123))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.25/3.25  tff(c_135, plain, (v1_relat_1('#skF_10') | ~v1_relat_1(k2_zfmisc_1('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_78, c_132])).
% 9.25/3.25  tff(c_141, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_135])).
% 9.25/3.25  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.25/3.25  tff(c_1442, plain, (![A_277, C_278]: (r2_hidden('#skF_6'(A_277, k2_relat_1(A_277), C_278), k1_relat_1(A_277)) | ~r2_hidden(C_278, k2_relat_1(A_277)) | ~v1_funct_1(A_277) | ~v1_relat_1(A_277))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.25/3.25  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.25/3.25  tff(c_1480, plain, (![A_282, C_283]: (~v1_xboole_0(k1_relat_1(A_282)) | ~r2_hidden(C_283, k2_relat_1(A_282)) | ~v1_funct_1(A_282) | ~v1_relat_1(A_282))), inference(resolution, [status(thm)], [c_1442, c_2])).
% 9.25/3.25  tff(c_1520, plain, (![A_284]: (~v1_xboole_0(k1_relat_1(A_284)) | ~v1_funct_1(A_284) | ~v1_relat_1(A_284) | v1_xboole_0(k2_relat_1(A_284)))), inference(resolution, [status(thm)], [c_4, c_1480])).
% 9.25/3.25  tff(c_14, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.25/3.25  tff(c_16, plain, (![A_12, B_13]: (r2_hidden(A_12, B_13) | v1_xboole_0(B_13) | ~m1_subset_1(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.25/3.25  tff(c_159, plain, (![C_126, B_127, A_128]: (r2_hidden(C_126, B_127) | ~r2_hidden(C_126, A_128) | ~r1_tarski(A_128, B_127))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.25/3.25  tff(c_337, plain, (![A_156, B_157, B_158]: (r2_hidden(A_156, B_157) | ~r1_tarski(B_158, B_157) | v1_xboole_0(B_158) | ~m1_subset_1(A_156, B_158))), inference(resolution, [status(thm)], [c_16, c_159])).
% 9.25/3.25  tff(c_346, plain, (![A_156]: (r2_hidden(A_156, k1_relat_1('#skF_11')) | v1_xboole_0(k2_relat_1('#skF_10')) | ~m1_subset_1(A_156, k2_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_319, c_337])).
% 9.25/3.25  tff(c_368, plain, (v1_xboole_0(k2_relat_1('#skF_10'))), inference(splitLeft, [status(thm)], [c_346])).
% 9.25/3.25  tff(c_12, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.25/3.25  tff(c_372, plain, (k2_relat_1('#skF_10')=k1_xboole_0), inference(resolution, [status(thm)], [c_368, c_12])).
% 9.25/3.25  tff(c_398, plain, (![A_165, D_166]: (r2_hidden(k1_funct_1(A_165, D_166), k2_relat_1(A_165)) | ~r2_hidden(D_166, k1_relat_1(A_165)) | ~v1_funct_1(A_165) | ~v1_relat_1(A_165))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.25/3.25  tff(c_409, plain, (![D_166]: (r2_hidden(k1_funct_1('#skF_10', D_166), k1_xboole_0) | ~r2_hidden(D_166, k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_372, c_398])).
% 9.25/3.25  tff(c_415, plain, (![D_167]: (r2_hidden(k1_funct_1('#skF_10', D_167), k1_xboole_0) | ~r2_hidden(D_167, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_82, c_409])).
% 9.25/3.25  tff(c_40, plain, (![B_60, A_59]: (~r1_tarski(B_60, A_59) | ~r2_hidden(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.25/3.25  tff(c_420, plain, (![D_167]: (~r1_tarski(k1_xboole_0, k1_funct_1('#skF_10', D_167)) | ~r2_hidden(D_167, k1_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_415, c_40])).
% 9.25/3.25  tff(c_433, plain, (![D_168]: (~r2_hidden(D_168, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_420])).
% 9.25/3.25  tff(c_458, plain, (v1_xboole_0(k1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_4, c_433])).
% 9.25/3.25  tff(c_462, plain, (k1_relat_1('#skF_10')=k1_xboole_0), inference(resolution, [status(thm)], [c_458, c_12])).
% 9.25/3.25  tff(c_465, plain, (k1_relset_1('#skF_8', '#skF_9', '#skF_10')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_462, c_294])).
% 9.25/3.25  tff(c_962, plain, (![B_220, A_221, C_222]: (k1_xboole_0=B_220 | k1_relset_1(A_221, B_220, C_222)=A_221 | ~v1_funct_2(C_222, A_221, B_220) | ~m1_subset_1(C_222, k1_zfmisc_1(k2_zfmisc_1(A_221, B_220))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.25/3.25  tff(c_965, plain, (k1_xboole_0='#skF_9' | k1_relset_1('#skF_8', '#skF_9', '#skF_10')='#skF_8' | ~v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_78, c_962])).
% 9.25/3.25  tff(c_971, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_465, c_965])).
% 9.25/3.25  tff(c_972, plain, (k1_xboole_0='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_68, c_971])).
% 9.25/3.25  tff(c_94, plain, (![B_112, A_113]: (~r1_tarski(B_112, A_113) | ~r2_hidden(A_113, B_112))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.25/3.25  tff(c_99, plain, (![A_114]: (~r1_tarski(A_114, '#skF_1'(A_114)) | v1_xboole_0(A_114))), inference(resolution, [status(thm)], [c_4, c_94])).
% 9.25/3.25  tff(c_104, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_99])).
% 9.25/3.25  tff(c_991, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_972, c_104])).
% 9.25/3.25  tff(c_996, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_991])).
% 9.25/3.25  tff(c_998, plain, (~v1_xboole_0(k2_relat_1('#skF_10'))), inference(splitRight, [status(thm)], [c_346])).
% 9.25/3.25  tff(c_1529, plain, (~v1_xboole_0(k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_1520, c_998])).
% 9.25/3.25  tff(c_1539, plain, (~v1_xboole_0(k1_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_82, c_1529])).
% 9.25/3.25  tff(c_1745, plain, (~v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1744, c_1539])).
% 9.25/3.25  tff(c_209, plain, (![C_137, B_138, A_139]: (v5_relat_1(C_137, B_138) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_139, B_138))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.25/3.25  tff(c_217, plain, (v5_relat_1('#skF_11', '#skF_7')), inference(resolution, [status(thm)], [c_74, c_209])).
% 9.25/3.25  tff(c_138, plain, (v1_relat_1('#skF_11') | ~v1_relat_1(k2_zfmisc_1('#skF_9', '#skF_7'))), inference(resolution, [status(thm)], [c_74, c_132])).
% 9.25/3.25  tff(c_144, plain, (v1_relat_1('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_138])).
% 9.25/3.25  tff(c_22, plain, (![A_19, D_58]: (r2_hidden(k1_funct_1(A_19, D_58), k2_relat_1(A_19)) | ~r2_hidden(D_58, k1_relat_1(A_19)) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.25/3.25  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.25/3.25  tff(c_125, plain, (![A_119, B_120]: (~r2_hidden('#skF_2'(A_119, B_120), B_120) | r1_tarski(A_119, B_120))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.25/3.25  tff(c_130, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_10, c_125])).
% 9.25/3.25  tff(c_26, plain, (![A_19, C_55]: (r2_hidden('#skF_6'(A_19, k2_relat_1(A_19), C_55), k1_relat_1(A_19)) | ~r2_hidden(C_55, k2_relat_1(A_19)) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.25/3.25  tff(c_1756, plain, (![C_55]: (r2_hidden('#skF_6'('#skF_10', k2_relat_1('#skF_10'), C_55), '#skF_8') | ~r2_hidden(C_55, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_1744, c_26])).
% 9.25/3.25  tff(c_1843, plain, (![C_311]: (r2_hidden('#skF_6'('#skF_10', k2_relat_1('#skF_10'), C_311), '#skF_8') | ~r2_hidden(C_311, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_82, c_1756])).
% 9.25/3.25  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.25/3.25  tff(c_1852, plain, (![C_311, B_6]: (r2_hidden('#skF_6'('#skF_10', k2_relat_1('#skF_10'), C_311), B_6) | ~r1_tarski('#skF_8', B_6) | ~r2_hidden(C_311, k2_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_1843, c_6])).
% 9.25/3.25  tff(c_24, plain, (![A_19, C_55]: (k1_funct_1(A_19, '#skF_6'(A_19, k2_relat_1(A_19), C_55))=C_55 | ~r2_hidden(C_55, k2_relat_1(A_19)) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.25/3.25  tff(c_1041, plain, (![A_228, D_229]: (r2_hidden(k1_funct_1(A_228, D_229), k2_relat_1(A_228)) | ~r2_hidden(D_229, k1_relat_1(A_228)) | ~v1_funct_1(A_228) | ~v1_relat_1(A_228))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.25/3.25  tff(c_2907, plain, (![A_406, D_407, B_408]: (r2_hidden(k1_funct_1(A_406, D_407), B_408) | ~r1_tarski(k2_relat_1(A_406), B_408) | ~r2_hidden(D_407, k1_relat_1(A_406)) | ~v1_funct_1(A_406) | ~v1_relat_1(A_406))), inference(resolution, [status(thm)], [c_1041, c_6])).
% 9.25/3.25  tff(c_6776, plain, (![A_703, D_704, B_705, B_706]: (r2_hidden(k1_funct_1(A_703, D_704), B_705) | ~r1_tarski(B_706, B_705) | ~r1_tarski(k2_relat_1(A_703), B_706) | ~r2_hidden(D_704, k1_relat_1(A_703)) | ~v1_funct_1(A_703) | ~v1_relat_1(A_703))), inference(resolution, [status(thm)], [c_2907, c_6])).
% 9.25/3.25  tff(c_6798, plain, (![A_707, D_708]: (r2_hidden(k1_funct_1(A_707, D_708), k1_relat_1('#skF_11')) | ~r1_tarski(k2_relat_1(A_707), k2_relat_1('#skF_10')) | ~r2_hidden(D_708, k1_relat_1(A_707)) | ~v1_funct_1(A_707) | ~v1_relat_1(A_707))), inference(resolution, [status(thm)], [c_319, c_6776])).
% 9.25/3.25  tff(c_7734, plain, (![C_747, A_748]: (r2_hidden(C_747, k1_relat_1('#skF_11')) | ~r1_tarski(k2_relat_1(A_748), k2_relat_1('#skF_10')) | ~r2_hidden('#skF_6'(A_748, k2_relat_1(A_748), C_747), k1_relat_1(A_748)) | ~v1_funct_1(A_748) | ~v1_relat_1(A_748) | ~r2_hidden(C_747, k2_relat_1(A_748)) | ~v1_funct_1(A_748) | ~v1_relat_1(A_748))), inference(superposition, [status(thm), theory('equality')], [c_24, c_6798])).
% 9.25/3.25  tff(c_7742, plain, (![C_311]: (r2_hidden(C_311, k1_relat_1('#skF_11')) | ~r1_tarski(k2_relat_1('#skF_10'), k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r1_tarski('#skF_8', k1_relat_1('#skF_10')) | ~r2_hidden(C_311, k2_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_1852, c_7734])).
% 9.25/3.25  tff(c_7769, plain, (![C_749]: (r2_hidden(C_749, k1_relat_1('#skF_11')) | ~r2_hidden(C_749, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_1744, c_141, c_82, c_130, c_7742])).
% 9.25/3.25  tff(c_7915, plain, (![D_58]: (r2_hidden(k1_funct_1('#skF_10', D_58), k1_relat_1('#skF_11')) | ~r2_hidden(D_58, k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_22, c_7769])).
% 9.25/3.25  tff(c_8023, plain, (![D_750]: (r2_hidden(k1_funct_1('#skF_10', D_750), k1_relat_1('#skF_11')) | ~r2_hidden(D_750, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_82, c_1744, c_7915])).
% 9.25/3.25  tff(c_62, plain, (![A_73, B_74, C_76]: (k7_partfun1(A_73, B_74, C_76)=k1_funct_1(B_74, C_76) | ~r2_hidden(C_76, k1_relat_1(B_74)) | ~v1_funct_1(B_74) | ~v5_relat_1(B_74, A_73) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_122])).
% 9.25/3.25  tff(c_8031, plain, (![A_73, D_750]: (k7_partfun1(A_73, '#skF_11', k1_funct_1('#skF_10', D_750))=k1_funct_1('#skF_11', k1_funct_1('#skF_10', D_750)) | ~v1_funct_1('#skF_11') | ~v5_relat_1('#skF_11', A_73) | ~v1_relat_1('#skF_11') | ~r2_hidden(D_750, '#skF_8'))), inference(resolution, [status(thm)], [c_8023, c_62])).
% 9.25/3.25  tff(c_9085, plain, (![A_780, D_781]: (k7_partfun1(A_780, '#skF_11', k1_funct_1('#skF_10', D_781))=k1_funct_1('#skF_11', k1_funct_1('#skF_10', D_781)) | ~v5_relat_1('#skF_11', A_780) | ~r2_hidden(D_781, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_76, c_8031])).
% 9.25/3.25  tff(c_66, plain, (k7_partfun1('#skF_7', '#skF_11', k1_funct_1('#skF_10', '#skF_12'))!=k1_funct_1(k8_funct_2('#skF_8', '#skF_9', '#skF_7', '#skF_10', '#skF_11'), '#skF_12')), inference(cnfTransformation, [status(thm)], [f_171])).
% 9.25/3.25  tff(c_9091, plain, (k1_funct_1(k8_funct_2('#skF_8', '#skF_9', '#skF_7', '#skF_10', '#skF_11'), '#skF_12')!=k1_funct_1('#skF_11', k1_funct_1('#skF_10', '#skF_12')) | ~v5_relat_1('#skF_11', '#skF_7') | ~r2_hidden('#skF_12', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_9085, c_66])).
% 9.25/3.25  tff(c_9115, plain, (k1_funct_1(k8_funct_2('#skF_8', '#skF_9', '#skF_7', '#skF_10', '#skF_11'), '#skF_12')!=k1_funct_1('#skF_11', k1_funct_1('#skF_10', '#skF_12')) | ~r2_hidden('#skF_12', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_217, c_9091])).
% 9.25/3.25  tff(c_9171, plain, (~r2_hidden('#skF_12', '#skF_8')), inference(splitLeft, [status(thm)], [c_9115])).
% 9.25/3.25  tff(c_9174, plain, (v1_xboole_0('#skF_8') | ~m1_subset_1('#skF_12', '#skF_8')), inference(resolution, [status(thm)], [c_16, c_9171])).
% 9.25/3.25  tff(c_9177, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_9174])).
% 9.25/3.25  tff(c_9179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1745, c_9177])).
% 9.25/3.25  tff(c_9180, plain, (k1_funct_1(k8_funct_2('#skF_8', '#skF_9', '#skF_7', '#skF_10', '#skF_11'), '#skF_12')!=k1_funct_1('#skF_11', k1_funct_1('#skF_10', '#skF_12'))), inference(splitRight, [status(thm)], [c_9115])).
% 9.25/3.25  tff(c_9198, plain, (~m1_subset_1('#skF_12', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_2758, c_9180])).
% 9.25/3.25  tff(c_9202, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_9198])).
% 9.25/3.25  tff(c_9203, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_1741])).
% 9.25/3.25  tff(c_9215, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_9203, c_104])).
% 9.25/3.25  tff(c_9220, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_9215])).
% 9.25/3.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.25/3.25  
% 9.25/3.25  Inference rules
% 9.25/3.25  ----------------------
% 9.25/3.25  #Ref     : 2
% 9.25/3.25  #Sup     : 1987
% 9.25/3.25  #Fact    : 0
% 9.25/3.25  #Define  : 0
% 9.25/3.25  #Split   : 23
% 9.25/3.25  #Chain   : 0
% 9.25/3.25  #Close   : 0
% 9.25/3.25  
% 9.25/3.25  Ordering : KBO
% 9.25/3.25  
% 9.25/3.25  Simplification rules
% 9.25/3.25  ----------------------
% 9.25/3.25  #Subsume      : 1040
% 9.25/3.25  #Demod        : 859
% 9.25/3.25  #Tautology    : 175
% 9.25/3.25  #SimpNegUnit  : 74
% 9.25/3.25  #BackRed      : 72
% 9.25/3.25  
% 9.25/3.25  #Partial instantiations: 0
% 9.25/3.25  #Strategies tried      : 1
% 9.25/3.25  
% 9.25/3.25  Timing (in seconds)
% 9.25/3.25  ----------------------
% 9.25/3.25  Preprocessing        : 0.39
% 9.25/3.25  Parsing              : 0.20
% 9.25/3.25  CNF conversion       : 0.04
% 9.25/3.25  Main loop            : 2.01
% 9.25/3.25  Inferencing          : 0.60
% 9.25/3.25  Reduction            : 0.55
% 9.25/3.25  Demodulation         : 0.37
% 9.25/3.25  BG Simplification    : 0.06
% 9.25/3.25  Subsumption          : 0.65
% 9.25/3.25  Abstraction          : 0.08
% 9.25/3.25  MUC search           : 0.00
% 9.25/3.25  Cooper               : 0.00
% 9.25/3.25  Total                : 2.45
% 9.25/3.25  Index Insertion      : 0.00
% 9.25/3.25  Index Deletion       : 0.00
% 9.25/3.25  Index Matching       : 0.00
% 9.25/3.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
