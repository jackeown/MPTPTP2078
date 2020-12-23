%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:49 EST 2020

% Result     : Theorem 14.65s
% Output     : CNFRefutation 14.88s
% Verified   : 
% Statistics : Number of formulae       :  173 (1001 expanded)
%              Number of leaves         :   54 ( 372 expanded)
%              Depth                    :   23
%              Number of atoms          :  364 (3523 expanded)
%              Number of equality atoms :   63 ( 832 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_15 > #skF_1 > #skF_4 > #skF_16 > #skF_14 > #skF_13 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_7 > #skF_9 > #skF_12 > #skF_10

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

tff('#skF_15',type,(
    '#skF_15': $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_16',type,(
    '#skF_16': $i )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_179,negated_conjecture,(
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

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_154,axiom,(
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

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_119,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_78,axiom,(
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

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_46,axiom,(
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

tff(f_63,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(E,k1_relat_1(A))
                  & r2_hidden(E,B)
                  & D = k1_funct_1(A,E) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_130,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(c_104,plain,(
    ~ v1_xboole_0('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_92,plain,(
    m1_subset_1('#skF_16','#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_96,plain,(
    v1_funct_1('#skF_15') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_94,plain,(
    m1_subset_1('#skF_15',k1_zfmisc_1(k2_zfmisc_1('#skF_13','#skF_11'))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_98,plain,(
    m1_subset_1('#skF_14',k1_zfmisc_1(k2_zfmisc_1('#skF_12','#skF_13'))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_298,plain,(
    ! [A_186,B_187,C_188] :
      ( k2_relset_1(A_186,B_187,C_188) = k2_relat_1(C_188)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1(A_186,B_187))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_305,plain,(
    k2_relset_1('#skF_12','#skF_13','#skF_14') = k2_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_98,c_298])).

tff(c_239,plain,(
    ! [A_179,B_180,C_181] :
      ( k1_relset_1(A_179,B_180,C_181) = k1_relat_1(C_181)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_247,plain,(
    k1_relset_1('#skF_13','#skF_11','#skF_15') = k1_relat_1('#skF_15') ),
    inference(resolution,[status(thm)],[c_94,c_239])).

tff(c_90,plain,(
    r1_tarski(k2_relset_1('#skF_12','#skF_13','#skF_14'),k1_relset_1('#skF_13','#skF_11','#skF_15')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_252,plain,(
    r1_tarski(k2_relset_1('#skF_12','#skF_13','#skF_14'),k1_relat_1('#skF_15')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_90])).

tff(c_326,plain,(
    r1_tarski(k2_relat_1('#skF_14'),k1_relat_1('#skF_15')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_252])).

tff(c_88,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_102,plain,(
    v1_funct_1('#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_100,plain,(
    v1_funct_2('#skF_14','#skF_12','#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_8105,plain,(
    ! [D_678,A_679,E_677,F_676,B_674,C_675] :
      ( k1_funct_1(k8_funct_2(B_674,C_675,A_679,D_678,E_677),F_676) = k1_funct_1(E_677,k1_funct_1(D_678,F_676))
      | k1_xboole_0 = B_674
      | ~ r1_tarski(k2_relset_1(B_674,C_675,D_678),k1_relset_1(C_675,A_679,E_677))
      | ~ m1_subset_1(F_676,B_674)
      | ~ m1_subset_1(E_677,k1_zfmisc_1(k2_zfmisc_1(C_675,A_679)))
      | ~ v1_funct_1(E_677)
      | ~ m1_subset_1(D_678,k1_zfmisc_1(k2_zfmisc_1(B_674,C_675)))
      | ~ v1_funct_2(D_678,B_674,C_675)
      | ~ v1_funct_1(D_678)
      | v1_xboole_0(C_675) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_8111,plain,(
    ! [A_679,E_677,F_676] :
      ( k1_funct_1(k8_funct_2('#skF_12','#skF_13',A_679,'#skF_14',E_677),F_676) = k1_funct_1(E_677,k1_funct_1('#skF_14',F_676))
      | k1_xboole_0 = '#skF_12'
      | ~ r1_tarski(k2_relat_1('#skF_14'),k1_relset_1('#skF_13',A_679,E_677))
      | ~ m1_subset_1(F_676,'#skF_12')
      | ~ m1_subset_1(E_677,k1_zfmisc_1(k2_zfmisc_1('#skF_13',A_679)))
      | ~ v1_funct_1(E_677)
      | ~ m1_subset_1('#skF_14',k1_zfmisc_1(k2_zfmisc_1('#skF_12','#skF_13')))
      | ~ v1_funct_2('#skF_14','#skF_12','#skF_13')
      | ~ v1_funct_1('#skF_14')
      | v1_xboole_0('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_8105])).

tff(c_8123,plain,(
    ! [A_679,E_677,F_676] :
      ( k1_funct_1(k8_funct_2('#skF_12','#skF_13',A_679,'#skF_14',E_677),F_676) = k1_funct_1(E_677,k1_funct_1('#skF_14',F_676))
      | k1_xboole_0 = '#skF_12'
      | ~ r1_tarski(k2_relat_1('#skF_14'),k1_relset_1('#skF_13',A_679,E_677))
      | ~ m1_subset_1(F_676,'#skF_12')
      | ~ m1_subset_1(E_677,k1_zfmisc_1(k2_zfmisc_1('#skF_13',A_679)))
      | ~ v1_funct_1(E_677)
      | v1_xboole_0('#skF_13') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_98,c_8111])).

tff(c_8199,plain,(
    ! [A_685,E_686,F_687] :
      ( k1_funct_1(k8_funct_2('#skF_12','#skF_13',A_685,'#skF_14',E_686),F_687) = k1_funct_1(E_686,k1_funct_1('#skF_14',F_687))
      | ~ r1_tarski(k2_relat_1('#skF_14'),k1_relset_1('#skF_13',A_685,E_686))
      | ~ m1_subset_1(F_687,'#skF_12')
      | ~ m1_subset_1(E_686,k1_zfmisc_1(k2_zfmisc_1('#skF_13',A_685)))
      | ~ v1_funct_1(E_686) ) ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_88,c_8123])).

tff(c_8204,plain,(
    ! [F_687] :
      ( k1_funct_1(k8_funct_2('#skF_12','#skF_13','#skF_11','#skF_14','#skF_15'),F_687) = k1_funct_1('#skF_15',k1_funct_1('#skF_14',F_687))
      | ~ r1_tarski(k2_relat_1('#skF_14'),k1_relat_1('#skF_15'))
      | ~ m1_subset_1(F_687,'#skF_12')
      | ~ m1_subset_1('#skF_15',k1_zfmisc_1(k2_zfmisc_1('#skF_13','#skF_11')))
      | ~ v1_funct_1('#skF_15') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_8199])).

tff(c_8212,plain,(
    ! [F_687] :
      ( k1_funct_1(k8_funct_2('#skF_12','#skF_13','#skF_11','#skF_14','#skF_15'),F_687) = k1_funct_1('#skF_15',k1_funct_1('#skF_14',F_687))
      | ~ m1_subset_1(F_687,'#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_326,c_8204])).

tff(c_209,plain,(
    ! [C_171,B_172,A_173] :
      ( v5_relat_1(C_171,B_172)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_173,B_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_217,plain,(
    v5_relat_1('#skF_15','#skF_11') ),
    inference(resolution,[status(thm)],[c_94,c_209])).

tff(c_138,plain,(
    ! [C_155,A_156,B_157] :
      ( v1_relat_1(C_155)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_146,plain,(
    v1_relat_1('#skF_15') ),
    inference(resolution,[status(thm)],[c_94,c_138])).

tff(c_246,plain,(
    k1_relset_1('#skF_12','#skF_13','#skF_14') = k1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_98,c_239])).

tff(c_2869,plain,(
    ! [B_390,A_391,C_392] :
      ( k1_xboole_0 = B_390
      | k1_relset_1(A_391,B_390,C_392) = A_391
      | ~ v1_funct_2(C_392,A_391,B_390)
      | ~ m1_subset_1(C_392,k1_zfmisc_1(k2_zfmisc_1(A_391,B_390))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2872,plain,
    ( k1_xboole_0 = '#skF_13'
    | k1_relset_1('#skF_12','#skF_13','#skF_14') = '#skF_12'
    | ~ v1_funct_2('#skF_14','#skF_12','#skF_13') ),
    inference(resolution,[status(thm)],[c_98,c_2869])).

tff(c_2878,plain,
    ( k1_xboole_0 = '#skF_13'
    | k1_relat_1('#skF_14') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_246,c_2872])).

tff(c_2882,plain,(
    k1_relat_1('#skF_14') = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_2878])).

tff(c_145,plain,(
    v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_98,c_138])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2558,plain,(
    ! [A_361,C_362] :
      ( r2_hidden('#skF_10'(A_361,k2_relat_1(A_361),C_362),k1_relat_1(A_361))
      | ~ r2_hidden(C_362,k2_relat_1(A_361))
      | ~ v1_funct_1(A_361)
      | ~ v1_relat_1(A_361) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2584,plain,(
    ! [A_363,C_364] :
      ( ~ v1_xboole_0(k1_relat_1(A_363))
      | ~ r2_hidden(C_364,k2_relat_1(A_363))
      | ~ v1_funct_1(A_363)
      | ~ v1_relat_1(A_363) ) ),
    inference(resolution,[status(thm)],[c_2558,c_2])).

tff(c_2619,plain,(
    ! [A_365] :
      ( ~ v1_xboole_0(k1_relat_1(A_365))
      | ~ v1_funct_1(A_365)
      | ~ v1_relat_1(A_365)
      | v1_xboole_0(k2_relat_1(A_365)) ) ),
    inference(resolution,[status(thm)],[c_4,c_2584])).

tff(c_12,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_108,plain,(
    ! [A_149] :
      ( v1_xboole_0(A_149)
      | r2_hidden('#skF_1'(A_149),A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,(
    ! [B_96,A_95] :
      ( ~ r1_tarski(B_96,A_95)
      | ~ r2_hidden(A_95,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_117,plain,(
    ! [A_150] :
      ( ~ r1_tarski(A_150,'#skF_1'(A_150))
      | v1_xboole_0(A_150) ) ),
    inference(resolution,[status(thm)],[c_108,c_58])).

tff(c_122,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_117])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( r2_hidden(A_11,B_12)
      | v1_xboole_0(B_12)
      | ~ m1_subset_1(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_198,plain,(
    ! [C_167,B_168,A_169] :
      ( r2_hidden(C_167,B_168)
      | ~ r2_hidden(C_167,A_169)
      | ~ r1_tarski(A_169,B_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_376,plain,(
    ! [A_199,B_200,B_201] :
      ( r2_hidden(A_199,B_200)
      | ~ r1_tarski(B_201,B_200)
      | v1_xboole_0(B_201)
      | ~ m1_subset_1(A_199,B_201) ) ),
    inference(resolution,[status(thm)],[c_14,c_198])).

tff(c_385,plain,(
    ! [A_199] :
      ( r2_hidden(A_199,k1_relat_1('#skF_15'))
      | v1_xboole_0(k2_relat_1('#skF_14'))
      | ~ m1_subset_1(A_199,k2_relat_1('#skF_14')) ) ),
    inference(resolution,[status(thm)],[c_326,c_376])).

tff(c_422,plain,(
    v1_xboole_0(k2_relat_1('#skF_14')) ),
    inference(splitLeft,[status(thm)],[c_385])).

tff(c_1063,plain,(
    ! [B_278,A_279,C_280] :
      ( k1_xboole_0 = B_278
      | k1_relset_1(A_279,B_278,C_280) = A_279
      | ~ v1_funct_2(C_280,A_279,B_278)
      | ~ m1_subset_1(C_280,k1_zfmisc_1(k2_zfmisc_1(A_279,B_278))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1066,plain,
    ( k1_xboole_0 = '#skF_13'
    | k1_relset_1('#skF_12','#skF_13','#skF_14') = '#skF_12'
    | ~ v1_funct_2('#skF_14','#skF_12','#skF_13') ),
    inference(resolution,[status(thm)],[c_98,c_1063])).

tff(c_1072,plain,
    ( k1_xboole_0 = '#skF_13'
    | k1_relat_1('#skF_14') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_246,c_1066])).

tff(c_1076,plain,(
    k1_relat_1('#skF_14') = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_1072])).

tff(c_454,plain,(
    ! [A_214,D_215] :
      ( r2_hidden(k1_funct_1(A_214,D_215),k2_relat_1(A_214))
      | ~ r2_hidden(D_215,k1_relat_1(A_214))
      | ~ v1_funct_1(A_214)
      | ~ v1_relat_1(A_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_465,plain,(
    ! [A_214,D_215] :
      ( ~ v1_xboole_0(k2_relat_1(A_214))
      | ~ r2_hidden(D_215,k1_relat_1(A_214))
      | ~ v1_funct_1(A_214)
      | ~ v1_relat_1(A_214) ) ),
    inference(resolution,[status(thm)],[c_454,c_2])).

tff(c_1096,plain,(
    ! [D_215] :
      ( ~ v1_xboole_0(k2_relat_1('#skF_14'))
      | ~ r2_hidden(D_215,'#skF_12')
      | ~ v1_funct_1('#skF_14')
      | ~ v1_relat_1('#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1076,c_465])).

tff(c_1110,plain,(
    ! [D_215] : ~ r2_hidden(D_215,'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_102,c_422,c_1096])).

tff(c_1956,plain,(
    ! [A_313,B_314] :
      ( r2_hidden('#skF_8'(A_313,B_314),k1_relat_1(A_313))
      | r2_hidden('#skF_9'(A_313,B_314),B_314)
      | k2_relat_1(A_313) = B_314
      | ~ v1_funct_1(A_313)
      | ~ v1_relat_1(A_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2003,plain,(
    ! [B_314] :
      ( r2_hidden('#skF_8'('#skF_14',B_314),'#skF_12')
      | r2_hidden('#skF_9'('#skF_14',B_314),B_314)
      | k2_relat_1('#skF_14') = B_314
      | ~ v1_funct_1('#skF_14')
      | ~ v1_relat_1('#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1076,c_1956])).

tff(c_2018,plain,(
    ! [B_314] :
      ( r2_hidden('#skF_8'('#skF_14',B_314),'#skF_12')
      | r2_hidden('#skF_9'('#skF_14',B_314),B_314)
      | k2_relat_1('#skF_14') = B_314 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_102,c_2003])).

tff(c_2020,plain,(
    ! [B_315] :
      ( r2_hidden('#skF_9'('#skF_14',B_315),B_315)
      | k2_relat_1('#skF_14') = B_315 ) ),
    inference(negUnitSimplification,[status(thm)],[c_1110,c_2018])).

tff(c_2061,plain,(
    k2_relat_1('#skF_14') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_2020,c_1110])).

tff(c_2066,plain,(
    ! [B_315] :
      ( ~ v1_xboole_0(B_315)
      | k2_relat_1('#skF_14') = B_315 ) ),
    inference(resolution,[status(thm)],[c_2020,c_2])).

tff(c_2142,plain,(
    ! [B_316] :
      ( ~ v1_xboole_0(B_316)
      | B_316 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2061,c_2066])).

tff(c_2157,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_122,c_2142])).

tff(c_2166,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_2157])).

tff(c_2167,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_1072])).

tff(c_2178,plain,(
    v1_xboole_0('#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2167,c_122])).

tff(c_2182,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_2178])).

tff(c_2184,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_14')) ),
    inference(splitRight,[status(thm)],[c_385])).

tff(c_2628,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_14'))
    | ~ v1_funct_1('#skF_14')
    | ~ v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_2619,c_2184])).

tff(c_2635,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_14')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_102,c_2628])).

tff(c_2883,plain,(
    ~ v1_xboole_0('#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2882,c_2635])).

tff(c_16,plain,(
    ! [A_13,E_54,B_36] :
      ( r2_hidden(k1_funct_1(A_13,E_54),k9_relat_1(A_13,B_36))
      | ~ r2_hidden(E_54,B_36)
      | ~ r2_hidden(E_54,k1_relat_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_147,plain,(
    ! [A_158,B_159] :
      ( r2_hidden('#skF_2'(A_158,B_159),A_158)
      | r1_tarski(A_158,B_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_158,plain,(
    ! [A_158] : r1_tarski(A_158,A_158) ),
    inference(resolution,[status(thm)],[c_147,c_8])).

tff(c_3958,plain,(
    ! [A_460,B_461,D_462] :
      ( r2_hidden('#skF_6'(A_460,B_461,k9_relat_1(A_460,B_461),D_462),k1_relat_1(A_460))
      | ~ r2_hidden(D_462,k9_relat_1(A_460,B_461))
      | ~ v1_funct_1(A_460)
      | ~ v1_relat_1(A_460) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3974,plain,(
    ! [B_461,D_462] :
      ( r2_hidden('#skF_6'('#skF_14',B_461,k9_relat_1('#skF_14',B_461),D_462),'#skF_12')
      | ~ r2_hidden(D_462,k9_relat_1('#skF_14',B_461))
      | ~ v1_funct_1('#skF_14')
      | ~ v1_relat_1('#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2882,c_3958])).

tff(c_4054,plain,(
    ! [B_465,D_466] :
      ( r2_hidden('#skF_6'('#skF_14',B_465,k9_relat_1('#skF_14',B_465),D_466),'#skF_12')
      | ~ r2_hidden(D_466,k9_relat_1('#skF_14',B_465)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_102,c_3974])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4066,plain,(
    ! [B_465,D_466,B_6] :
      ( r2_hidden('#skF_6'('#skF_14',B_465,k9_relat_1('#skF_14',B_465),D_466),B_6)
      | ~ r1_tarski('#skF_12',B_6)
      | ~ r2_hidden(D_466,k9_relat_1('#skF_14',B_465)) ) ),
    inference(resolution,[status(thm)],[c_4054,c_6])).

tff(c_4165,plain,(
    ! [A_474,B_475,D_476] :
      ( k1_funct_1(A_474,'#skF_6'(A_474,B_475,k9_relat_1(A_474,B_475),D_476)) = D_476
      | ~ r2_hidden(D_476,k9_relat_1(A_474,B_475))
      | ~ v1_funct_1(A_474)
      | ~ v1_relat_1(A_474) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_40,plain,(
    ! [A_55,D_94] :
      ( r2_hidden(k1_funct_1(A_55,D_94),k2_relat_1(A_55))
      | ~ r2_hidden(D_94,k1_relat_1(A_55))
      | ~ v1_funct_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_22503,plain,(
    ! [D_1196,A_1197,B_1198] :
      ( r2_hidden(D_1196,k2_relat_1(A_1197))
      | ~ r2_hidden('#skF_6'(A_1197,B_1198,k9_relat_1(A_1197,B_1198),D_1196),k1_relat_1(A_1197))
      | ~ v1_funct_1(A_1197)
      | ~ v1_relat_1(A_1197)
      | ~ r2_hidden(D_1196,k9_relat_1(A_1197,B_1198))
      | ~ v1_funct_1(A_1197)
      | ~ v1_relat_1(A_1197) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4165,c_40])).

tff(c_22518,plain,(
    ! [D_466,B_465] :
      ( r2_hidden(D_466,k2_relat_1('#skF_14'))
      | ~ v1_funct_1('#skF_14')
      | ~ v1_relat_1('#skF_14')
      | ~ r1_tarski('#skF_12',k1_relat_1('#skF_14'))
      | ~ r2_hidden(D_466,k9_relat_1('#skF_14',B_465)) ) ),
    inference(resolution,[status(thm)],[c_4066,c_22503])).

tff(c_22567,plain,(
    ! [D_1199,B_1200] :
      ( r2_hidden(D_1199,k2_relat_1('#skF_14'))
      | ~ r2_hidden(D_1199,k9_relat_1('#skF_14',B_1200)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_2882,c_145,c_102,c_22518])).

tff(c_22805,plain,(
    ! [E_54,B_36] :
      ( r2_hidden(k1_funct_1('#skF_14',E_54),k2_relat_1('#skF_14'))
      | ~ r2_hidden(E_54,B_36)
      | ~ r2_hidden(E_54,k1_relat_1('#skF_14'))
      | ~ v1_funct_1('#skF_14')
      | ~ v1_relat_1('#skF_14') ) ),
    inference(resolution,[status(thm)],[c_16,c_22567])).

tff(c_23119,plain,(
    ! [E_1206,B_1207] :
      ( r2_hidden(k1_funct_1('#skF_14',E_1206),k2_relat_1('#skF_14'))
      | ~ r2_hidden(E_1206,B_1207)
      | ~ r2_hidden(E_1206,'#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_102,c_2882,c_22805])).

tff(c_29297,plain,(
    ! [A_1349,B_1350] :
      ( r2_hidden(k1_funct_1('#skF_14',A_1349),k2_relat_1('#skF_14'))
      | ~ r2_hidden(A_1349,'#skF_12')
      | v1_xboole_0(B_1350)
      | ~ m1_subset_1(A_1349,B_1350) ) ),
    inference(resolution,[status(thm)],[c_14,c_23119])).

tff(c_29303,plain,
    ( r2_hidden(k1_funct_1('#skF_14','#skF_16'),k2_relat_1('#skF_14'))
    | ~ r2_hidden('#skF_16','#skF_12')
    | v1_xboole_0('#skF_12') ),
    inference(resolution,[status(thm)],[c_92,c_29297])).

tff(c_29308,plain,
    ( r2_hidden(k1_funct_1('#skF_14','#skF_16'),k2_relat_1('#skF_14'))
    | ~ r2_hidden('#skF_16','#skF_12') ),
    inference(negUnitSimplification,[status(thm)],[c_2883,c_29303])).

tff(c_29309,plain,(
    ~ r2_hidden('#skF_16','#skF_12') ),
    inference(splitLeft,[status(thm)],[c_29308])).

tff(c_29312,plain,
    ( v1_xboole_0('#skF_12')
    | ~ m1_subset_1('#skF_16','#skF_12') ),
    inference(resolution,[status(thm)],[c_14,c_29309])).

tff(c_29315,plain,(
    v1_xboole_0('#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_29312])).

tff(c_29317,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2883,c_29315])).

tff(c_29319,plain,(
    r2_hidden('#skF_16','#skF_12') ),
    inference(splitRight,[status(thm)],[c_29308])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_25561,plain,(
    ! [B_1252,B_1253] :
      ( r2_hidden('#skF_2'(k9_relat_1('#skF_14',B_1252),B_1253),k2_relat_1('#skF_14'))
      | r1_tarski(k9_relat_1('#skF_14',B_1252),B_1253) ) ),
    inference(resolution,[status(thm)],[c_10,c_22567])).

tff(c_25649,plain,(
    ! [B_1257] : r1_tarski(k9_relat_1('#skF_14',B_1257),k2_relat_1('#skF_14')) ),
    inference(resolution,[status(thm)],[c_25561,c_8])).

tff(c_344,plain,(
    ! [A_192,B_193,B_194] :
      ( r2_hidden('#skF_2'(A_192,B_193),B_194)
      | ~ r1_tarski(A_192,B_194)
      | r1_tarski(A_192,B_193) ) ),
    inference(resolution,[status(thm)],[c_10,c_198])).

tff(c_2444,plain,(
    ! [A_347,B_348,B_349,B_350] :
      ( r2_hidden('#skF_2'(A_347,B_348),B_349)
      | ~ r1_tarski(B_350,B_349)
      | ~ r1_tarski(A_347,B_350)
      | r1_tarski(A_347,B_348) ) ),
    inference(resolution,[status(thm)],[c_344,c_6])).

tff(c_2460,plain,(
    ! [A_351,B_352] :
      ( r2_hidden('#skF_2'(A_351,B_352),k1_relat_1('#skF_15'))
      | ~ r1_tarski(A_351,k2_relat_1('#skF_14'))
      | r1_tarski(A_351,B_352) ) ),
    inference(resolution,[status(thm)],[c_326,c_2444])).

tff(c_2480,plain,(
    ! [A_351] :
      ( ~ r1_tarski(A_351,k2_relat_1('#skF_14'))
      | r1_tarski(A_351,k1_relat_1('#skF_15')) ) ),
    inference(resolution,[status(thm)],[c_2460,c_8])).

tff(c_25758,plain,(
    ! [B_1258] : r1_tarski(k9_relat_1('#skF_14',B_1258),k1_relat_1('#skF_15')) ),
    inference(resolution,[status(thm)],[c_25649,c_2480])).

tff(c_2940,plain,(
    ! [A_395,E_396,B_397] :
      ( r2_hidden(k1_funct_1(A_395,E_396),k9_relat_1(A_395,B_397))
      | ~ r2_hidden(E_396,B_397)
      | ~ r2_hidden(E_396,k1_relat_1(A_395))
      | ~ v1_funct_1(A_395)
      | ~ v1_relat_1(A_395) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2952,plain,(
    ! [A_395,E_396,B_6,B_397] :
      ( r2_hidden(k1_funct_1(A_395,E_396),B_6)
      | ~ r1_tarski(k9_relat_1(A_395,B_397),B_6)
      | ~ r2_hidden(E_396,B_397)
      | ~ r2_hidden(E_396,k1_relat_1(A_395))
      | ~ v1_funct_1(A_395)
      | ~ v1_relat_1(A_395) ) ),
    inference(resolution,[status(thm)],[c_2940,c_6])).

tff(c_25776,plain,(
    ! [E_396,B_1258] :
      ( r2_hidden(k1_funct_1('#skF_14',E_396),k1_relat_1('#skF_15'))
      | ~ r2_hidden(E_396,B_1258)
      | ~ r2_hidden(E_396,k1_relat_1('#skF_14'))
      | ~ v1_funct_1('#skF_14')
      | ~ v1_relat_1('#skF_14') ) ),
    inference(resolution,[status(thm)],[c_25758,c_2952])).

tff(c_25836,plain,(
    ! [E_396,B_1258] :
      ( r2_hidden(k1_funct_1('#skF_14',E_396),k1_relat_1('#skF_15'))
      | ~ r2_hidden(E_396,B_1258)
      | ~ r2_hidden(E_396,'#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_102,c_2882,c_25776])).

tff(c_29478,plain,
    ( r2_hidden(k1_funct_1('#skF_14','#skF_16'),k1_relat_1('#skF_15'))
    | ~ r2_hidden('#skF_16','#skF_12') ),
    inference(resolution,[status(thm)],[c_29319,c_25836])).

tff(c_29495,plain,(
    r2_hidden(k1_funct_1('#skF_14','#skF_16'),k1_relat_1('#skF_15')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29319,c_29478])).

tff(c_82,plain,(
    ! [A_112,B_113,C_115] :
      ( k7_partfun1(A_112,B_113,C_115) = k1_funct_1(B_113,C_115)
      | ~ r2_hidden(C_115,k1_relat_1(B_113))
      | ~ v1_funct_1(B_113)
      | ~ v5_relat_1(B_113,A_112)
      | ~ v1_relat_1(B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_29827,plain,(
    ! [A_112] :
      ( k7_partfun1(A_112,'#skF_15',k1_funct_1('#skF_14','#skF_16')) = k1_funct_1('#skF_15',k1_funct_1('#skF_14','#skF_16'))
      | ~ v1_funct_1('#skF_15')
      | ~ v5_relat_1('#skF_15',A_112)
      | ~ v1_relat_1('#skF_15') ) ),
    inference(resolution,[status(thm)],[c_29495,c_82])).

tff(c_32081,plain,(
    ! [A_1423] :
      ( k7_partfun1(A_1423,'#skF_15',k1_funct_1('#skF_14','#skF_16')) = k1_funct_1('#skF_15',k1_funct_1('#skF_14','#skF_16'))
      | ~ v5_relat_1('#skF_15',A_1423) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_96,c_29827])).

tff(c_86,plain,(
    k7_partfun1('#skF_11','#skF_15',k1_funct_1('#skF_14','#skF_16')) != k1_funct_1(k8_funct_2('#skF_12','#skF_13','#skF_11','#skF_14','#skF_15'),'#skF_16') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_32087,plain,
    ( k1_funct_1(k8_funct_2('#skF_12','#skF_13','#skF_11','#skF_14','#skF_15'),'#skF_16') != k1_funct_1('#skF_15',k1_funct_1('#skF_14','#skF_16'))
    | ~ v5_relat_1('#skF_15','#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_32081,c_86])).

tff(c_32093,plain,(
    k1_funct_1(k8_funct_2('#skF_12','#skF_13','#skF_11','#skF_14','#skF_15'),'#skF_16') != k1_funct_1('#skF_15',k1_funct_1('#skF_14','#skF_16')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_32087])).

tff(c_32097,plain,(
    ~ m1_subset_1('#skF_16','#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_8212,c_32093])).

tff(c_32101,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_32097])).

tff(c_32102,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_2878])).

tff(c_32113,plain,(
    v1_xboole_0('#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32102,c_122])).

tff(c_32117,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_32113])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:54:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.65/7.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.65/7.39  
% 14.65/7.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.65/7.39  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_15 > #skF_1 > #skF_4 > #skF_16 > #skF_14 > #skF_13 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_7 > #skF_9 > #skF_12 > #skF_10
% 14.65/7.39  
% 14.65/7.39  %Foreground sorts:
% 14.65/7.39  
% 14.65/7.39  
% 14.65/7.39  %Background operators:
% 14.65/7.39  
% 14.65/7.39  
% 14.65/7.39  %Foreground operators:
% 14.65/7.39  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 14.65/7.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 14.65/7.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.65/7.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.65/7.39  tff('#skF_11', type, '#skF_11': $i).
% 14.65/7.39  tff('#skF_15', type, '#skF_15': $i).
% 14.65/7.39  tff('#skF_1', type, '#skF_1': $i > $i).
% 14.65/7.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.65/7.39  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 14.65/7.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.65/7.39  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 14.65/7.39  tff('#skF_16', type, '#skF_16': $i).
% 14.65/7.39  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 14.65/7.39  tff('#skF_14', type, '#skF_14': $i).
% 14.65/7.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 14.65/7.39  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 14.65/7.39  tff('#skF_13', type, '#skF_13': $i).
% 14.65/7.39  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 14.65/7.39  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 14.65/7.39  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 14.65/7.39  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 14.65/7.39  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 14.65/7.39  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 14.65/7.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.65/7.39  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 14.65/7.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.65/7.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.65/7.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 14.65/7.39  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 14.65/7.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.65/7.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 14.65/7.39  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 14.65/7.39  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 14.65/7.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 14.65/7.39  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 14.65/7.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 14.65/7.39  tff('#skF_12', type, '#skF_12': $i).
% 14.65/7.39  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 14.65/7.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.65/7.39  
% 14.88/7.42  tff(f_179, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 14.88/7.42  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 14.88/7.42  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 14.88/7.42  tff(f_154, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 14.88/7.42  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 14.88/7.42  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 14.88/7.42  tff(f_119, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 14.88/7.42  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 14.88/7.42  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 14.88/7.42  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 14.88/7.42  tff(f_83, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 14.88/7.42  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 14.88/7.42  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 14.88/7.42  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_1)).
% 14.88/7.42  tff(f_130, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 14.88/7.42  tff(c_104, plain, (~v1_xboole_0('#skF_13')), inference(cnfTransformation, [status(thm)], [f_179])).
% 14.88/7.42  tff(c_92, plain, (m1_subset_1('#skF_16', '#skF_12')), inference(cnfTransformation, [status(thm)], [f_179])).
% 14.88/7.42  tff(c_96, plain, (v1_funct_1('#skF_15')), inference(cnfTransformation, [status(thm)], [f_179])).
% 14.88/7.42  tff(c_94, plain, (m1_subset_1('#skF_15', k1_zfmisc_1(k2_zfmisc_1('#skF_13', '#skF_11')))), inference(cnfTransformation, [status(thm)], [f_179])).
% 14.88/7.42  tff(c_98, plain, (m1_subset_1('#skF_14', k1_zfmisc_1(k2_zfmisc_1('#skF_12', '#skF_13')))), inference(cnfTransformation, [status(thm)], [f_179])).
% 14.88/7.42  tff(c_298, plain, (![A_186, B_187, C_188]: (k2_relset_1(A_186, B_187, C_188)=k2_relat_1(C_188) | ~m1_subset_1(C_188, k1_zfmisc_1(k2_zfmisc_1(A_186, B_187))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 14.88/7.42  tff(c_305, plain, (k2_relset_1('#skF_12', '#skF_13', '#skF_14')=k2_relat_1('#skF_14')), inference(resolution, [status(thm)], [c_98, c_298])).
% 14.88/7.42  tff(c_239, plain, (![A_179, B_180, C_181]: (k1_relset_1(A_179, B_180, C_181)=k1_relat_1(C_181) | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 14.88/7.42  tff(c_247, plain, (k1_relset_1('#skF_13', '#skF_11', '#skF_15')=k1_relat_1('#skF_15')), inference(resolution, [status(thm)], [c_94, c_239])).
% 14.88/7.42  tff(c_90, plain, (r1_tarski(k2_relset_1('#skF_12', '#skF_13', '#skF_14'), k1_relset_1('#skF_13', '#skF_11', '#skF_15'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 14.88/7.42  tff(c_252, plain, (r1_tarski(k2_relset_1('#skF_12', '#skF_13', '#skF_14'), k1_relat_1('#skF_15'))), inference(demodulation, [status(thm), theory('equality')], [c_247, c_90])).
% 14.88/7.42  tff(c_326, plain, (r1_tarski(k2_relat_1('#skF_14'), k1_relat_1('#skF_15'))), inference(demodulation, [status(thm), theory('equality')], [c_305, c_252])).
% 14.88/7.42  tff(c_88, plain, (k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_179])).
% 14.88/7.42  tff(c_102, plain, (v1_funct_1('#skF_14')), inference(cnfTransformation, [status(thm)], [f_179])).
% 14.88/7.42  tff(c_100, plain, (v1_funct_2('#skF_14', '#skF_12', '#skF_13')), inference(cnfTransformation, [status(thm)], [f_179])).
% 14.88/7.42  tff(c_8105, plain, (![D_678, A_679, E_677, F_676, B_674, C_675]: (k1_funct_1(k8_funct_2(B_674, C_675, A_679, D_678, E_677), F_676)=k1_funct_1(E_677, k1_funct_1(D_678, F_676)) | k1_xboole_0=B_674 | ~r1_tarski(k2_relset_1(B_674, C_675, D_678), k1_relset_1(C_675, A_679, E_677)) | ~m1_subset_1(F_676, B_674) | ~m1_subset_1(E_677, k1_zfmisc_1(k2_zfmisc_1(C_675, A_679))) | ~v1_funct_1(E_677) | ~m1_subset_1(D_678, k1_zfmisc_1(k2_zfmisc_1(B_674, C_675))) | ~v1_funct_2(D_678, B_674, C_675) | ~v1_funct_1(D_678) | v1_xboole_0(C_675))), inference(cnfTransformation, [status(thm)], [f_154])).
% 14.88/7.42  tff(c_8111, plain, (![A_679, E_677, F_676]: (k1_funct_1(k8_funct_2('#skF_12', '#skF_13', A_679, '#skF_14', E_677), F_676)=k1_funct_1(E_677, k1_funct_1('#skF_14', F_676)) | k1_xboole_0='#skF_12' | ~r1_tarski(k2_relat_1('#skF_14'), k1_relset_1('#skF_13', A_679, E_677)) | ~m1_subset_1(F_676, '#skF_12') | ~m1_subset_1(E_677, k1_zfmisc_1(k2_zfmisc_1('#skF_13', A_679))) | ~v1_funct_1(E_677) | ~m1_subset_1('#skF_14', k1_zfmisc_1(k2_zfmisc_1('#skF_12', '#skF_13'))) | ~v1_funct_2('#skF_14', '#skF_12', '#skF_13') | ~v1_funct_1('#skF_14') | v1_xboole_0('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_305, c_8105])).
% 14.88/7.42  tff(c_8123, plain, (![A_679, E_677, F_676]: (k1_funct_1(k8_funct_2('#skF_12', '#skF_13', A_679, '#skF_14', E_677), F_676)=k1_funct_1(E_677, k1_funct_1('#skF_14', F_676)) | k1_xboole_0='#skF_12' | ~r1_tarski(k2_relat_1('#skF_14'), k1_relset_1('#skF_13', A_679, E_677)) | ~m1_subset_1(F_676, '#skF_12') | ~m1_subset_1(E_677, k1_zfmisc_1(k2_zfmisc_1('#skF_13', A_679))) | ~v1_funct_1(E_677) | v1_xboole_0('#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_98, c_8111])).
% 14.88/7.42  tff(c_8199, plain, (![A_685, E_686, F_687]: (k1_funct_1(k8_funct_2('#skF_12', '#skF_13', A_685, '#skF_14', E_686), F_687)=k1_funct_1(E_686, k1_funct_1('#skF_14', F_687)) | ~r1_tarski(k2_relat_1('#skF_14'), k1_relset_1('#skF_13', A_685, E_686)) | ~m1_subset_1(F_687, '#skF_12') | ~m1_subset_1(E_686, k1_zfmisc_1(k2_zfmisc_1('#skF_13', A_685))) | ~v1_funct_1(E_686))), inference(negUnitSimplification, [status(thm)], [c_104, c_88, c_8123])).
% 14.88/7.42  tff(c_8204, plain, (![F_687]: (k1_funct_1(k8_funct_2('#skF_12', '#skF_13', '#skF_11', '#skF_14', '#skF_15'), F_687)=k1_funct_1('#skF_15', k1_funct_1('#skF_14', F_687)) | ~r1_tarski(k2_relat_1('#skF_14'), k1_relat_1('#skF_15')) | ~m1_subset_1(F_687, '#skF_12') | ~m1_subset_1('#skF_15', k1_zfmisc_1(k2_zfmisc_1('#skF_13', '#skF_11'))) | ~v1_funct_1('#skF_15'))), inference(superposition, [status(thm), theory('equality')], [c_247, c_8199])).
% 14.88/7.42  tff(c_8212, plain, (![F_687]: (k1_funct_1(k8_funct_2('#skF_12', '#skF_13', '#skF_11', '#skF_14', '#skF_15'), F_687)=k1_funct_1('#skF_15', k1_funct_1('#skF_14', F_687)) | ~m1_subset_1(F_687, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_326, c_8204])).
% 14.88/7.42  tff(c_209, plain, (![C_171, B_172, A_173]: (v5_relat_1(C_171, B_172) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_173, B_172))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 14.88/7.42  tff(c_217, plain, (v5_relat_1('#skF_15', '#skF_11')), inference(resolution, [status(thm)], [c_94, c_209])).
% 14.88/7.42  tff(c_138, plain, (![C_155, A_156, B_157]: (v1_relat_1(C_155) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.88/7.42  tff(c_146, plain, (v1_relat_1('#skF_15')), inference(resolution, [status(thm)], [c_94, c_138])).
% 14.88/7.42  tff(c_246, plain, (k1_relset_1('#skF_12', '#skF_13', '#skF_14')=k1_relat_1('#skF_14')), inference(resolution, [status(thm)], [c_98, c_239])).
% 14.88/7.42  tff(c_2869, plain, (![B_390, A_391, C_392]: (k1_xboole_0=B_390 | k1_relset_1(A_391, B_390, C_392)=A_391 | ~v1_funct_2(C_392, A_391, B_390) | ~m1_subset_1(C_392, k1_zfmisc_1(k2_zfmisc_1(A_391, B_390))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 14.88/7.42  tff(c_2872, plain, (k1_xboole_0='#skF_13' | k1_relset_1('#skF_12', '#skF_13', '#skF_14')='#skF_12' | ~v1_funct_2('#skF_14', '#skF_12', '#skF_13')), inference(resolution, [status(thm)], [c_98, c_2869])).
% 14.88/7.42  tff(c_2878, plain, (k1_xboole_0='#skF_13' | k1_relat_1('#skF_14')='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_246, c_2872])).
% 14.88/7.42  tff(c_2882, plain, (k1_relat_1('#skF_14')='#skF_12'), inference(splitLeft, [status(thm)], [c_2878])).
% 14.88/7.42  tff(c_145, plain, (v1_relat_1('#skF_14')), inference(resolution, [status(thm)], [c_98, c_138])).
% 14.88/7.42  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.88/7.42  tff(c_2558, plain, (![A_361, C_362]: (r2_hidden('#skF_10'(A_361, k2_relat_1(A_361), C_362), k1_relat_1(A_361)) | ~r2_hidden(C_362, k2_relat_1(A_361)) | ~v1_funct_1(A_361) | ~v1_relat_1(A_361))), inference(cnfTransformation, [status(thm)], [f_78])).
% 14.88/7.42  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.88/7.42  tff(c_2584, plain, (![A_363, C_364]: (~v1_xboole_0(k1_relat_1(A_363)) | ~r2_hidden(C_364, k2_relat_1(A_363)) | ~v1_funct_1(A_363) | ~v1_relat_1(A_363))), inference(resolution, [status(thm)], [c_2558, c_2])).
% 14.88/7.42  tff(c_2619, plain, (![A_365]: (~v1_xboole_0(k1_relat_1(A_365)) | ~v1_funct_1(A_365) | ~v1_relat_1(A_365) | v1_xboole_0(k2_relat_1(A_365)))), inference(resolution, [status(thm)], [c_4, c_2584])).
% 14.88/7.42  tff(c_12, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 14.88/7.42  tff(c_108, plain, (![A_149]: (v1_xboole_0(A_149) | r2_hidden('#skF_1'(A_149), A_149))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.88/7.42  tff(c_58, plain, (![B_96, A_95]: (~r1_tarski(B_96, A_95) | ~r2_hidden(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_83])).
% 14.88/7.42  tff(c_117, plain, (![A_150]: (~r1_tarski(A_150, '#skF_1'(A_150)) | v1_xboole_0(A_150))), inference(resolution, [status(thm)], [c_108, c_58])).
% 14.88/7.42  tff(c_122, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_117])).
% 14.88/7.42  tff(c_14, plain, (![A_11, B_12]: (r2_hidden(A_11, B_12) | v1_xboole_0(B_12) | ~m1_subset_1(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 14.88/7.42  tff(c_198, plain, (![C_167, B_168, A_169]: (r2_hidden(C_167, B_168) | ~r2_hidden(C_167, A_169) | ~r1_tarski(A_169, B_168))), inference(cnfTransformation, [status(thm)], [f_38])).
% 14.88/7.42  tff(c_376, plain, (![A_199, B_200, B_201]: (r2_hidden(A_199, B_200) | ~r1_tarski(B_201, B_200) | v1_xboole_0(B_201) | ~m1_subset_1(A_199, B_201))), inference(resolution, [status(thm)], [c_14, c_198])).
% 14.88/7.42  tff(c_385, plain, (![A_199]: (r2_hidden(A_199, k1_relat_1('#skF_15')) | v1_xboole_0(k2_relat_1('#skF_14')) | ~m1_subset_1(A_199, k2_relat_1('#skF_14')))), inference(resolution, [status(thm)], [c_326, c_376])).
% 14.88/7.42  tff(c_422, plain, (v1_xboole_0(k2_relat_1('#skF_14'))), inference(splitLeft, [status(thm)], [c_385])).
% 14.88/7.42  tff(c_1063, plain, (![B_278, A_279, C_280]: (k1_xboole_0=B_278 | k1_relset_1(A_279, B_278, C_280)=A_279 | ~v1_funct_2(C_280, A_279, B_278) | ~m1_subset_1(C_280, k1_zfmisc_1(k2_zfmisc_1(A_279, B_278))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 14.88/7.42  tff(c_1066, plain, (k1_xboole_0='#skF_13' | k1_relset_1('#skF_12', '#skF_13', '#skF_14')='#skF_12' | ~v1_funct_2('#skF_14', '#skF_12', '#skF_13')), inference(resolution, [status(thm)], [c_98, c_1063])).
% 14.88/7.42  tff(c_1072, plain, (k1_xboole_0='#skF_13' | k1_relat_1('#skF_14')='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_246, c_1066])).
% 14.88/7.42  tff(c_1076, plain, (k1_relat_1('#skF_14')='#skF_12'), inference(splitLeft, [status(thm)], [c_1072])).
% 14.88/7.42  tff(c_454, plain, (![A_214, D_215]: (r2_hidden(k1_funct_1(A_214, D_215), k2_relat_1(A_214)) | ~r2_hidden(D_215, k1_relat_1(A_214)) | ~v1_funct_1(A_214) | ~v1_relat_1(A_214))), inference(cnfTransformation, [status(thm)], [f_78])).
% 14.88/7.42  tff(c_465, plain, (![A_214, D_215]: (~v1_xboole_0(k2_relat_1(A_214)) | ~r2_hidden(D_215, k1_relat_1(A_214)) | ~v1_funct_1(A_214) | ~v1_relat_1(A_214))), inference(resolution, [status(thm)], [c_454, c_2])).
% 14.88/7.42  tff(c_1096, plain, (![D_215]: (~v1_xboole_0(k2_relat_1('#skF_14')) | ~r2_hidden(D_215, '#skF_12') | ~v1_funct_1('#skF_14') | ~v1_relat_1('#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_1076, c_465])).
% 14.88/7.42  tff(c_1110, plain, (![D_215]: (~r2_hidden(D_215, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_102, c_422, c_1096])).
% 14.88/7.42  tff(c_1956, plain, (![A_313, B_314]: (r2_hidden('#skF_8'(A_313, B_314), k1_relat_1(A_313)) | r2_hidden('#skF_9'(A_313, B_314), B_314) | k2_relat_1(A_313)=B_314 | ~v1_funct_1(A_313) | ~v1_relat_1(A_313))), inference(cnfTransformation, [status(thm)], [f_78])).
% 14.88/7.42  tff(c_2003, plain, (![B_314]: (r2_hidden('#skF_8'('#skF_14', B_314), '#skF_12') | r2_hidden('#skF_9'('#skF_14', B_314), B_314) | k2_relat_1('#skF_14')=B_314 | ~v1_funct_1('#skF_14') | ~v1_relat_1('#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_1076, c_1956])).
% 14.88/7.42  tff(c_2018, plain, (![B_314]: (r2_hidden('#skF_8'('#skF_14', B_314), '#skF_12') | r2_hidden('#skF_9'('#skF_14', B_314), B_314) | k2_relat_1('#skF_14')=B_314)), inference(demodulation, [status(thm), theory('equality')], [c_145, c_102, c_2003])).
% 14.88/7.42  tff(c_2020, plain, (![B_315]: (r2_hidden('#skF_9'('#skF_14', B_315), B_315) | k2_relat_1('#skF_14')=B_315)), inference(negUnitSimplification, [status(thm)], [c_1110, c_2018])).
% 14.88/7.42  tff(c_2061, plain, (k2_relat_1('#skF_14')='#skF_12'), inference(resolution, [status(thm)], [c_2020, c_1110])).
% 14.88/7.42  tff(c_2066, plain, (![B_315]: (~v1_xboole_0(B_315) | k2_relat_1('#skF_14')=B_315)), inference(resolution, [status(thm)], [c_2020, c_2])).
% 14.88/7.42  tff(c_2142, plain, (![B_316]: (~v1_xboole_0(B_316) | B_316='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_2061, c_2066])).
% 14.88/7.42  tff(c_2157, plain, (k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_122, c_2142])).
% 14.88/7.42  tff(c_2166, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_2157])).
% 14.88/7.42  tff(c_2167, plain, (k1_xboole_0='#skF_13'), inference(splitRight, [status(thm)], [c_1072])).
% 14.88/7.42  tff(c_2178, plain, (v1_xboole_0('#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_2167, c_122])).
% 14.88/7.42  tff(c_2182, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_2178])).
% 14.88/7.42  tff(c_2184, plain, (~v1_xboole_0(k2_relat_1('#skF_14'))), inference(splitRight, [status(thm)], [c_385])).
% 14.88/7.42  tff(c_2628, plain, (~v1_xboole_0(k1_relat_1('#skF_14')) | ~v1_funct_1('#skF_14') | ~v1_relat_1('#skF_14')), inference(resolution, [status(thm)], [c_2619, c_2184])).
% 14.88/7.42  tff(c_2635, plain, (~v1_xboole_0(k1_relat_1('#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_102, c_2628])).
% 14.88/7.42  tff(c_2883, plain, (~v1_xboole_0('#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_2882, c_2635])).
% 14.88/7.42  tff(c_16, plain, (![A_13, E_54, B_36]: (r2_hidden(k1_funct_1(A_13, E_54), k9_relat_1(A_13, B_36)) | ~r2_hidden(E_54, B_36) | ~r2_hidden(E_54, k1_relat_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_63])).
% 14.88/7.42  tff(c_147, plain, (![A_158, B_159]: (r2_hidden('#skF_2'(A_158, B_159), A_158) | r1_tarski(A_158, B_159))), inference(cnfTransformation, [status(thm)], [f_38])).
% 14.88/7.42  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 14.88/7.42  tff(c_158, plain, (![A_158]: (r1_tarski(A_158, A_158))), inference(resolution, [status(thm)], [c_147, c_8])).
% 14.88/7.42  tff(c_3958, plain, (![A_460, B_461, D_462]: (r2_hidden('#skF_6'(A_460, B_461, k9_relat_1(A_460, B_461), D_462), k1_relat_1(A_460)) | ~r2_hidden(D_462, k9_relat_1(A_460, B_461)) | ~v1_funct_1(A_460) | ~v1_relat_1(A_460))), inference(cnfTransformation, [status(thm)], [f_63])).
% 14.88/7.42  tff(c_3974, plain, (![B_461, D_462]: (r2_hidden('#skF_6'('#skF_14', B_461, k9_relat_1('#skF_14', B_461), D_462), '#skF_12') | ~r2_hidden(D_462, k9_relat_1('#skF_14', B_461)) | ~v1_funct_1('#skF_14') | ~v1_relat_1('#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_2882, c_3958])).
% 14.88/7.42  tff(c_4054, plain, (![B_465, D_466]: (r2_hidden('#skF_6'('#skF_14', B_465, k9_relat_1('#skF_14', B_465), D_466), '#skF_12') | ~r2_hidden(D_466, k9_relat_1('#skF_14', B_465)))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_102, c_3974])).
% 14.88/7.42  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 14.88/7.42  tff(c_4066, plain, (![B_465, D_466, B_6]: (r2_hidden('#skF_6'('#skF_14', B_465, k9_relat_1('#skF_14', B_465), D_466), B_6) | ~r1_tarski('#skF_12', B_6) | ~r2_hidden(D_466, k9_relat_1('#skF_14', B_465)))), inference(resolution, [status(thm)], [c_4054, c_6])).
% 14.88/7.42  tff(c_4165, plain, (![A_474, B_475, D_476]: (k1_funct_1(A_474, '#skF_6'(A_474, B_475, k9_relat_1(A_474, B_475), D_476))=D_476 | ~r2_hidden(D_476, k9_relat_1(A_474, B_475)) | ~v1_funct_1(A_474) | ~v1_relat_1(A_474))), inference(cnfTransformation, [status(thm)], [f_63])).
% 14.88/7.42  tff(c_40, plain, (![A_55, D_94]: (r2_hidden(k1_funct_1(A_55, D_94), k2_relat_1(A_55)) | ~r2_hidden(D_94, k1_relat_1(A_55)) | ~v1_funct_1(A_55) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_78])).
% 14.88/7.42  tff(c_22503, plain, (![D_1196, A_1197, B_1198]: (r2_hidden(D_1196, k2_relat_1(A_1197)) | ~r2_hidden('#skF_6'(A_1197, B_1198, k9_relat_1(A_1197, B_1198), D_1196), k1_relat_1(A_1197)) | ~v1_funct_1(A_1197) | ~v1_relat_1(A_1197) | ~r2_hidden(D_1196, k9_relat_1(A_1197, B_1198)) | ~v1_funct_1(A_1197) | ~v1_relat_1(A_1197))), inference(superposition, [status(thm), theory('equality')], [c_4165, c_40])).
% 14.88/7.42  tff(c_22518, plain, (![D_466, B_465]: (r2_hidden(D_466, k2_relat_1('#skF_14')) | ~v1_funct_1('#skF_14') | ~v1_relat_1('#skF_14') | ~r1_tarski('#skF_12', k1_relat_1('#skF_14')) | ~r2_hidden(D_466, k9_relat_1('#skF_14', B_465)))), inference(resolution, [status(thm)], [c_4066, c_22503])).
% 14.88/7.42  tff(c_22567, plain, (![D_1199, B_1200]: (r2_hidden(D_1199, k2_relat_1('#skF_14')) | ~r2_hidden(D_1199, k9_relat_1('#skF_14', B_1200)))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_2882, c_145, c_102, c_22518])).
% 14.88/7.42  tff(c_22805, plain, (![E_54, B_36]: (r2_hidden(k1_funct_1('#skF_14', E_54), k2_relat_1('#skF_14')) | ~r2_hidden(E_54, B_36) | ~r2_hidden(E_54, k1_relat_1('#skF_14')) | ~v1_funct_1('#skF_14') | ~v1_relat_1('#skF_14'))), inference(resolution, [status(thm)], [c_16, c_22567])).
% 14.88/7.42  tff(c_23119, plain, (![E_1206, B_1207]: (r2_hidden(k1_funct_1('#skF_14', E_1206), k2_relat_1('#skF_14')) | ~r2_hidden(E_1206, B_1207) | ~r2_hidden(E_1206, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_102, c_2882, c_22805])).
% 14.88/7.42  tff(c_29297, plain, (![A_1349, B_1350]: (r2_hidden(k1_funct_1('#skF_14', A_1349), k2_relat_1('#skF_14')) | ~r2_hidden(A_1349, '#skF_12') | v1_xboole_0(B_1350) | ~m1_subset_1(A_1349, B_1350))), inference(resolution, [status(thm)], [c_14, c_23119])).
% 14.88/7.42  tff(c_29303, plain, (r2_hidden(k1_funct_1('#skF_14', '#skF_16'), k2_relat_1('#skF_14')) | ~r2_hidden('#skF_16', '#skF_12') | v1_xboole_0('#skF_12')), inference(resolution, [status(thm)], [c_92, c_29297])).
% 14.88/7.42  tff(c_29308, plain, (r2_hidden(k1_funct_1('#skF_14', '#skF_16'), k2_relat_1('#skF_14')) | ~r2_hidden('#skF_16', '#skF_12')), inference(negUnitSimplification, [status(thm)], [c_2883, c_29303])).
% 14.88/7.42  tff(c_29309, plain, (~r2_hidden('#skF_16', '#skF_12')), inference(splitLeft, [status(thm)], [c_29308])).
% 14.88/7.42  tff(c_29312, plain, (v1_xboole_0('#skF_12') | ~m1_subset_1('#skF_16', '#skF_12')), inference(resolution, [status(thm)], [c_14, c_29309])).
% 14.88/7.42  tff(c_29315, plain, (v1_xboole_0('#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_29312])).
% 14.88/7.42  tff(c_29317, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2883, c_29315])).
% 14.88/7.42  tff(c_29319, plain, (r2_hidden('#skF_16', '#skF_12')), inference(splitRight, [status(thm)], [c_29308])).
% 14.88/7.42  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 14.88/7.42  tff(c_25561, plain, (![B_1252, B_1253]: (r2_hidden('#skF_2'(k9_relat_1('#skF_14', B_1252), B_1253), k2_relat_1('#skF_14')) | r1_tarski(k9_relat_1('#skF_14', B_1252), B_1253))), inference(resolution, [status(thm)], [c_10, c_22567])).
% 14.88/7.42  tff(c_25649, plain, (![B_1257]: (r1_tarski(k9_relat_1('#skF_14', B_1257), k2_relat_1('#skF_14')))), inference(resolution, [status(thm)], [c_25561, c_8])).
% 14.88/7.42  tff(c_344, plain, (![A_192, B_193, B_194]: (r2_hidden('#skF_2'(A_192, B_193), B_194) | ~r1_tarski(A_192, B_194) | r1_tarski(A_192, B_193))), inference(resolution, [status(thm)], [c_10, c_198])).
% 14.88/7.42  tff(c_2444, plain, (![A_347, B_348, B_349, B_350]: (r2_hidden('#skF_2'(A_347, B_348), B_349) | ~r1_tarski(B_350, B_349) | ~r1_tarski(A_347, B_350) | r1_tarski(A_347, B_348))), inference(resolution, [status(thm)], [c_344, c_6])).
% 14.88/7.42  tff(c_2460, plain, (![A_351, B_352]: (r2_hidden('#skF_2'(A_351, B_352), k1_relat_1('#skF_15')) | ~r1_tarski(A_351, k2_relat_1('#skF_14')) | r1_tarski(A_351, B_352))), inference(resolution, [status(thm)], [c_326, c_2444])).
% 14.88/7.42  tff(c_2480, plain, (![A_351]: (~r1_tarski(A_351, k2_relat_1('#skF_14')) | r1_tarski(A_351, k1_relat_1('#skF_15')))), inference(resolution, [status(thm)], [c_2460, c_8])).
% 14.88/7.42  tff(c_25758, plain, (![B_1258]: (r1_tarski(k9_relat_1('#skF_14', B_1258), k1_relat_1('#skF_15')))), inference(resolution, [status(thm)], [c_25649, c_2480])).
% 14.88/7.42  tff(c_2940, plain, (![A_395, E_396, B_397]: (r2_hidden(k1_funct_1(A_395, E_396), k9_relat_1(A_395, B_397)) | ~r2_hidden(E_396, B_397) | ~r2_hidden(E_396, k1_relat_1(A_395)) | ~v1_funct_1(A_395) | ~v1_relat_1(A_395))), inference(cnfTransformation, [status(thm)], [f_63])).
% 14.88/7.42  tff(c_2952, plain, (![A_395, E_396, B_6, B_397]: (r2_hidden(k1_funct_1(A_395, E_396), B_6) | ~r1_tarski(k9_relat_1(A_395, B_397), B_6) | ~r2_hidden(E_396, B_397) | ~r2_hidden(E_396, k1_relat_1(A_395)) | ~v1_funct_1(A_395) | ~v1_relat_1(A_395))), inference(resolution, [status(thm)], [c_2940, c_6])).
% 14.88/7.42  tff(c_25776, plain, (![E_396, B_1258]: (r2_hidden(k1_funct_1('#skF_14', E_396), k1_relat_1('#skF_15')) | ~r2_hidden(E_396, B_1258) | ~r2_hidden(E_396, k1_relat_1('#skF_14')) | ~v1_funct_1('#skF_14') | ~v1_relat_1('#skF_14'))), inference(resolution, [status(thm)], [c_25758, c_2952])).
% 14.88/7.42  tff(c_25836, plain, (![E_396, B_1258]: (r2_hidden(k1_funct_1('#skF_14', E_396), k1_relat_1('#skF_15')) | ~r2_hidden(E_396, B_1258) | ~r2_hidden(E_396, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_102, c_2882, c_25776])).
% 14.88/7.42  tff(c_29478, plain, (r2_hidden(k1_funct_1('#skF_14', '#skF_16'), k1_relat_1('#skF_15')) | ~r2_hidden('#skF_16', '#skF_12')), inference(resolution, [status(thm)], [c_29319, c_25836])).
% 14.88/7.42  tff(c_29495, plain, (r2_hidden(k1_funct_1('#skF_14', '#skF_16'), k1_relat_1('#skF_15'))), inference(demodulation, [status(thm), theory('equality')], [c_29319, c_29478])).
% 14.88/7.42  tff(c_82, plain, (![A_112, B_113, C_115]: (k7_partfun1(A_112, B_113, C_115)=k1_funct_1(B_113, C_115) | ~r2_hidden(C_115, k1_relat_1(B_113)) | ~v1_funct_1(B_113) | ~v5_relat_1(B_113, A_112) | ~v1_relat_1(B_113))), inference(cnfTransformation, [status(thm)], [f_130])).
% 14.88/7.42  tff(c_29827, plain, (![A_112]: (k7_partfun1(A_112, '#skF_15', k1_funct_1('#skF_14', '#skF_16'))=k1_funct_1('#skF_15', k1_funct_1('#skF_14', '#skF_16')) | ~v1_funct_1('#skF_15') | ~v5_relat_1('#skF_15', A_112) | ~v1_relat_1('#skF_15'))), inference(resolution, [status(thm)], [c_29495, c_82])).
% 14.88/7.42  tff(c_32081, plain, (![A_1423]: (k7_partfun1(A_1423, '#skF_15', k1_funct_1('#skF_14', '#skF_16'))=k1_funct_1('#skF_15', k1_funct_1('#skF_14', '#skF_16')) | ~v5_relat_1('#skF_15', A_1423))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_96, c_29827])).
% 14.88/7.42  tff(c_86, plain, (k7_partfun1('#skF_11', '#skF_15', k1_funct_1('#skF_14', '#skF_16'))!=k1_funct_1(k8_funct_2('#skF_12', '#skF_13', '#skF_11', '#skF_14', '#skF_15'), '#skF_16')), inference(cnfTransformation, [status(thm)], [f_179])).
% 14.88/7.42  tff(c_32087, plain, (k1_funct_1(k8_funct_2('#skF_12', '#skF_13', '#skF_11', '#skF_14', '#skF_15'), '#skF_16')!=k1_funct_1('#skF_15', k1_funct_1('#skF_14', '#skF_16')) | ~v5_relat_1('#skF_15', '#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_32081, c_86])).
% 14.88/7.42  tff(c_32093, plain, (k1_funct_1(k8_funct_2('#skF_12', '#skF_13', '#skF_11', '#skF_14', '#skF_15'), '#skF_16')!=k1_funct_1('#skF_15', k1_funct_1('#skF_14', '#skF_16'))), inference(demodulation, [status(thm), theory('equality')], [c_217, c_32087])).
% 14.88/7.42  tff(c_32097, plain, (~m1_subset_1('#skF_16', '#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_8212, c_32093])).
% 14.88/7.42  tff(c_32101, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_32097])).
% 14.88/7.42  tff(c_32102, plain, (k1_xboole_0='#skF_13'), inference(splitRight, [status(thm)], [c_2878])).
% 14.88/7.42  tff(c_32113, plain, (v1_xboole_0('#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_32102, c_122])).
% 14.88/7.42  tff(c_32117, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_32113])).
% 14.88/7.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.88/7.42  
% 14.88/7.42  Inference rules
% 14.88/7.42  ----------------------
% 14.88/7.42  #Ref     : 4
% 14.88/7.42  #Sup     : 7194
% 14.88/7.42  #Fact    : 0
% 14.88/7.42  #Define  : 0
% 14.88/7.42  #Split   : 47
% 14.88/7.42  #Chain   : 0
% 14.88/7.42  #Close   : 0
% 14.88/7.42  
% 14.88/7.42  Ordering : KBO
% 14.88/7.42  
% 14.88/7.42  Simplification rules
% 14.88/7.42  ----------------------
% 14.88/7.42  #Subsume      : 3008
% 14.88/7.42  #Demod        : 2418
% 14.88/7.42  #Tautology    : 426
% 14.88/7.42  #SimpNegUnit  : 141
% 14.88/7.42  #BackRed      : 69
% 14.88/7.42  
% 14.88/7.42  #Partial instantiations: 0
% 14.88/7.42  #Strategies tried      : 1
% 14.88/7.42  
% 14.88/7.42  Timing (in seconds)
% 14.88/7.42  ----------------------
% 14.88/7.42  Preprocessing        : 0.41
% 14.88/7.42  Parsing              : 0.20
% 14.88/7.42  CNF conversion       : 0.04
% 14.88/7.42  Main loop            : 6.17
% 14.88/7.42  Inferencing          : 1.27
% 14.88/7.42  Reduction            : 1.49
% 14.88/7.42  Demodulation         : 1.01
% 14.88/7.42  BG Simplification    : 0.12
% 14.88/7.42  Subsumption          : 2.84
% 14.88/7.42  Abstraction          : 0.19
% 14.88/7.42  MUC search           : 0.00
% 14.88/7.42  Cooper               : 0.00
% 14.88/7.42  Total                : 6.64
% 14.88/7.42  Index Insertion      : 0.00
% 14.88/7.42  Index Deletion       : 0.00
% 14.88/7.42  Index Matching       : 0.00
% 14.88/7.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
