%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:12 EST 2020

% Result     : Theorem 7.91s
% Output     : CNFRefutation 8.17s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 490 expanded)
%              Number of leaves         :   40 ( 196 expanded)
%              Depth                    :   12
%              Number of atoms          :  603 (2578 expanded)
%              Number of equality atoms :  120 ( 524 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r1_subset_1,type,(
    r1_subset_1: ( $i * $i ) > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_tmap_1,type,(
    k1_tmap_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_225,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( ~ v1_xboole_0(C)
                  & m1_subset_1(C,k1_zfmisc_1(A)) )
               => ! [D] :
                    ( ( ~ v1_xboole_0(D)
                      & m1_subset_1(D,k1_zfmisc_1(A)) )
                   => ( r1_subset_1(C,D)
                     => ! [E] :
                          ( ( v1_funct_1(E)
                            & v1_funct_2(E,C,B)
                            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,B))) )
                         => ! [F] :
                              ( ( v1_funct_1(F)
                                & v1_funct_2(F,D,B)
                                & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(D,B))) )
                             => ( k2_partfun1(C,B,E,k9_subset_1(A,C,D)) = k2_partfun1(D,B,F,k9_subset_1(A,C,D))
                                & k2_partfun1(k4_subset_1(A,C,D),B,k1_tmap_1(A,B,C,D,E,F),C) = E
                                & k2_partfun1(k4_subset_1(A,C,D),B,k1_tmap_1(A,B,C,D,E,F),D) = F ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tmap_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_183,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & ~ v1_xboole_0(C)
        & m1_subset_1(C,k1_zfmisc_1(A))
        & ~ v1_xboole_0(D)
        & m1_subset_1(D,k1_zfmisc_1(A))
        & v1_funct_1(E)
        & v1_funct_2(E,C,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,D,B)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(D,B))) )
     => ( v1_funct_1(k1_tmap_1(A,B,C,D,E,F))
        & v1_funct_2(k1_tmap_1(A,B,C,D,E,F),k4_subset_1(A,C,D),B)
        & m1_subset_1(k1_tmap_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A,C,D),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tmap_1)).

tff(f_101,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_149,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ( ~ v1_xboole_0(C)
                & m1_subset_1(C,k1_zfmisc_1(A)) )
             => ! [D] :
                  ( ( ~ v1_xboole_0(D)
                    & m1_subset_1(D,k1_zfmisc_1(A)) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,C,B)
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,B))) )
                     => ! [F] :
                          ( ( v1_funct_1(F)
                            & v1_funct_2(F,D,B)
                            & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(D,B))) )
                         => ( k2_partfun1(C,B,E,k9_subset_1(A,C,D)) = k2_partfun1(D,B,F,k9_subset_1(A,C,D))
                           => ! [G] :
                                ( ( v1_funct_1(G)
                                  & v1_funct_2(G,k4_subset_1(A,C,D),B)
                                  & m1_subset_1(G,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A,C,D),B))) )
                               => ( G = k1_tmap_1(A,B,C,D,E,F)
                                <=> ( k2_partfun1(k4_subset_1(A,C,D),B,G,C) = E
                                    & k2_partfun1(k4_subset_1(A,C,D),B,G,D) = F ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tmap_1)).

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_891,plain,(
    ! [C_327,A_328,B_329] :
      ( v1_relat_1(C_327)
      | ~ m1_subset_1(C_327,k1_zfmisc_1(k2_zfmisc_1(A_328,B_329))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_899,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_891])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_84,plain,(
    ! [A_228,B_229] :
      ( r1_xboole_0(A_228,B_229)
      | k3_xboole_0(A_228,B_229) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_92,plain,(
    ! [B_230,A_231] :
      ( r1_xboole_0(B_230,A_231)
      | k3_xboole_0(A_231,B_230) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_84,c_6])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_905,plain,(
    ! [B_330,A_331] :
      ( k3_xboole_0(B_330,A_331) = k1_xboole_0
      | k3_xboole_0(A_331,B_330) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_92,c_2])).

tff(c_908,plain,(
    ! [A_5] : k3_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_905])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_3632,plain,(
    ! [A_742,B_743] :
      ( k7_relat_1(A_742,B_743) = k1_xboole_0
      | ~ r1_xboole_0(B_743,k1_relat_1(A_742))
      | ~ v1_relat_1(A_742) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4703,plain,(
    ! [A_851,A_852] :
      ( k7_relat_1(A_851,A_852) = k1_xboole_0
      | ~ v1_relat_1(A_851)
      | k3_xboole_0(A_852,k1_relat_1(A_851)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_3632])).

tff(c_4719,plain,(
    ! [A_853] :
      ( k7_relat_1(A_853,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_853) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_908,c_4703])).

tff(c_4726,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_899,c_4719])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_62,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_3643,plain,(
    ! [A_744,B_745] :
      ( r1_xboole_0(A_744,B_745)
      | ~ r1_subset_1(A_744,B_745)
      | v1_xboole_0(B_745)
      | v1_xboole_0(A_744) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4670,plain,(
    ! [A_849,B_850] :
      ( k3_xboole_0(A_849,B_850) = k1_xboole_0
      | ~ r1_subset_1(A_849,B_850)
      | v1_xboole_0(B_850)
      | v1_xboole_0(A_849) ) ),
    inference(resolution,[status(thm)],[c_3643,c_2])).

tff(c_4679,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_4670])).

tff(c_4686,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_66,c_4679])).

tff(c_3692,plain,(
    ! [A_752,B_753,C_754] :
      ( k9_subset_1(A_752,B_753,C_754) = k3_xboole_0(B_753,C_754)
      | ~ m1_subset_1(C_754,k1_zfmisc_1(A_752)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3704,plain,(
    ! [B_753] : k9_subset_1('#skF_1',B_753,'#skF_4') = k3_xboole_0(B_753,'#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_3692])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_898,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_891])).

tff(c_4727,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_898,c_4719])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_58,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_72,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_54,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_52,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_4784,plain,(
    ! [F_859,E_857,B_855,D_856,A_858,C_854] :
      ( v1_funct_1(k1_tmap_1(A_858,B_855,C_854,D_856,E_857,F_859))
      | ~ m1_subset_1(F_859,k1_zfmisc_1(k2_zfmisc_1(D_856,B_855)))
      | ~ v1_funct_2(F_859,D_856,B_855)
      | ~ v1_funct_1(F_859)
      | ~ m1_subset_1(E_857,k1_zfmisc_1(k2_zfmisc_1(C_854,B_855)))
      | ~ v1_funct_2(E_857,C_854,B_855)
      | ~ v1_funct_1(E_857)
      | ~ m1_subset_1(D_856,k1_zfmisc_1(A_858))
      | v1_xboole_0(D_856)
      | ~ m1_subset_1(C_854,k1_zfmisc_1(A_858))
      | v1_xboole_0(C_854)
      | v1_xboole_0(B_855)
      | v1_xboole_0(A_858) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_4788,plain,(
    ! [A_858,C_854,E_857] :
      ( v1_funct_1(k1_tmap_1(A_858,'#skF_2',C_854,'#skF_4',E_857,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_857,k1_zfmisc_1(k2_zfmisc_1(C_854,'#skF_2')))
      | ~ v1_funct_2(E_857,C_854,'#skF_2')
      | ~ v1_funct_1(E_857)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_858))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_854,k1_zfmisc_1(A_858))
      | v1_xboole_0(C_854)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_858) ) ),
    inference(resolution,[status(thm)],[c_50,c_4784])).

tff(c_4795,plain,(
    ! [A_858,C_854,E_857] :
      ( v1_funct_1(k1_tmap_1(A_858,'#skF_2',C_854,'#skF_4',E_857,'#skF_6'))
      | ~ m1_subset_1(E_857,k1_zfmisc_1(k2_zfmisc_1(C_854,'#skF_2')))
      | ~ v1_funct_2(E_857,C_854,'#skF_2')
      | ~ v1_funct_1(E_857)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_858))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_854,k1_zfmisc_1(A_858))
      | v1_xboole_0(C_854)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_858) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_4788])).

tff(c_4942,plain,(
    ! [A_881,C_882,E_883] :
      ( v1_funct_1(k1_tmap_1(A_881,'#skF_2',C_882,'#skF_4',E_883,'#skF_6'))
      | ~ m1_subset_1(E_883,k1_zfmisc_1(k2_zfmisc_1(C_882,'#skF_2')))
      | ~ v1_funct_2(E_883,C_882,'#skF_2')
      | ~ v1_funct_1(E_883)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_881))
      | ~ m1_subset_1(C_882,k1_zfmisc_1(A_881))
      | v1_xboole_0(C_882)
      | v1_xboole_0(A_881) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_4795])).

tff(c_4944,plain,(
    ! [A_881] :
      ( v1_funct_1(k1_tmap_1(A_881,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_881))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_881))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_881) ) ),
    inference(resolution,[status(thm)],[c_56,c_4942])).

tff(c_4949,plain,(
    ! [A_881] :
      ( v1_funct_1(k1_tmap_1(A_881,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_881))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_881))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_881) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_4944])).

tff(c_4962,plain,(
    ! [A_885] :
      ( v1_funct_1(k1_tmap_1(A_885,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_885))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_885))
      | v1_xboole_0(A_885) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_4949])).

tff(c_4965,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_4962])).

tff(c_4968,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_4965])).

tff(c_4969,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_4968])).

tff(c_4512,plain,(
    ! [A_833,B_834,C_835,D_836] :
      ( k2_partfun1(A_833,B_834,C_835,D_836) = k7_relat_1(C_835,D_836)
      | ~ m1_subset_1(C_835,k1_zfmisc_1(k2_zfmisc_1(A_833,B_834)))
      | ~ v1_funct_1(C_835) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_4514,plain,(
    ! [D_836] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_836) = k7_relat_1('#skF_5',D_836)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_4512])).

tff(c_4519,plain,(
    ! [D_836] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_836) = k7_relat_1('#skF_5',D_836) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_4514])).

tff(c_4516,plain,(
    ! [D_836] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_836) = k7_relat_1('#skF_6',D_836)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_50,c_4512])).

tff(c_4522,plain,(
    ! [D_836] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_836) = k7_relat_1('#skF_6',D_836) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4516])).

tff(c_44,plain,(
    ! [B_161,C_162,A_160,E_164,F_165,D_163] :
      ( v1_funct_2(k1_tmap_1(A_160,B_161,C_162,D_163,E_164,F_165),k4_subset_1(A_160,C_162,D_163),B_161)
      | ~ m1_subset_1(F_165,k1_zfmisc_1(k2_zfmisc_1(D_163,B_161)))
      | ~ v1_funct_2(F_165,D_163,B_161)
      | ~ v1_funct_1(F_165)
      | ~ m1_subset_1(E_164,k1_zfmisc_1(k2_zfmisc_1(C_162,B_161)))
      | ~ v1_funct_2(E_164,C_162,B_161)
      | ~ v1_funct_1(E_164)
      | ~ m1_subset_1(D_163,k1_zfmisc_1(A_160))
      | v1_xboole_0(D_163)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(A_160))
      | v1_xboole_0(C_162)
      | v1_xboole_0(B_161)
      | v1_xboole_0(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_42,plain,(
    ! [B_161,C_162,A_160,E_164,F_165,D_163] :
      ( m1_subset_1(k1_tmap_1(A_160,B_161,C_162,D_163,E_164,F_165),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_160,C_162,D_163),B_161)))
      | ~ m1_subset_1(F_165,k1_zfmisc_1(k2_zfmisc_1(D_163,B_161)))
      | ~ v1_funct_2(F_165,D_163,B_161)
      | ~ v1_funct_1(F_165)
      | ~ m1_subset_1(E_164,k1_zfmisc_1(k2_zfmisc_1(C_162,B_161)))
      | ~ v1_funct_2(E_164,C_162,B_161)
      | ~ v1_funct_1(E_164)
      | ~ m1_subset_1(D_163,k1_zfmisc_1(A_160))
      | v1_xboole_0(D_163)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(A_160))
      | v1_xboole_0(C_162)
      | v1_xboole_0(B_161)
      | v1_xboole_0(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_5012,plain,(
    ! [E_893,D_897,C_896,F_895,A_892,B_894] :
      ( k2_partfun1(k4_subset_1(A_892,C_896,D_897),B_894,k1_tmap_1(A_892,B_894,C_896,D_897,E_893,F_895),C_896) = E_893
      | ~ m1_subset_1(k1_tmap_1(A_892,B_894,C_896,D_897,E_893,F_895),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_892,C_896,D_897),B_894)))
      | ~ v1_funct_2(k1_tmap_1(A_892,B_894,C_896,D_897,E_893,F_895),k4_subset_1(A_892,C_896,D_897),B_894)
      | ~ v1_funct_1(k1_tmap_1(A_892,B_894,C_896,D_897,E_893,F_895))
      | k2_partfun1(D_897,B_894,F_895,k9_subset_1(A_892,C_896,D_897)) != k2_partfun1(C_896,B_894,E_893,k9_subset_1(A_892,C_896,D_897))
      | ~ m1_subset_1(F_895,k1_zfmisc_1(k2_zfmisc_1(D_897,B_894)))
      | ~ v1_funct_2(F_895,D_897,B_894)
      | ~ v1_funct_1(F_895)
      | ~ m1_subset_1(E_893,k1_zfmisc_1(k2_zfmisc_1(C_896,B_894)))
      | ~ v1_funct_2(E_893,C_896,B_894)
      | ~ v1_funct_1(E_893)
      | ~ m1_subset_1(D_897,k1_zfmisc_1(A_892))
      | v1_xboole_0(D_897)
      | ~ m1_subset_1(C_896,k1_zfmisc_1(A_892))
      | v1_xboole_0(C_896)
      | v1_xboole_0(B_894)
      | v1_xboole_0(A_892) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_5587,plain,(
    ! [A_1020,B_1017,C_1016,F_1021,D_1018,E_1019] :
      ( k2_partfun1(k4_subset_1(A_1020,C_1016,D_1018),B_1017,k1_tmap_1(A_1020,B_1017,C_1016,D_1018,E_1019,F_1021),C_1016) = E_1019
      | ~ v1_funct_2(k1_tmap_1(A_1020,B_1017,C_1016,D_1018,E_1019,F_1021),k4_subset_1(A_1020,C_1016,D_1018),B_1017)
      | ~ v1_funct_1(k1_tmap_1(A_1020,B_1017,C_1016,D_1018,E_1019,F_1021))
      | k2_partfun1(D_1018,B_1017,F_1021,k9_subset_1(A_1020,C_1016,D_1018)) != k2_partfun1(C_1016,B_1017,E_1019,k9_subset_1(A_1020,C_1016,D_1018))
      | ~ m1_subset_1(F_1021,k1_zfmisc_1(k2_zfmisc_1(D_1018,B_1017)))
      | ~ v1_funct_2(F_1021,D_1018,B_1017)
      | ~ v1_funct_1(F_1021)
      | ~ m1_subset_1(E_1019,k1_zfmisc_1(k2_zfmisc_1(C_1016,B_1017)))
      | ~ v1_funct_2(E_1019,C_1016,B_1017)
      | ~ v1_funct_1(E_1019)
      | ~ m1_subset_1(D_1018,k1_zfmisc_1(A_1020))
      | v1_xboole_0(D_1018)
      | ~ m1_subset_1(C_1016,k1_zfmisc_1(A_1020))
      | v1_xboole_0(C_1016)
      | v1_xboole_0(B_1017)
      | v1_xboole_0(A_1020) ) ),
    inference(resolution,[status(thm)],[c_42,c_5012])).

tff(c_5808,plain,(
    ! [F_1056,E_1054,D_1053,C_1051,A_1055,B_1052] :
      ( k2_partfun1(k4_subset_1(A_1055,C_1051,D_1053),B_1052,k1_tmap_1(A_1055,B_1052,C_1051,D_1053,E_1054,F_1056),C_1051) = E_1054
      | ~ v1_funct_1(k1_tmap_1(A_1055,B_1052,C_1051,D_1053,E_1054,F_1056))
      | k2_partfun1(D_1053,B_1052,F_1056,k9_subset_1(A_1055,C_1051,D_1053)) != k2_partfun1(C_1051,B_1052,E_1054,k9_subset_1(A_1055,C_1051,D_1053))
      | ~ m1_subset_1(F_1056,k1_zfmisc_1(k2_zfmisc_1(D_1053,B_1052)))
      | ~ v1_funct_2(F_1056,D_1053,B_1052)
      | ~ v1_funct_1(F_1056)
      | ~ m1_subset_1(E_1054,k1_zfmisc_1(k2_zfmisc_1(C_1051,B_1052)))
      | ~ v1_funct_2(E_1054,C_1051,B_1052)
      | ~ v1_funct_1(E_1054)
      | ~ m1_subset_1(D_1053,k1_zfmisc_1(A_1055))
      | v1_xboole_0(D_1053)
      | ~ m1_subset_1(C_1051,k1_zfmisc_1(A_1055))
      | v1_xboole_0(C_1051)
      | v1_xboole_0(B_1052)
      | v1_xboole_0(A_1055) ) ),
    inference(resolution,[status(thm)],[c_44,c_5587])).

tff(c_5814,plain,(
    ! [A_1055,C_1051,E_1054] :
      ( k2_partfun1(k4_subset_1(A_1055,C_1051,'#skF_4'),'#skF_2',k1_tmap_1(A_1055,'#skF_2',C_1051,'#skF_4',E_1054,'#skF_6'),C_1051) = E_1054
      | ~ v1_funct_1(k1_tmap_1(A_1055,'#skF_2',C_1051,'#skF_4',E_1054,'#skF_6'))
      | k2_partfun1(C_1051,'#skF_2',E_1054,k9_subset_1(A_1055,C_1051,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_1055,C_1051,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1054,k1_zfmisc_1(k2_zfmisc_1(C_1051,'#skF_2')))
      | ~ v1_funct_2(E_1054,C_1051,'#skF_2')
      | ~ v1_funct_1(E_1054)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1055))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1051,k1_zfmisc_1(A_1055))
      | v1_xboole_0(C_1051)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1055) ) ),
    inference(resolution,[status(thm)],[c_50,c_5808])).

tff(c_5822,plain,(
    ! [A_1055,C_1051,E_1054] :
      ( k2_partfun1(k4_subset_1(A_1055,C_1051,'#skF_4'),'#skF_2',k1_tmap_1(A_1055,'#skF_2',C_1051,'#skF_4',E_1054,'#skF_6'),C_1051) = E_1054
      | ~ v1_funct_1(k1_tmap_1(A_1055,'#skF_2',C_1051,'#skF_4',E_1054,'#skF_6'))
      | k2_partfun1(C_1051,'#skF_2',E_1054,k9_subset_1(A_1055,C_1051,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1055,C_1051,'#skF_4'))
      | ~ m1_subset_1(E_1054,k1_zfmisc_1(k2_zfmisc_1(C_1051,'#skF_2')))
      | ~ v1_funct_2(E_1054,C_1051,'#skF_2')
      | ~ v1_funct_1(E_1054)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1055))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1051,k1_zfmisc_1(A_1055))
      | v1_xboole_0(C_1051)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1055) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_4522,c_5814])).

tff(c_6210,plain,(
    ! [A_1127,C_1128,E_1129] :
      ( k2_partfun1(k4_subset_1(A_1127,C_1128,'#skF_4'),'#skF_2',k1_tmap_1(A_1127,'#skF_2',C_1128,'#skF_4',E_1129,'#skF_6'),C_1128) = E_1129
      | ~ v1_funct_1(k1_tmap_1(A_1127,'#skF_2',C_1128,'#skF_4',E_1129,'#skF_6'))
      | k2_partfun1(C_1128,'#skF_2',E_1129,k9_subset_1(A_1127,C_1128,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1127,C_1128,'#skF_4'))
      | ~ m1_subset_1(E_1129,k1_zfmisc_1(k2_zfmisc_1(C_1128,'#skF_2')))
      | ~ v1_funct_2(E_1129,C_1128,'#skF_2')
      | ~ v1_funct_1(E_1129)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1127))
      | ~ m1_subset_1(C_1128,k1_zfmisc_1(A_1127))
      | v1_xboole_0(C_1128)
      | v1_xboole_0(A_1127) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_5822])).

tff(c_6215,plain,(
    ! [A_1127] :
      ( k2_partfun1(k4_subset_1(A_1127,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1127,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1127,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1127,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1127,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1127))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1127))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1127) ) ),
    inference(resolution,[status(thm)],[c_56,c_6210])).

tff(c_6223,plain,(
    ! [A_1127] :
      ( k2_partfun1(k4_subset_1(A_1127,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1127,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1127,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1127,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1127,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1127))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1127))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_4519,c_6215])).

tff(c_6246,plain,(
    ! [A_1130] :
      ( k2_partfun1(k4_subset_1(A_1130,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1130,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1130,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1130,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1130,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1130))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1130))
      | v1_xboole_0(A_1130) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_6223])).

tff(c_948,plain,(
    ! [A_340,B_341] :
      ( k7_relat_1(A_340,B_341) = k1_xboole_0
      | ~ r1_xboole_0(B_341,k1_relat_1(A_340))
      | ~ v1_relat_1(A_340) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2040,plain,(
    ! [A_456,A_457] :
      ( k7_relat_1(A_456,A_457) = k1_xboole_0
      | ~ v1_relat_1(A_456)
      | k3_xboole_0(A_457,k1_relat_1(A_456)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_948])).

tff(c_2056,plain,(
    ! [A_458] :
      ( k7_relat_1(A_458,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_458) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_908,c_2040])).

tff(c_2063,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_899,c_2056])).

tff(c_968,plain,(
    ! [A_344,B_345] :
      ( r1_xboole_0(A_344,B_345)
      | ~ r1_subset_1(A_344,B_345)
      | v1_xboole_0(B_345)
      | v1_xboole_0(A_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2164,plain,(
    ! [A_464,B_465] :
      ( k3_xboole_0(A_464,B_465) = k1_xboole_0
      | ~ r1_subset_1(A_464,B_465)
      | v1_xboole_0(B_465)
      | v1_xboole_0(A_464) ) ),
    inference(resolution,[status(thm)],[c_968,c_2])).

tff(c_2173,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_2164])).

tff(c_2180,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_66,c_2173])).

tff(c_1865,plain,(
    ! [A_437,B_438,C_439] :
      ( k9_subset_1(A_437,B_438,C_439) = k3_xboole_0(B_438,C_439)
      | ~ m1_subset_1(C_439,k1_zfmisc_1(A_437)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1877,plain,(
    ! [B_438] : k9_subset_1('#skF_1',B_438,'#skF_4') = k3_xboole_0(B_438,'#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_1865])).

tff(c_2064,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_898,c_2056])).

tff(c_2268,plain,(
    ! [A_476,B_473,C_472,D_474,E_475,F_477] :
      ( v1_funct_1(k1_tmap_1(A_476,B_473,C_472,D_474,E_475,F_477))
      | ~ m1_subset_1(F_477,k1_zfmisc_1(k2_zfmisc_1(D_474,B_473)))
      | ~ v1_funct_2(F_477,D_474,B_473)
      | ~ v1_funct_1(F_477)
      | ~ m1_subset_1(E_475,k1_zfmisc_1(k2_zfmisc_1(C_472,B_473)))
      | ~ v1_funct_2(E_475,C_472,B_473)
      | ~ v1_funct_1(E_475)
      | ~ m1_subset_1(D_474,k1_zfmisc_1(A_476))
      | v1_xboole_0(D_474)
      | ~ m1_subset_1(C_472,k1_zfmisc_1(A_476))
      | v1_xboole_0(C_472)
      | v1_xboole_0(B_473)
      | v1_xboole_0(A_476) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_2272,plain,(
    ! [A_476,C_472,E_475] :
      ( v1_funct_1(k1_tmap_1(A_476,'#skF_2',C_472,'#skF_4',E_475,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_475,k1_zfmisc_1(k2_zfmisc_1(C_472,'#skF_2')))
      | ~ v1_funct_2(E_475,C_472,'#skF_2')
      | ~ v1_funct_1(E_475)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_476))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_472,k1_zfmisc_1(A_476))
      | v1_xboole_0(C_472)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_476) ) ),
    inference(resolution,[status(thm)],[c_50,c_2268])).

tff(c_2279,plain,(
    ! [A_476,C_472,E_475] :
      ( v1_funct_1(k1_tmap_1(A_476,'#skF_2',C_472,'#skF_4',E_475,'#skF_6'))
      | ~ m1_subset_1(E_475,k1_zfmisc_1(k2_zfmisc_1(C_472,'#skF_2')))
      | ~ v1_funct_2(E_475,C_472,'#skF_2')
      | ~ v1_funct_1(E_475)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_476))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_472,k1_zfmisc_1(A_476))
      | v1_xboole_0(C_472)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_476) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_2272])).

tff(c_2364,plain,(
    ! [A_493,C_494,E_495] :
      ( v1_funct_1(k1_tmap_1(A_493,'#skF_2',C_494,'#skF_4',E_495,'#skF_6'))
      | ~ m1_subset_1(E_495,k1_zfmisc_1(k2_zfmisc_1(C_494,'#skF_2')))
      | ~ v1_funct_2(E_495,C_494,'#skF_2')
      | ~ v1_funct_1(E_495)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_493))
      | ~ m1_subset_1(C_494,k1_zfmisc_1(A_493))
      | v1_xboole_0(C_494)
      | v1_xboole_0(A_493) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_2279])).

tff(c_2366,plain,(
    ! [A_493] :
      ( v1_funct_1(k1_tmap_1(A_493,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_493))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_493))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_493) ) ),
    inference(resolution,[status(thm)],[c_56,c_2364])).

tff(c_2371,plain,(
    ! [A_493] :
      ( v1_funct_1(k1_tmap_1(A_493,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_493))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_493))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_493) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_2366])).

tff(c_2384,plain,(
    ! [A_497] :
      ( v1_funct_1(k1_tmap_1(A_497,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_497))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_497))
      | v1_xboole_0(A_497) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_2371])).

tff(c_2387,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_2384])).

tff(c_2390,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2387])).

tff(c_2391,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2390])).

tff(c_1951,plain,(
    ! [A_448,B_449,C_450,D_451] :
      ( k2_partfun1(A_448,B_449,C_450,D_451) = k7_relat_1(C_450,D_451)
      | ~ m1_subset_1(C_450,k1_zfmisc_1(k2_zfmisc_1(A_448,B_449)))
      | ~ v1_funct_1(C_450) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1953,plain,(
    ! [D_451] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_451) = k7_relat_1('#skF_5',D_451)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_1951])).

tff(c_1958,plain,(
    ! [D_451] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_451) = k7_relat_1('#skF_5',D_451) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1953])).

tff(c_1955,plain,(
    ! [D_451] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_451) = k7_relat_1('#skF_6',D_451)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_50,c_1951])).

tff(c_1961,plain,(
    ! [D_451] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_451) = k7_relat_1('#skF_6',D_451) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1955])).

tff(c_2434,plain,(
    ! [D_509,A_504,F_507,E_505,C_508,B_506] :
      ( k2_partfun1(k4_subset_1(A_504,C_508,D_509),B_506,k1_tmap_1(A_504,B_506,C_508,D_509,E_505,F_507),D_509) = F_507
      | ~ m1_subset_1(k1_tmap_1(A_504,B_506,C_508,D_509,E_505,F_507),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_504,C_508,D_509),B_506)))
      | ~ v1_funct_2(k1_tmap_1(A_504,B_506,C_508,D_509,E_505,F_507),k4_subset_1(A_504,C_508,D_509),B_506)
      | ~ v1_funct_1(k1_tmap_1(A_504,B_506,C_508,D_509,E_505,F_507))
      | k2_partfun1(D_509,B_506,F_507,k9_subset_1(A_504,C_508,D_509)) != k2_partfun1(C_508,B_506,E_505,k9_subset_1(A_504,C_508,D_509))
      | ~ m1_subset_1(F_507,k1_zfmisc_1(k2_zfmisc_1(D_509,B_506)))
      | ~ v1_funct_2(F_507,D_509,B_506)
      | ~ v1_funct_1(F_507)
      | ~ m1_subset_1(E_505,k1_zfmisc_1(k2_zfmisc_1(C_508,B_506)))
      | ~ v1_funct_2(E_505,C_508,B_506)
      | ~ v1_funct_1(E_505)
      | ~ m1_subset_1(D_509,k1_zfmisc_1(A_504))
      | v1_xboole_0(D_509)
      | ~ m1_subset_1(C_508,k1_zfmisc_1(A_504))
      | v1_xboole_0(C_508)
      | v1_xboole_0(B_506)
      | v1_xboole_0(A_504) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_2784,plain,(
    ! [B_620,E_622,D_621,A_623,C_619,F_624] :
      ( k2_partfun1(k4_subset_1(A_623,C_619,D_621),B_620,k1_tmap_1(A_623,B_620,C_619,D_621,E_622,F_624),D_621) = F_624
      | ~ v1_funct_2(k1_tmap_1(A_623,B_620,C_619,D_621,E_622,F_624),k4_subset_1(A_623,C_619,D_621),B_620)
      | ~ v1_funct_1(k1_tmap_1(A_623,B_620,C_619,D_621,E_622,F_624))
      | k2_partfun1(D_621,B_620,F_624,k9_subset_1(A_623,C_619,D_621)) != k2_partfun1(C_619,B_620,E_622,k9_subset_1(A_623,C_619,D_621))
      | ~ m1_subset_1(F_624,k1_zfmisc_1(k2_zfmisc_1(D_621,B_620)))
      | ~ v1_funct_2(F_624,D_621,B_620)
      | ~ v1_funct_1(F_624)
      | ~ m1_subset_1(E_622,k1_zfmisc_1(k2_zfmisc_1(C_619,B_620)))
      | ~ v1_funct_2(E_622,C_619,B_620)
      | ~ v1_funct_1(E_622)
      | ~ m1_subset_1(D_621,k1_zfmisc_1(A_623))
      | v1_xboole_0(D_621)
      | ~ m1_subset_1(C_619,k1_zfmisc_1(A_623))
      | v1_xboole_0(C_619)
      | v1_xboole_0(B_620)
      | v1_xboole_0(A_623) ) ),
    inference(resolution,[status(thm)],[c_42,c_2434])).

tff(c_3223,plain,(
    ! [F_669,E_667,D_666,C_664,A_668,B_665] :
      ( k2_partfun1(k4_subset_1(A_668,C_664,D_666),B_665,k1_tmap_1(A_668,B_665,C_664,D_666,E_667,F_669),D_666) = F_669
      | ~ v1_funct_1(k1_tmap_1(A_668,B_665,C_664,D_666,E_667,F_669))
      | k2_partfun1(D_666,B_665,F_669,k9_subset_1(A_668,C_664,D_666)) != k2_partfun1(C_664,B_665,E_667,k9_subset_1(A_668,C_664,D_666))
      | ~ m1_subset_1(F_669,k1_zfmisc_1(k2_zfmisc_1(D_666,B_665)))
      | ~ v1_funct_2(F_669,D_666,B_665)
      | ~ v1_funct_1(F_669)
      | ~ m1_subset_1(E_667,k1_zfmisc_1(k2_zfmisc_1(C_664,B_665)))
      | ~ v1_funct_2(E_667,C_664,B_665)
      | ~ v1_funct_1(E_667)
      | ~ m1_subset_1(D_666,k1_zfmisc_1(A_668))
      | v1_xboole_0(D_666)
      | ~ m1_subset_1(C_664,k1_zfmisc_1(A_668))
      | v1_xboole_0(C_664)
      | v1_xboole_0(B_665)
      | v1_xboole_0(A_668) ) ),
    inference(resolution,[status(thm)],[c_44,c_2784])).

tff(c_3229,plain,(
    ! [A_668,C_664,E_667] :
      ( k2_partfun1(k4_subset_1(A_668,C_664,'#skF_4'),'#skF_2',k1_tmap_1(A_668,'#skF_2',C_664,'#skF_4',E_667,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_668,'#skF_2',C_664,'#skF_4',E_667,'#skF_6'))
      | k2_partfun1(C_664,'#skF_2',E_667,k9_subset_1(A_668,C_664,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_668,C_664,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_667,k1_zfmisc_1(k2_zfmisc_1(C_664,'#skF_2')))
      | ~ v1_funct_2(E_667,C_664,'#skF_2')
      | ~ v1_funct_1(E_667)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_668))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_664,k1_zfmisc_1(A_668))
      | v1_xboole_0(C_664)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_668) ) ),
    inference(resolution,[status(thm)],[c_50,c_3223])).

tff(c_3237,plain,(
    ! [A_668,C_664,E_667] :
      ( k2_partfun1(k4_subset_1(A_668,C_664,'#skF_4'),'#skF_2',k1_tmap_1(A_668,'#skF_2',C_664,'#skF_4',E_667,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_668,'#skF_2',C_664,'#skF_4',E_667,'#skF_6'))
      | k2_partfun1(C_664,'#skF_2',E_667,k9_subset_1(A_668,C_664,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_668,C_664,'#skF_4'))
      | ~ m1_subset_1(E_667,k1_zfmisc_1(k2_zfmisc_1(C_664,'#skF_2')))
      | ~ v1_funct_2(E_667,C_664,'#skF_2')
      | ~ v1_funct_1(E_667)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_668))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_664,k1_zfmisc_1(A_668))
      | v1_xboole_0(C_664)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_668) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1961,c_3229])).

tff(c_3558,plain,(
    ! [A_734,C_735,E_736] :
      ( k2_partfun1(k4_subset_1(A_734,C_735,'#skF_4'),'#skF_2',k1_tmap_1(A_734,'#skF_2',C_735,'#skF_4',E_736,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_734,'#skF_2',C_735,'#skF_4',E_736,'#skF_6'))
      | k2_partfun1(C_735,'#skF_2',E_736,k9_subset_1(A_734,C_735,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_734,C_735,'#skF_4'))
      | ~ m1_subset_1(E_736,k1_zfmisc_1(k2_zfmisc_1(C_735,'#skF_2')))
      | ~ v1_funct_2(E_736,C_735,'#skF_2')
      | ~ v1_funct_1(E_736)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_734))
      | ~ m1_subset_1(C_735,k1_zfmisc_1(A_734))
      | v1_xboole_0(C_735)
      | v1_xboole_0(A_734) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_3237])).

tff(c_3563,plain,(
    ! [A_734] :
      ( k2_partfun1(k4_subset_1(A_734,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_734,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_734,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_734,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_734,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_734))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_734))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_734) ) ),
    inference(resolution,[status(thm)],[c_56,c_3558])).

tff(c_3571,plain,(
    ! [A_734] :
      ( k2_partfun1(k4_subset_1(A_734,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_734,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_734,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_734,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_734,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_734))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_734))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_734) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1958,c_3563])).

tff(c_3597,plain,(
    ! [A_740] :
      ( k2_partfun1(k4_subset_1(A_740,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_740,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_740,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_740,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_740,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_740))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_740))
      | v1_xboole_0(A_740) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_3571])).

tff(c_122,plain,(
    ! [C_234,A_235,B_236] :
      ( v1_relat_1(C_234)
      | ~ m1_subset_1(C_234,k1_zfmisc_1(k2_zfmisc_1(A_235,B_236))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_129,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_122])).

tff(c_140,plain,(
    ! [B_240,A_241] :
      ( k3_xboole_0(B_240,A_241) = k1_xboole_0
      | k3_xboole_0(A_241,B_240) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_92,c_2])).

tff(c_143,plain,(
    ! [A_5] : k3_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_140])).

tff(c_180,plain,(
    ! [A_248,B_249] :
      ( k7_relat_1(A_248,B_249) = k1_xboole_0
      | ~ r1_xboole_0(B_249,k1_relat_1(A_248))
      | ~ v1_relat_1(A_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_769,plain,(
    ! [A_314,A_315] :
      ( k7_relat_1(A_314,A_315) = k1_xboole_0
      | ~ v1_relat_1(A_314)
      | k3_xboole_0(A_315,k1_relat_1(A_314)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_180])).

tff(c_780,plain,(
    ! [A_316] :
      ( k7_relat_1(A_316,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_316) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_769])).

tff(c_788,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_129,c_780])).

tff(c_130,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_122])).

tff(c_787,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_130,c_780])).

tff(c_172,plain,(
    ! [A_246,B_247] :
      ( r1_xboole_0(A_246,B_247)
      | ~ r1_subset_1(A_246,B_247)
      | v1_xboole_0(B_247)
      | v1_xboole_0(A_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_867,plain,(
    ! [A_325,B_326] :
      ( k3_xboole_0(A_325,B_326) = k1_xboole_0
      | ~ r1_subset_1(A_325,B_326)
      | v1_xboole_0(B_326)
      | v1_xboole_0(A_325) ) ),
    inference(resolution,[status(thm)],[c_172,c_2])).

tff(c_876,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_867])).

tff(c_883,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_66,c_876])).

tff(c_817,plain,(
    ! [A_317,B_318,C_319,D_320] :
      ( k2_partfun1(A_317,B_318,C_319,D_320) = k7_relat_1(C_319,D_320)
      | ~ m1_subset_1(C_319,k1_zfmisc_1(k2_zfmisc_1(A_317,B_318)))
      | ~ v1_funct_1(C_319) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_821,plain,(
    ! [D_320] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_320) = k7_relat_1('#skF_6',D_320)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_50,c_817])).

tff(c_827,plain,(
    ! [D_320] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_320) = k7_relat_1('#skF_6',D_320) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_821])).

tff(c_819,plain,(
    ! [D_320] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_320) = k7_relat_1('#skF_5',D_320)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_817])).

tff(c_824,plain,(
    ! [D_320] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_320) = k7_relat_1('#skF_5',D_320) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_819])).

tff(c_692,plain,(
    ! [A_306,B_307,C_308] :
      ( k9_subset_1(A_306,B_307,C_308) = k3_xboole_0(B_307,C_308)
      | ~ m1_subset_1(C_308,k1_zfmisc_1(A_306)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_704,plain,(
    ! [B_307] : k9_subset_1('#skF_1',B_307,'#skF_4') = k3_xboole_0(B_307,'#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_692])).

tff(c_48,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_119,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_734,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_704,c_704,c_119])).

tff(c_850,plain,(
    k7_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k7_relat_1('#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_827,c_824,c_734])).

tff(c_884,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) != k7_relat_1('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_883,c_883,c_850])).

tff(c_887,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_788,c_787,c_884])).

tff(c_888,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_946,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_888])).

tff(c_3608,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3597,c_946])).

tff(c_3622,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_2063,c_2180,c_1877,c_2064,c_2180,c_1877,c_2391,c_3608])).

tff(c_3624,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_3622])).

tff(c_3625,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_888])).

tff(c_6255,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6246,c_3625])).

tff(c_6266,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_4726,c_4686,c_3704,c_4727,c_4686,c_3704,c_4969,c_6255])).

tff(c_6268,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_6266])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:33:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.91/2.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.91/2.88  
% 7.91/2.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.91/2.89  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.91/2.89  
% 7.91/2.89  %Foreground sorts:
% 7.91/2.89  
% 7.91/2.89  
% 7.91/2.89  %Background operators:
% 7.91/2.89  
% 7.91/2.89  
% 7.91/2.89  %Foreground operators:
% 7.91/2.89  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 7.91/2.89  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.91/2.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.91/2.89  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.91/2.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.91/2.89  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 7.91/2.89  tff('#skF_5', type, '#skF_5': $i).
% 7.91/2.89  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.91/2.89  tff('#skF_6', type, '#skF_6': $i).
% 7.91/2.89  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.91/2.89  tff('#skF_2', type, '#skF_2': $i).
% 7.91/2.89  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.91/2.89  tff('#skF_3', type, '#skF_3': $i).
% 7.91/2.89  tff('#skF_1', type, '#skF_1': $i).
% 7.91/2.89  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.91/2.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.91/2.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.91/2.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.91/2.89  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.91/2.89  tff('#skF_4', type, '#skF_4': $i).
% 7.91/2.89  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.91/2.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.91/2.89  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 7.91/2.89  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.91/2.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.91/2.89  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.91/2.89  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.91/2.89  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.91/2.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.91/2.89  
% 8.17/2.91  tff(f_225, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 8.17/2.91  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.17/2.91  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 8.17/2.91  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.17/2.91  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 8.17/2.91  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 8.17/2.91  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 8.17/2.91  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 8.17/2.91  tff(f_183, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 8.17/2.91  tff(f_101, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 8.17/2.91  tff(f_149, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 8.17/2.91  tff(c_74, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.17/2.91  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.17/2.91  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.17/2.91  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.17/2.91  tff(c_891, plain, (![C_327, A_328, B_329]: (v1_relat_1(C_327) | ~m1_subset_1(C_327, k1_zfmisc_1(k2_zfmisc_1(A_328, B_329))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.17/2.91  tff(c_899, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_891])).
% 8.17/2.91  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.17/2.91  tff(c_84, plain, (![A_228, B_229]: (r1_xboole_0(A_228, B_229) | k3_xboole_0(A_228, B_229)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.17/2.91  tff(c_6, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.17/2.91  tff(c_92, plain, (![B_230, A_231]: (r1_xboole_0(B_230, A_231) | k3_xboole_0(A_231, B_230)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_84, c_6])).
% 8.17/2.91  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.17/2.91  tff(c_905, plain, (![B_330, A_331]: (k3_xboole_0(B_330, A_331)=k1_xboole_0 | k3_xboole_0(A_331, B_330)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_92, c_2])).
% 8.17/2.91  tff(c_908, plain, (![A_5]: (k3_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_905])).
% 8.17/2.91  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.17/2.91  tff(c_3632, plain, (![A_742, B_743]: (k7_relat_1(A_742, B_743)=k1_xboole_0 | ~r1_xboole_0(B_743, k1_relat_1(A_742)) | ~v1_relat_1(A_742))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.17/2.91  tff(c_4703, plain, (![A_851, A_852]: (k7_relat_1(A_851, A_852)=k1_xboole_0 | ~v1_relat_1(A_851) | k3_xboole_0(A_852, k1_relat_1(A_851))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_3632])).
% 8.17/2.91  tff(c_4719, plain, (![A_853]: (k7_relat_1(A_853, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_853))), inference(superposition, [status(thm), theory('equality')], [c_908, c_4703])).
% 8.17/2.91  tff(c_4726, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_899, c_4719])).
% 8.17/2.91  tff(c_70, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.17/2.91  tff(c_66, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.17/2.91  tff(c_62, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.17/2.91  tff(c_3643, plain, (![A_744, B_745]: (r1_xboole_0(A_744, B_745) | ~r1_subset_1(A_744, B_745) | v1_xboole_0(B_745) | v1_xboole_0(A_744))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.17/2.91  tff(c_4670, plain, (![A_849, B_850]: (k3_xboole_0(A_849, B_850)=k1_xboole_0 | ~r1_subset_1(A_849, B_850) | v1_xboole_0(B_850) | v1_xboole_0(A_849))), inference(resolution, [status(thm)], [c_3643, c_2])).
% 8.17/2.91  tff(c_4679, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_62, c_4670])).
% 8.17/2.91  tff(c_4686, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_70, c_66, c_4679])).
% 8.17/2.91  tff(c_3692, plain, (![A_752, B_753, C_754]: (k9_subset_1(A_752, B_753, C_754)=k3_xboole_0(B_753, C_754) | ~m1_subset_1(C_754, k1_zfmisc_1(A_752)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.17/2.91  tff(c_3704, plain, (![B_753]: (k9_subset_1('#skF_1', B_753, '#skF_4')=k3_xboole_0(B_753, '#skF_4'))), inference(resolution, [status(thm)], [c_64, c_3692])).
% 8.17/2.91  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.17/2.91  tff(c_898, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_891])).
% 8.17/2.91  tff(c_4727, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_898, c_4719])).
% 8.17/2.91  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.17/2.91  tff(c_58, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.17/2.91  tff(c_72, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.17/2.91  tff(c_54, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.17/2.91  tff(c_52, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.17/2.91  tff(c_4784, plain, (![F_859, E_857, B_855, D_856, A_858, C_854]: (v1_funct_1(k1_tmap_1(A_858, B_855, C_854, D_856, E_857, F_859)) | ~m1_subset_1(F_859, k1_zfmisc_1(k2_zfmisc_1(D_856, B_855))) | ~v1_funct_2(F_859, D_856, B_855) | ~v1_funct_1(F_859) | ~m1_subset_1(E_857, k1_zfmisc_1(k2_zfmisc_1(C_854, B_855))) | ~v1_funct_2(E_857, C_854, B_855) | ~v1_funct_1(E_857) | ~m1_subset_1(D_856, k1_zfmisc_1(A_858)) | v1_xboole_0(D_856) | ~m1_subset_1(C_854, k1_zfmisc_1(A_858)) | v1_xboole_0(C_854) | v1_xboole_0(B_855) | v1_xboole_0(A_858))), inference(cnfTransformation, [status(thm)], [f_183])).
% 8.17/2.91  tff(c_4788, plain, (![A_858, C_854, E_857]: (v1_funct_1(k1_tmap_1(A_858, '#skF_2', C_854, '#skF_4', E_857, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_857, k1_zfmisc_1(k2_zfmisc_1(C_854, '#skF_2'))) | ~v1_funct_2(E_857, C_854, '#skF_2') | ~v1_funct_1(E_857) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_858)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_854, k1_zfmisc_1(A_858)) | v1_xboole_0(C_854) | v1_xboole_0('#skF_2') | v1_xboole_0(A_858))), inference(resolution, [status(thm)], [c_50, c_4784])).
% 8.17/2.91  tff(c_4795, plain, (![A_858, C_854, E_857]: (v1_funct_1(k1_tmap_1(A_858, '#skF_2', C_854, '#skF_4', E_857, '#skF_6')) | ~m1_subset_1(E_857, k1_zfmisc_1(k2_zfmisc_1(C_854, '#skF_2'))) | ~v1_funct_2(E_857, C_854, '#skF_2') | ~v1_funct_1(E_857) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_858)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_854, k1_zfmisc_1(A_858)) | v1_xboole_0(C_854) | v1_xboole_0('#skF_2') | v1_xboole_0(A_858))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_4788])).
% 8.17/2.91  tff(c_4942, plain, (![A_881, C_882, E_883]: (v1_funct_1(k1_tmap_1(A_881, '#skF_2', C_882, '#skF_4', E_883, '#skF_6')) | ~m1_subset_1(E_883, k1_zfmisc_1(k2_zfmisc_1(C_882, '#skF_2'))) | ~v1_funct_2(E_883, C_882, '#skF_2') | ~v1_funct_1(E_883) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_881)) | ~m1_subset_1(C_882, k1_zfmisc_1(A_881)) | v1_xboole_0(C_882) | v1_xboole_0(A_881))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_4795])).
% 8.17/2.91  tff(c_4944, plain, (![A_881]: (v1_funct_1(k1_tmap_1(A_881, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_881)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_881)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_881))), inference(resolution, [status(thm)], [c_56, c_4942])).
% 8.17/2.91  tff(c_4949, plain, (![A_881]: (v1_funct_1(k1_tmap_1(A_881, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_881)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_881)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_881))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_4944])).
% 8.17/2.91  tff(c_4962, plain, (![A_885]: (v1_funct_1(k1_tmap_1(A_885, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_885)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_885)) | v1_xboole_0(A_885))), inference(negUnitSimplification, [status(thm)], [c_70, c_4949])).
% 8.17/2.91  tff(c_4965, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_68, c_4962])).
% 8.17/2.91  tff(c_4968, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_4965])).
% 8.17/2.91  tff(c_4969, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_74, c_4968])).
% 8.17/2.91  tff(c_4512, plain, (![A_833, B_834, C_835, D_836]: (k2_partfun1(A_833, B_834, C_835, D_836)=k7_relat_1(C_835, D_836) | ~m1_subset_1(C_835, k1_zfmisc_1(k2_zfmisc_1(A_833, B_834))) | ~v1_funct_1(C_835))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.17/2.91  tff(c_4514, plain, (![D_836]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_836)=k7_relat_1('#skF_5', D_836) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_4512])).
% 8.17/2.91  tff(c_4519, plain, (![D_836]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_836)=k7_relat_1('#skF_5', D_836))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_4514])).
% 8.17/2.91  tff(c_4516, plain, (![D_836]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_836)=k7_relat_1('#skF_6', D_836) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_50, c_4512])).
% 8.17/2.91  tff(c_4522, plain, (![D_836]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_836)=k7_relat_1('#skF_6', D_836))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_4516])).
% 8.17/2.91  tff(c_44, plain, (![B_161, C_162, A_160, E_164, F_165, D_163]: (v1_funct_2(k1_tmap_1(A_160, B_161, C_162, D_163, E_164, F_165), k4_subset_1(A_160, C_162, D_163), B_161) | ~m1_subset_1(F_165, k1_zfmisc_1(k2_zfmisc_1(D_163, B_161))) | ~v1_funct_2(F_165, D_163, B_161) | ~v1_funct_1(F_165) | ~m1_subset_1(E_164, k1_zfmisc_1(k2_zfmisc_1(C_162, B_161))) | ~v1_funct_2(E_164, C_162, B_161) | ~v1_funct_1(E_164) | ~m1_subset_1(D_163, k1_zfmisc_1(A_160)) | v1_xboole_0(D_163) | ~m1_subset_1(C_162, k1_zfmisc_1(A_160)) | v1_xboole_0(C_162) | v1_xboole_0(B_161) | v1_xboole_0(A_160))), inference(cnfTransformation, [status(thm)], [f_183])).
% 8.17/2.91  tff(c_42, plain, (![B_161, C_162, A_160, E_164, F_165, D_163]: (m1_subset_1(k1_tmap_1(A_160, B_161, C_162, D_163, E_164, F_165), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_160, C_162, D_163), B_161))) | ~m1_subset_1(F_165, k1_zfmisc_1(k2_zfmisc_1(D_163, B_161))) | ~v1_funct_2(F_165, D_163, B_161) | ~v1_funct_1(F_165) | ~m1_subset_1(E_164, k1_zfmisc_1(k2_zfmisc_1(C_162, B_161))) | ~v1_funct_2(E_164, C_162, B_161) | ~v1_funct_1(E_164) | ~m1_subset_1(D_163, k1_zfmisc_1(A_160)) | v1_xboole_0(D_163) | ~m1_subset_1(C_162, k1_zfmisc_1(A_160)) | v1_xboole_0(C_162) | v1_xboole_0(B_161) | v1_xboole_0(A_160))), inference(cnfTransformation, [status(thm)], [f_183])).
% 8.17/2.91  tff(c_5012, plain, (![E_893, D_897, C_896, F_895, A_892, B_894]: (k2_partfun1(k4_subset_1(A_892, C_896, D_897), B_894, k1_tmap_1(A_892, B_894, C_896, D_897, E_893, F_895), C_896)=E_893 | ~m1_subset_1(k1_tmap_1(A_892, B_894, C_896, D_897, E_893, F_895), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_892, C_896, D_897), B_894))) | ~v1_funct_2(k1_tmap_1(A_892, B_894, C_896, D_897, E_893, F_895), k4_subset_1(A_892, C_896, D_897), B_894) | ~v1_funct_1(k1_tmap_1(A_892, B_894, C_896, D_897, E_893, F_895)) | k2_partfun1(D_897, B_894, F_895, k9_subset_1(A_892, C_896, D_897))!=k2_partfun1(C_896, B_894, E_893, k9_subset_1(A_892, C_896, D_897)) | ~m1_subset_1(F_895, k1_zfmisc_1(k2_zfmisc_1(D_897, B_894))) | ~v1_funct_2(F_895, D_897, B_894) | ~v1_funct_1(F_895) | ~m1_subset_1(E_893, k1_zfmisc_1(k2_zfmisc_1(C_896, B_894))) | ~v1_funct_2(E_893, C_896, B_894) | ~v1_funct_1(E_893) | ~m1_subset_1(D_897, k1_zfmisc_1(A_892)) | v1_xboole_0(D_897) | ~m1_subset_1(C_896, k1_zfmisc_1(A_892)) | v1_xboole_0(C_896) | v1_xboole_0(B_894) | v1_xboole_0(A_892))), inference(cnfTransformation, [status(thm)], [f_149])).
% 8.17/2.91  tff(c_5587, plain, (![A_1020, B_1017, C_1016, F_1021, D_1018, E_1019]: (k2_partfun1(k4_subset_1(A_1020, C_1016, D_1018), B_1017, k1_tmap_1(A_1020, B_1017, C_1016, D_1018, E_1019, F_1021), C_1016)=E_1019 | ~v1_funct_2(k1_tmap_1(A_1020, B_1017, C_1016, D_1018, E_1019, F_1021), k4_subset_1(A_1020, C_1016, D_1018), B_1017) | ~v1_funct_1(k1_tmap_1(A_1020, B_1017, C_1016, D_1018, E_1019, F_1021)) | k2_partfun1(D_1018, B_1017, F_1021, k9_subset_1(A_1020, C_1016, D_1018))!=k2_partfun1(C_1016, B_1017, E_1019, k9_subset_1(A_1020, C_1016, D_1018)) | ~m1_subset_1(F_1021, k1_zfmisc_1(k2_zfmisc_1(D_1018, B_1017))) | ~v1_funct_2(F_1021, D_1018, B_1017) | ~v1_funct_1(F_1021) | ~m1_subset_1(E_1019, k1_zfmisc_1(k2_zfmisc_1(C_1016, B_1017))) | ~v1_funct_2(E_1019, C_1016, B_1017) | ~v1_funct_1(E_1019) | ~m1_subset_1(D_1018, k1_zfmisc_1(A_1020)) | v1_xboole_0(D_1018) | ~m1_subset_1(C_1016, k1_zfmisc_1(A_1020)) | v1_xboole_0(C_1016) | v1_xboole_0(B_1017) | v1_xboole_0(A_1020))), inference(resolution, [status(thm)], [c_42, c_5012])).
% 8.17/2.91  tff(c_5808, plain, (![F_1056, E_1054, D_1053, C_1051, A_1055, B_1052]: (k2_partfun1(k4_subset_1(A_1055, C_1051, D_1053), B_1052, k1_tmap_1(A_1055, B_1052, C_1051, D_1053, E_1054, F_1056), C_1051)=E_1054 | ~v1_funct_1(k1_tmap_1(A_1055, B_1052, C_1051, D_1053, E_1054, F_1056)) | k2_partfun1(D_1053, B_1052, F_1056, k9_subset_1(A_1055, C_1051, D_1053))!=k2_partfun1(C_1051, B_1052, E_1054, k9_subset_1(A_1055, C_1051, D_1053)) | ~m1_subset_1(F_1056, k1_zfmisc_1(k2_zfmisc_1(D_1053, B_1052))) | ~v1_funct_2(F_1056, D_1053, B_1052) | ~v1_funct_1(F_1056) | ~m1_subset_1(E_1054, k1_zfmisc_1(k2_zfmisc_1(C_1051, B_1052))) | ~v1_funct_2(E_1054, C_1051, B_1052) | ~v1_funct_1(E_1054) | ~m1_subset_1(D_1053, k1_zfmisc_1(A_1055)) | v1_xboole_0(D_1053) | ~m1_subset_1(C_1051, k1_zfmisc_1(A_1055)) | v1_xboole_0(C_1051) | v1_xboole_0(B_1052) | v1_xboole_0(A_1055))), inference(resolution, [status(thm)], [c_44, c_5587])).
% 8.17/2.91  tff(c_5814, plain, (![A_1055, C_1051, E_1054]: (k2_partfun1(k4_subset_1(A_1055, C_1051, '#skF_4'), '#skF_2', k1_tmap_1(A_1055, '#skF_2', C_1051, '#skF_4', E_1054, '#skF_6'), C_1051)=E_1054 | ~v1_funct_1(k1_tmap_1(A_1055, '#skF_2', C_1051, '#skF_4', E_1054, '#skF_6')) | k2_partfun1(C_1051, '#skF_2', E_1054, k9_subset_1(A_1055, C_1051, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_1055, C_1051, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1054, k1_zfmisc_1(k2_zfmisc_1(C_1051, '#skF_2'))) | ~v1_funct_2(E_1054, C_1051, '#skF_2') | ~v1_funct_1(E_1054) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1055)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1051, k1_zfmisc_1(A_1055)) | v1_xboole_0(C_1051) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1055))), inference(resolution, [status(thm)], [c_50, c_5808])).
% 8.17/2.91  tff(c_5822, plain, (![A_1055, C_1051, E_1054]: (k2_partfun1(k4_subset_1(A_1055, C_1051, '#skF_4'), '#skF_2', k1_tmap_1(A_1055, '#skF_2', C_1051, '#skF_4', E_1054, '#skF_6'), C_1051)=E_1054 | ~v1_funct_1(k1_tmap_1(A_1055, '#skF_2', C_1051, '#skF_4', E_1054, '#skF_6')) | k2_partfun1(C_1051, '#skF_2', E_1054, k9_subset_1(A_1055, C_1051, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1055, C_1051, '#skF_4')) | ~m1_subset_1(E_1054, k1_zfmisc_1(k2_zfmisc_1(C_1051, '#skF_2'))) | ~v1_funct_2(E_1054, C_1051, '#skF_2') | ~v1_funct_1(E_1054) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1055)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1051, k1_zfmisc_1(A_1055)) | v1_xboole_0(C_1051) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1055))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_4522, c_5814])).
% 8.17/2.91  tff(c_6210, plain, (![A_1127, C_1128, E_1129]: (k2_partfun1(k4_subset_1(A_1127, C_1128, '#skF_4'), '#skF_2', k1_tmap_1(A_1127, '#skF_2', C_1128, '#skF_4', E_1129, '#skF_6'), C_1128)=E_1129 | ~v1_funct_1(k1_tmap_1(A_1127, '#skF_2', C_1128, '#skF_4', E_1129, '#skF_6')) | k2_partfun1(C_1128, '#skF_2', E_1129, k9_subset_1(A_1127, C_1128, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1127, C_1128, '#skF_4')) | ~m1_subset_1(E_1129, k1_zfmisc_1(k2_zfmisc_1(C_1128, '#skF_2'))) | ~v1_funct_2(E_1129, C_1128, '#skF_2') | ~v1_funct_1(E_1129) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1127)) | ~m1_subset_1(C_1128, k1_zfmisc_1(A_1127)) | v1_xboole_0(C_1128) | v1_xboole_0(A_1127))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_5822])).
% 8.17/2.91  tff(c_6215, plain, (![A_1127]: (k2_partfun1(k4_subset_1(A_1127, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1127, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1127, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_1127, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1127, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1127)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1127)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1127))), inference(resolution, [status(thm)], [c_56, c_6210])).
% 8.17/2.91  tff(c_6223, plain, (![A_1127]: (k2_partfun1(k4_subset_1(A_1127, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1127, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1127, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1127, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1127, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1127)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1127)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1127))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_4519, c_6215])).
% 8.17/2.91  tff(c_6246, plain, (![A_1130]: (k2_partfun1(k4_subset_1(A_1130, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1130, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1130, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1130, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1130, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1130)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1130)) | v1_xboole_0(A_1130))), inference(negUnitSimplification, [status(thm)], [c_70, c_6223])).
% 8.17/2.91  tff(c_948, plain, (![A_340, B_341]: (k7_relat_1(A_340, B_341)=k1_xboole_0 | ~r1_xboole_0(B_341, k1_relat_1(A_340)) | ~v1_relat_1(A_340))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.17/2.91  tff(c_2040, plain, (![A_456, A_457]: (k7_relat_1(A_456, A_457)=k1_xboole_0 | ~v1_relat_1(A_456) | k3_xboole_0(A_457, k1_relat_1(A_456))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_948])).
% 8.17/2.91  tff(c_2056, plain, (![A_458]: (k7_relat_1(A_458, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_458))), inference(superposition, [status(thm), theory('equality')], [c_908, c_2040])).
% 8.17/2.91  tff(c_2063, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_899, c_2056])).
% 8.17/2.91  tff(c_968, plain, (![A_344, B_345]: (r1_xboole_0(A_344, B_345) | ~r1_subset_1(A_344, B_345) | v1_xboole_0(B_345) | v1_xboole_0(A_344))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.17/2.91  tff(c_2164, plain, (![A_464, B_465]: (k3_xboole_0(A_464, B_465)=k1_xboole_0 | ~r1_subset_1(A_464, B_465) | v1_xboole_0(B_465) | v1_xboole_0(A_464))), inference(resolution, [status(thm)], [c_968, c_2])).
% 8.17/2.91  tff(c_2173, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_62, c_2164])).
% 8.17/2.91  tff(c_2180, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_70, c_66, c_2173])).
% 8.17/2.91  tff(c_1865, plain, (![A_437, B_438, C_439]: (k9_subset_1(A_437, B_438, C_439)=k3_xboole_0(B_438, C_439) | ~m1_subset_1(C_439, k1_zfmisc_1(A_437)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.17/2.91  tff(c_1877, plain, (![B_438]: (k9_subset_1('#skF_1', B_438, '#skF_4')=k3_xboole_0(B_438, '#skF_4'))), inference(resolution, [status(thm)], [c_64, c_1865])).
% 8.17/2.91  tff(c_2064, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_898, c_2056])).
% 8.17/2.91  tff(c_2268, plain, (![A_476, B_473, C_472, D_474, E_475, F_477]: (v1_funct_1(k1_tmap_1(A_476, B_473, C_472, D_474, E_475, F_477)) | ~m1_subset_1(F_477, k1_zfmisc_1(k2_zfmisc_1(D_474, B_473))) | ~v1_funct_2(F_477, D_474, B_473) | ~v1_funct_1(F_477) | ~m1_subset_1(E_475, k1_zfmisc_1(k2_zfmisc_1(C_472, B_473))) | ~v1_funct_2(E_475, C_472, B_473) | ~v1_funct_1(E_475) | ~m1_subset_1(D_474, k1_zfmisc_1(A_476)) | v1_xboole_0(D_474) | ~m1_subset_1(C_472, k1_zfmisc_1(A_476)) | v1_xboole_0(C_472) | v1_xboole_0(B_473) | v1_xboole_0(A_476))), inference(cnfTransformation, [status(thm)], [f_183])).
% 8.17/2.91  tff(c_2272, plain, (![A_476, C_472, E_475]: (v1_funct_1(k1_tmap_1(A_476, '#skF_2', C_472, '#skF_4', E_475, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_475, k1_zfmisc_1(k2_zfmisc_1(C_472, '#skF_2'))) | ~v1_funct_2(E_475, C_472, '#skF_2') | ~v1_funct_1(E_475) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_476)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_472, k1_zfmisc_1(A_476)) | v1_xboole_0(C_472) | v1_xboole_0('#skF_2') | v1_xboole_0(A_476))), inference(resolution, [status(thm)], [c_50, c_2268])).
% 8.17/2.91  tff(c_2279, plain, (![A_476, C_472, E_475]: (v1_funct_1(k1_tmap_1(A_476, '#skF_2', C_472, '#skF_4', E_475, '#skF_6')) | ~m1_subset_1(E_475, k1_zfmisc_1(k2_zfmisc_1(C_472, '#skF_2'))) | ~v1_funct_2(E_475, C_472, '#skF_2') | ~v1_funct_1(E_475) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_476)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_472, k1_zfmisc_1(A_476)) | v1_xboole_0(C_472) | v1_xboole_0('#skF_2') | v1_xboole_0(A_476))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_2272])).
% 8.17/2.91  tff(c_2364, plain, (![A_493, C_494, E_495]: (v1_funct_1(k1_tmap_1(A_493, '#skF_2', C_494, '#skF_4', E_495, '#skF_6')) | ~m1_subset_1(E_495, k1_zfmisc_1(k2_zfmisc_1(C_494, '#skF_2'))) | ~v1_funct_2(E_495, C_494, '#skF_2') | ~v1_funct_1(E_495) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_493)) | ~m1_subset_1(C_494, k1_zfmisc_1(A_493)) | v1_xboole_0(C_494) | v1_xboole_0(A_493))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_2279])).
% 8.17/2.91  tff(c_2366, plain, (![A_493]: (v1_funct_1(k1_tmap_1(A_493, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_493)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_493)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_493))), inference(resolution, [status(thm)], [c_56, c_2364])).
% 8.17/2.91  tff(c_2371, plain, (![A_493]: (v1_funct_1(k1_tmap_1(A_493, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_493)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_493)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_493))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_2366])).
% 8.17/2.91  tff(c_2384, plain, (![A_497]: (v1_funct_1(k1_tmap_1(A_497, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_497)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_497)) | v1_xboole_0(A_497))), inference(negUnitSimplification, [status(thm)], [c_70, c_2371])).
% 8.17/2.91  tff(c_2387, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_68, c_2384])).
% 8.17/2.91  tff(c_2390, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2387])).
% 8.17/2.91  tff(c_2391, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_74, c_2390])).
% 8.17/2.91  tff(c_1951, plain, (![A_448, B_449, C_450, D_451]: (k2_partfun1(A_448, B_449, C_450, D_451)=k7_relat_1(C_450, D_451) | ~m1_subset_1(C_450, k1_zfmisc_1(k2_zfmisc_1(A_448, B_449))) | ~v1_funct_1(C_450))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.17/2.91  tff(c_1953, plain, (![D_451]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_451)=k7_relat_1('#skF_5', D_451) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_1951])).
% 8.17/2.91  tff(c_1958, plain, (![D_451]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_451)=k7_relat_1('#skF_5', D_451))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1953])).
% 8.17/2.91  tff(c_1955, plain, (![D_451]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_451)=k7_relat_1('#skF_6', D_451) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_50, c_1951])).
% 8.17/2.91  tff(c_1961, plain, (![D_451]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_451)=k7_relat_1('#skF_6', D_451))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1955])).
% 8.17/2.91  tff(c_2434, plain, (![D_509, A_504, F_507, E_505, C_508, B_506]: (k2_partfun1(k4_subset_1(A_504, C_508, D_509), B_506, k1_tmap_1(A_504, B_506, C_508, D_509, E_505, F_507), D_509)=F_507 | ~m1_subset_1(k1_tmap_1(A_504, B_506, C_508, D_509, E_505, F_507), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_504, C_508, D_509), B_506))) | ~v1_funct_2(k1_tmap_1(A_504, B_506, C_508, D_509, E_505, F_507), k4_subset_1(A_504, C_508, D_509), B_506) | ~v1_funct_1(k1_tmap_1(A_504, B_506, C_508, D_509, E_505, F_507)) | k2_partfun1(D_509, B_506, F_507, k9_subset_1(A_504, C_508, D_509))!=k2_partfun1(C_508, B_506, E_505, k9_subset_1(A_504, C_508, D_509)) | ~m1_subset_1(F_507, k1_zfmisc_1(k2_zfmisc_1(D_509, B_506))) | ~v1_funct_2(F_507, D_509, B_506) | ~v1_funct_1(F_507) | ~m1_subset_1(E_505, k1_zfmisc_1(k2_zfmisc_1(C_508, B_506))) | ~v1_funct_2(E_505, C_508, B_506) | ~v1_funct_1(E_505) | ~m1_subset_1(D_509, k1_zfmisc_1(A_504)) | v1_xboole_0(D_509) | ~m1_subset_1(C_508, k1_zfmisc_1(A_504)) | v1_xboole_0(C_508) | v1_xboole_0(B_506) | v1_xboole_0(A_504))), inference(cnfTransformation, [status(thm)], [f_149])).
% 8.17/2.91  tff(c_2784, plain, (![B_620, E_622, D_621, A_623, C_619, F_624]: (k2_partfun1(k4_subset_1(A_623, C_619, D_621), B_620, k1_tmap_1(A_623, B_620, C_619, D_621, E_622, F_624), D_621)=F_624 | ~v1_funct_2(k1_tmap_1(A_623, B_620, C_619, D_621, E_622, F_624), k4_subset_1(A_623, C_619, D_621), B_620) | ~v1_funct_1(k1_tmap_1(A_623, B_620, C_619, D_621, E_622, F_624)) | k2_partfun1(D_621, B_620, F_624, k9_subset_1(A_623, C_619, D_621))!=k2_partfun1(C_619, B_620, E_622, k9_subset_1(A_623, C_619, D_621)) | ~m1_subset_1(F_624, k1_zfmisc_1(k2_zfmisc_1(D_621, B_620))) | ~v1_funct_2(F_624, D_621, B_620) | ~v1_funct_1(F_624) | ~m1_subset_1(E_622, k1_zfmisc_1(k2_zfmisc_1(C_619, B_620))) | ~v1_funct_2(E_622, C_619, B_620) | ~v1_funct_1(E_622) | ~m1_subset_1(D_621, k1_zfmisc_1(A_623)) | v1_xboole_0(D_621) | ~m1_subset_1(C_619, k1_zfmisc_1(A_623)) | v1_xboole_0(C_619) | v1_xboole_0(B_620) | v1_xboole_0(A_623))), inference(resolution, [status(thm)], [c_42, c_2434])).
% 8.17/2.91  tff(c_3223, plain, (![F_669, E_667, D_666, C_664, A_668, B_665]: (k2_partfun1(k4_subset_1(A_668, C_664, D_666), B_665, k1_tmap_1(A_668, B_665, C_664, D_666, E_667, F_669), D_666)=F_669 | ~v1_funct_1(k1_tmap_1(A_668, B_665, C_664, D_666, E_667, F_669)) | k2_partfun1(D_666, B_665, F_669, k9_subset_1(A_668, C_664, D_666))!=k2_partfun1(C_664, B_665, E_667, k9_subset_1(A_668, C_664, D_666)) | ~m1_subset_1(F_669, k1_zfmisc_1(k2_zfmisc_1(D_666, B_665))) | ~v1_funct_2(F_669, D_666, B_665) | ~v1_funct_1(F_669) | ~m1_subset_1(E_667, k1_zfmisc_1(k2_zfmisc_1(C_664, B_665))) | ~v1_funct_2(E_667, C_664, B_665) | ~v1_funct_1(E_667) | ~m1_subset_1(D_666, k1_zfmisc_1(A_668)) | v1_xboole_0(D_666) | ~m1_subset_1(C_664, k1_zfmisc_1(A_668)) | v1_xboole_0(C_664) | v1_xboole_0(B_665) | v1_xboole_0(A_668))), inference(resolution, [status(thm)], [c_44, c_2784])).
% 8.17/2.91  tff(c_3229, plain, (![A_668, C_664, E_667]: (k2_partfun1(k4_subset_1(A_668, C_664, '#skF_4'), '#skF_2', k1_tmap_1(A_668, '#skF_2', C_664, '#skF_4', E_667, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_668, '#skF_2', C_664, '#skF_4', E_667, '#skF_6')) | k2_partfun1(C_664, '#skF_2', E_667, k9_subset_1(A_668, C_664, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_668, C_664, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_667, k1_zfmisc_1(k2_zfmisc_1(C_664, '#skF_2'))) | ~v1_funct_2(E_667, C_664, '#skF_2') | ~v1_funct_1(E_667) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_668)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_664, k1_zfmisc_1(A_668)) | v1_xboole_0(C_664) | v1_xboole_0('#skF_2') | v1_xboole_0(A_668))), inference(resolution, [status(thm)], [c_50, c_3223])).
% 8.17/2.91  tff(c_3237, plain, (![A_668, C_664, E_667]: (k2_partfun1(k4_subset_1(A_668, C_664, '#skF_4'), '#skF_2', k1_tmap_1(A_668, '#skF_2', C_664, '#skF_4', E_667, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_668, '#skF_2', C_664, '#skF_4', E_667, '#skF_6')) | k2_partfun1(C_664, '#skF_2', E_667, k9_subset_1(A_668, C_664, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_668, C_664, '#skF_4')) | ~m1_subset_1(E_667, k1_zfmisc_1(k2_zfmisc_1(C_664, '#skF_2'))) | ~v1_funct_2(E_667, C_664, '#skF_2') | ~v1_funct_1(E_667) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_668)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_664, k1_zfmisc_1(A_668)) | v1_xboole_0(C_664) | v1_xboole_0('#skF_2') | v1_xboole_0(A_668))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1961, c_3229])).
% 8.17/2.91  tff(c_3558, plain, (![A_734, C_735, E_736]: (k2_partfun1(k4_subset_1(A_734, C_735, '#skF_4'), '#skF_2', k1_tmap_1(A_734, '#skF_2', C_735, '#skF_4', E_736, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_734, '#skF_2', C_735, '#skF_4', E_736, '#skF_6')) | k2_partfun1(C_735, '#skF_2', E_736, k9_subset_1(A_734, C_735, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_734, C_735, '#skF_4')) | ~m1_subset_1(E_736, k1_zfmisc_1(k2_zfmisc_1(C_735, '#skF_2'))) | ~v1_funct_2(E_736, C_735, '#skF_2') | ~v1_funct_1(E_736) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_734)) | ~m1_subset_1(C_735, k1_zfmisc_1(A_734)) | v1_xboole_0(C_735) | v1_xboole_0(A_734))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_3237])).
% 8.17/2.91  tff(c_3563, plain, (![A_734]: (k2_partfun1(k4_subset_1(A_734, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_734, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_734, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_734, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_734, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_734)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_734)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_734))), inference(resolution, [status(thm)], [c_56, c_3558])).
% 8.17/2.91  tff(c_3571, plain, (![A_734]: (k2_partfun1(k4_subset_1(A_734, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_734, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_734, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_734, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_734, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_734)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_734)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_734))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1958, c_3563])).
% 8.17/2.91  tff(c_3597, plain, (![A_740]: (k2_partfun1(k4_subset_1(A_740, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_740, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_740, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_740, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_740, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_740)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_740)) | v1_xboole_0(A_740))), inference(negUnitSimplification, [status(thm)], [c_70, c_3571])).
% 8.17/2.91  tff(c_122, plain, (![C_234, A_235, B_236]: (v1_relat_1(C_234) | ~m1_subset_1(C_234, k1_zfmisc_1(k2_zfmisc_1(A_235, B_236))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.17/2.91  tff(c_129, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_122])).
% 8.17/2.91  tff(c_140, plain, (![B_240, A_241]: (k3_xboole_0(B_240, A_241)=k1_xboole_0 | k3_xboole_0(A_241, B_240)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_92, c_2])).
% 8.17/2.91  tff(c_143, plain, (![A_5]: (k3_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_140])).
% 8.17/2.91  tff(c_180, plain, (![A_248, B_249]: (k7_relat_1(A_248, B_249)=k1_xboole_0 | ~r1_xboole_0(B_249, k1_relat_1(A_248)) | ~v1_relat_1(A_248))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.17/2.91  tff(c_769, plain, (![A_314, A_315]: (k7_relat_1(A_314, A_315)=k1_xboole_0 | ~v1_relat_1(A_314) | k3_xboole_0(A_315, k1_relat_1(A_314))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_180])).
% 8.17/2.91  tff(c_780, plain, (![A_316]: (k7_relat_1(A_316, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_316))), inference(superposition, [status(thm), theory('equality')], [c_143, c_769])).
% 8.17/2.91  tff(c_788, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_129, c_780])).
% 8.17/2.91  tff(c_130, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_122])).
% 8.17/2.91  tff(c_787, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_130, c_780])).
% 8.17/2.91  tff(c_172, plain, (![A_246, B_247]: (r1_xboole_0(A_246, B_247) | ~r1_subset_1(A_246, B_247) | v1_xboole_0(B_247) | v1_xboole_0(A_246))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.17/2.91  tff(c_867, plain, (![A_325, B_326]: (k3_xboole_0(A_325, B_326)=k1_xboole_0 | ~r1_subset_1(A_325, B_326) | v1_xboole_0(B_326) | v1_xboole_0(A_325))), inference(resolution, [status(thm)], [c_172, c_2])).
% 8.17/2.91  tff(c_876, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_62, c_867])).
% 8.17/2.91  tff(c_883, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_70, c_66, c_876])).
% 8.17/2.91  tff(c_817, plain, (![A_317, B_318, C_319, D_320]: (k2_partfun1(A_317, B_318, C_319, D_320)=k7_relat_1(C_319, D_320) | ~m1_subset_1(C_319, k1_zfmisc_1(k2_zfmisc_1(A_317, B_318))) | ~v1_funct_1(C_319))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.17/2.91  tff(c_821, plain, (![D_320]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_320)=k7_relat_1('#skF_6', D_320) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_50, c_817])).
% 8.17/2.91  tff(c_827, plain, (![D_320]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_320)=k7_relat_1('#skF_6', D_320))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_821])).
% 8.17/2.91  tff(c_819, plain, (![D_320]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_320)=k7_relat_1('#skF_5', D_320) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_817])).
% 8.17/2.91  tff(c_824, plain, (![D_320]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_320)=k7_relat_1('#skF_5', D_320))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_819])).
% 8.17/2.91  tff(c_692, plain, (![A_306, B_307, C_308]: (k9_subset_1(A_306, B_307, C_308)=k3_xboole_0(B_307, C_308) | ~m1_subset_1(C_308, k1_zfmisc_1(A_306)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.17/2.91  tff(c_704, plain, (![B_307]: (k9_subset_1('#skF_1', B_307, '#skF_4')=k3_xboole_0(B_307, '#skF_4'))), inference(resolution, [status(thm)], [c_64, c_692])).
% 8.17/2.91  tff(c_48, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.17/2.91  tff(c_119, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_48])).
% 8.17/2.91  tff(c_734, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_704, c_704, c_119])).
% 8.17/2.91  tff(c_850, plain, (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_827, c_824, c_734])).
% 8.17/2.91  tff(c_884, plain, (k7_relat_1('#skF_5', k1_xboole_0)!=k7_relat_1('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_883, c_883, c_850])).
% 8.17/2.91  tff(c_887, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_788, c_787, c_884])).
% 8.17/2.91  tff(c_888, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_48])).
% 8.17/2.91  tff(c_946, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_888])).
% 8.17/2.91  tff(c_3608, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3597, c_946])).
% 8.17/2.91  tff(c_3622, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_2063, c_2180, c_1877, c_2064, c_2180, c_1877, c_2391, c_3608])).
% 8.17/2.91  tff(c_3624, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_3622])).
% 8.17/2.91  tff(c_3625, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_888])).
% 8.17/2.91  tff(c_6255, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6246, c_3625])).
% 8.17/2.91  tff(c_6266, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_4726, c_4686, c_3704, c_4727, c_4686, c_3704, c_4969, c_6255])).
% 8.17/2.91  tff(c_6268, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_6266])).
% 8.17/2.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.17/2.91  
% 8.17/2.91  Inference rules
% 8.17/2.91  ----------------------
% 8.17/2.91  #Ref     : 0
% 8.17/2.91  #Sup     : 1286
% 8.17/2.91  #Fact    : 0
% 8.17/2.91  #Define  : 0
% 8.17/2.91  #Split   : 44
% 8.17/2.91  #Chain   : 0
% 8.17/2.91  #Close   : 0
% 8.17/2.91  
% 8.17/2.91  Ordering : KBO
% 8.17/2.91  
% 8.17/2.91  Simplification rules
% 8.17/2.91  ----------------------
% 8.17/2.91  #Subsume      : 123
% 8.17/2.91  #Demod        : 847
% 8.17/2.91  #Tautology    : 662
% 8.17/2.91  #SimpNegUnit  : 295
% 8.17/2.91  #BackRed      : 14
% 8.17/2.91  
% 8.17/2.91  #Partial instantiations: 0
% 8.17/2.91  #Strategies tried      : 1
% 8.17/2.91  
% 8.17/2.91  Timing (in seconds)
% 8.17/2.91  ----------------------
% 8.17/2.92  Preprocessing        : 0.41
% 8.17/2.92  Parsing              : 0.21
% 8.17/2.92  CNF conversion       : 0.05
% 8.17/2.92  Main loop            : 1.72
% 8.17/2.92  Inferencing          : 0.60
% 8.17/2.92  Reduction            : 0.57
% 8.17/2.92  Demodulation         : 0.41
% 8.17/2.92  BG Simplification    : 0.06
% 8.17/2.92  Subsumption          : 0.37
% 8.17/2.92  Abstraction          : 0.07
% 8.17/2.92  MUC search           : 0.00
% 8.17/2.92  Cooper               : 0.00
% 8.17/2.92  Total                : 2.19
% 8.17/2.92  Index Insertion      : 0.00
% 8.17/2.92  Index Deletion       : 0.00
% 8.17/2.92  Index Matching       : 0.00
% 8.17/2.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
