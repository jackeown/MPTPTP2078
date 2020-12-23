%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:08 EST 2020

% Result     : Theorem 7.92s
% Output     : CNFRefutation 8.09s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 593 expanded)
%              Number of leaves         :   43 ( 234 expanded)
%              Depth                    :   12
%              Number of atoms          :  608 (2643 expanded)
%              Number of equality atoms :  125 ( 631 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tmap_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_46,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tmap_1)).

tff(f_101,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tmap_1)).

tff(c_76,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_70,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_1292,plain,(
    ! [C_362,A_363,B_364] :
      ( v1_relat_1(C_362)
      | ~ m1_subset_1(C_362,k1_zfmisc_1(k2_zfmisc_1(A_363,B_364))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1299,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_1292])).

tff(c_8,plain,(
    ! [B_5,A_4] : k2_tarski(B_5,A_4) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_118,plain,(
    ! [A_230,B_231] : k1_setfam_1(k2_tarski(A_230,B_231)) = k3_xboole_0(A_230,B_231) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_138,plain,(
    ! [B_234,A_235] : k1_setfam_1(k2_tarski(B_234,A_235)) = k3_xboole_0(A_235,B_234) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_118])).

tff(c_14,plain,(
    ! [A_12,B_13] : k1_setfam_1(k2_tarski(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1204,plain,(
    ! [B_359,A_360] : k3_xboole_0(B_359,A_360) = k3_xboole_0(A_360,B_359) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_14])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1220,plain,(
    ! [A_360] : k3_xboole_0(k1_xboole_0,A_360) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1204,c_6])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_3818,plain,(
    ! [A_760,B_761] :
      ( k7_relat_1(A_760,B_761) = k1_xboole_0
      | ~ r1_xboole_0(B_761,k1_relat_1(A_760))
      | ~ v1_relat_1(A_760) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4695,plain,(
    ! [A_864,A_865] :
      ( k7_relat_1(A_864,A_865) = k1_xboole_0
      | ~ v1_relat_1(A_864)
      | k3_xboole_0(A_865,k1_relat_1(A_864)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_3818])).

tff(c_4719,plain,(
    ! [A_866] :
      ( k7_relat_1(A_866,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_866) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1220,c_4695])).

tff(c_4727,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1299,c_4719])).

tff(c_72,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_144,plain,(
    ! [B_234,A_235] : k3_xboole_0(B_234,A_235) = k3_xboole_0(A_235,B_234) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_14])).

tff(c_64,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_3799,plain,(
    ! [A_755,B_756] :
      ( r1_xboole_0(A_755,B_756)
      | ~ r1_subset_1(A_755,B_756)
      | v1_xboole_0(B_756)
      | v1_xboole_0(A_755) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4775,plain,(
    ! [A_870,B_871] :
      ( k3_xboole_0(A_870,B_871) = k1_xboole_0
      | ~ r1_subset_1(A_870,B_871)
      | v1_xboole_0(B_871)
      | v1_xboole_0(A_870) ) ),
    inference(resolution,[status(thm)],[c_3799,c_2])).

tff(c_4778,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_4775])).

tff(c_4780,plain,
    ( k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_4778])).

tff(c_4781,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_68,c_4780])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_1300,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_1292])).

tff(c_4726,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1300,c_4719])).

tff(c_4292,plain,(
    ! [A_817,B_818,C_819] :
      ( k9_subset_1(A_817,B_818,C_819) = k3_xboole_0(B_818,C_819)
      | ~ m1_subset_1(C_819,k1_zfmisc_1(A_817)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4303,plain,(
    ! [B_818] : k9_subset_1('#skF_1',B_818,'#skF_4') = k3_xboole_0(B_818,'#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_4292])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_60,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_56,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_54,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_4897,plain,(
    ! [D_880,E_882,A_881,F_879,B_878,C_883] :
      ( v1_funct_1(k1_tmap_1(A_881,B_878,C_883,D_880,E_882,F_879))
      | ~ m1_subset_1(F_879,k1_zfmisc_1(k2_zfmisc_1(D_880,B_878)))
      | ~ v1_funct_2(F_879,D_880,B_878)
      | ~ v1_funct_1(F_879)
      | ~ m1_subset_1(E_882,k1_zfmisc_1(k2_zfmisc_1(C_883,B_878)))
      | ~ v1_funct_2(E_882,C_883,B_878)
      | ~ v1_funct_1(E_882)
      | ~ m1_subset_1(D_880,k1_zfmisc_1(A_881))
      | v1_xboole_0(D_880)
      | ~ m1_subset_1(C_883,k1_zfmisc_1(A_881))
      | v1_xboole_0(C_883)
      | v1_xboole_0(B_878)
      | v1_xboole_0(A_881) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_4899,plain,(
    ! [A_881,C_883,E_882] :
      ( v1_funct_1(k1_tmap_1(A_881,'#skF_2',C_883,'#skF_4',E_882,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_882,k1_zfmisc_1(k2_zfmisc_1(C_883,'#skF_2')))
      | ~ v1_funct_2(E_882,C_883,'#skF_2')
      | ~ v1_funct_1(E_882)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_881))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_883,k1_zfmisc_1(A_881))
      | v1_xboole_0(C_883)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_881) ) ),
    inference(resolution,[status(thm)],[c_52,c_4897])).

tff(c_4904,plain,(
    ! [A_881,C_883,E_882] :
      ( v1_funct_1(k1_tmap_1(A_881,'#skF_2',C_883,'#skF_4',E_882,'#skF_6'))
      | ~ m1_subset_1(E_882,k1_zfmisc_1(k2_zfmisc_1(C_883,'#skF_2')))
      | ~ v1_funct_2(E_882,C_883,'#skF_2')
      | ~ v1_funct_1(E_882)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_881))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_883,k1_zfmisc_1(A_881))
      | v1_xboole_0(C_883)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_881) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4899])).

tff(c_4929,plain,(
    ! [A_886,C_887,E_888] :
      ( v1_funct_1(k1_tmap_1(A_886,'#skF_2',C_887,'#skF_4',E_888,'#skF_6'))
      | ~ m1_subset_1(E_888,k1_zfmisc_1(k2_zfmisc_1(C_887,'#skF_2')))
      | ~ v1_funct_2(E_888,C_887,'#skF_2')
      | ~ v1_funct_1(E_888)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_886))
      | ~ m1_subset_1(C_887,k1_zfmisc_1(A_886))
      | v1_xboole_0(C_887)
      | v1_xboole_0(A_886) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_4904])).

tff(c_4933,plain,(
    ! [A_886] :
      ( v1_funct_1(k1_tmap_1(A_886,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_886))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_886))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_886) ) ),
    inference(resolution,[status(thm)],[c_58,c_4929])).

tff(c_4940,plain,(
    ! [A_886] :
      ( v1_funct_1(k1_tmap_1(A_886,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_886))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_886))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_886) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_4933])).

tff(c_4949,plain,(
    ! [A_890] :
      ( v1_funct_1(k1_tmap_1(A_890,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_890))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_890))
      | v1_xboole_0(A_890) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_4940])).

tff(c_4952,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_4949])).

tff(c_4955,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_4952])).

tff(c_4956,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_4955])).

tff(c_4626,plain,(
    ! [A_854,B_855,C_856,D_857] :
      ( k2_partfun1(A_854,B_855,C_856,D_857) = k7_relat_1(C_856,D_857)
      | ~ m1_subset_1(C_856,k1_zfmisc_1(k2_zfmisc_1(A_854,B_855)))
      | ~ v1_funct_1(C_856) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_4630,plain,(
    ! [D_857] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_857) = k7_relat_1('#skF_5',D_857)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_58,c_4626])).

tff(c_4636,plain,(
    ! [D_857] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_857) = k7_relat_1('#skF_5',D_857) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_4630])).

tff(c_4628,plain,(
    ! [D_857] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_857) = k7_relat_1('#skF_6',D_857)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_52,c_4626])).

tff(c_4633,plain,(
    ! [D_857] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_857) = k7_relat_1('#skF_6',D_857) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_4628])).

tff(c_46,plain,(
    ! [E_166,F_167,B_163,D_165,A_162,C_164] :
      ( v1_funct_2(k1_tmap_1(A_162,B_163,C_164,D_165,E_166,F_167),k4_subset_1(A_162,C_164,D_165),B_163)
      | ~ m1_subset_1(F_167,k1_zfmisc_1(k2_zfmisc_1(D_165,B_163)))
      | ~ v1_funct_2(F_167,D_165,B_163)
      | ~ v1_funct_1(F_167)
      | ~ m1_subset_1(E_166,k1_zfmisc_1(k2_zfmisc_1(C_164,B_163)))
      | ~ v1_funct_2(E_166,C_164,B_163)
      | ~ v1_funct_1(E_166)
      | ~ m1_subset_1(D_165,k1_zfmisc_1(A_162))
      | v1_xboole_0(D_165)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(A_162))
      | v1_xboole_0(C_164)
      | v1_xboole_0(B_163)
      | v1_xboole_0(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_44,plain,(
    ! [E_166,F_167,B_163,D_165,A_162,C_164] :
      ( m1_subset_1(k1_tmap_1(A_162,B_163,C_164,D_165,E_166,F_167),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_162,C_164,D_165),B_163)))
      | ~ m1_subset_1(F_167,k1_zfmisc_1(k2_zfmisc_1(D_165,B_163)))
      | ~ v1_funct_2(F_167,D_165,B_163)
      | ~ v1_funct_1(F_167)
      | ~ m1_subset_1(E_166,k1_zfmisc_1(k2_zfmisc_1(C_164,B_163)))
      | ~ v1_funct_2(E_166,C_164,B_163)
      | ~ v1_funct_1(E_166)
      | ~ m1_subset_1(D_165,k1_zfmisc_1(A_162))
      | v1_xboole_0(D_165)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(A_162))
      | v1_xboole_0(C_164)
      | v1_xboole_0(B_163)
      | v1_xboole_0(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_5078,plain,(
    ! [E_920,B_921,C_923,F_918,A_919,D_922] :
      ( k2_partfun1(k4_subset_1(A_919,C_923,D_922),B_921,k1_tmap_1(A_919,B_921,C_923,D_922,E_920,F_918),C_923) = E_920
      | ~ m1_subset_1(k1_tmap_1(A_919,B_921,C_923,D_922,E_920,F_918),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_919,C_923,D_922),B_921)))
      | ~ v1_funct_2(k1_tmap_1(A_919,B_921,C_923,D_922,E_920,F_918),k4_subset_1(A_919,C_923,D_922),B_921)
      | ~ v1_funct_1(k1_tmap_1(A_919,B_921,C_923,D_922,E_920,F_918))
      | k2_partfun1(D_922,B_921,F_918,k9_subset_1(A_919,C_923,D_922)) != k2_partfun1(C_923,B_921,E_920,k9_subset_1(A_919,C_923,D_922))
      | ~ m1_subset_1(F_918,k1_zfmisc_1(k2_zfmisc_1(D_922,B_921)))
      | ~ v1_funct_2(F_918,D_922,B_921)
      | ~ v1_funct_1(F_918)
      | ~ m1_subset_1(E_920,k1_zfmisc_1(k2_zfmisc_1(C_923,B_921)))
      | ~ v1_funct_2(E_920,C_923,B_921)
      | ~ v1_funct_1(E_920)
      | ~ m1_subset_1(D_922,k1_zfmisc_1(A_919))
      | v1_xboole_0(D_922)
      | ~ m1_subset_1(C_923,k1_zfmisc_1(A_919))
      | v1_xboole_0(C_923)
      | v1_xboole_0(B_921)
      | v1_xboole_0(A_919) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_5459,plain,(
    ! [B_1029,D_1031,F_1030,A_1032,E_1033,C_1034] :
      ( k2_partfun1(k4_subset_1(A_1032,C_1034,D_1031),B_1029,k1_tmap_1(A_1032,B_1029,C_1034,D_1031,E_1033,F_1030),C_1034) = E_1033
      | ~ v1_funct_2(k1_tmap_1(A_1032,B_1029,C_1034,D_1031,E_1033,F_1030),k4_subset_1(A_1032,C_1034,D_1031),B_1029)
      | ~ v1_funct_1(k1_tmap_1(A_1032,B_1029,C_1034,D_1031,E_1033,F_1030))
      | k2_partfun1(D_1031,B_1029,F_1030,k9_subset_1(A_1032,C_1034,D_1031)) != k2_partfun1(C_1034,B_1029,E_1033,k9_subset_1(A_1032,C_1034,D_1031))
      | ~ m1_subset_1(F_1030,k1_zfmisc_1(k2_zfmisc_1(D_1031,B_1029)))
      | ~ v1_funct_2(F_1030,D_1031,B_1029)
      | ~ v1_funct_1(F_1030)
      | ~ m1_subset_1(E_1033,k1_zfmisc_1(k2_zfmisc_1(C_1034,B_1029)))
      | ~ v1_funct_2(E_1033,C_1034,B_1029)
      | ~ v1_funct_1(E_1033)
      | ~ m1_subset_1(D_1031,k1_zfmisc_1(A_1032))
      | v1_xboole_0(D_1031)
      | ~ m1_subset_1(C_1034,k1_zfmisc_1(A_1032))
      | v1_xboole_0(C_1034)
      | v1_xboole_0(B_1029)
      | v1_xboole_0(A_1032) ) ),
    inference(resolution,[status(thm)],[c_44,c_5078])).

tff(c_5817,plain,(
    ! [A_1083,D_1082,F_1081,E_1084,B_1080,C_1085] :
      ( k2_partfun1(k4_subset_1(A_1083,C_1085,D_1082),B_1080,k1_tmap_1(A_1083,B_1080,C_1085,D_1082,E_1084,F_1081),C_1085) = E_1084
      | ~ v1_funct_1(k1_tmap_1(A_1083,B_1080,C_1085,D_1082,E_1084,F_1081))
      | k2_partfun1(D_1082,B_1080,F_1081,k9_subset_1(A_1083,C_1085,D_1082)) != k2_partfun1(C_1085,B_1080,E_1084,k9_subset_1(A_1083,C_1085,D_1082))
      | ~ m1_subset_1(F_1081,k1_zfmisc_1(k2_zfmisc_1(D_1082,B_1080)))
      | ~ v1_funct_2(F_1081,D_1082,B_1080)
      | ~ v1_funct_1(F_1081)
      | ~ m1_subset_1(E_1084,k1_zfmisc_1(k2_zfmisc_1(C_1085,B_1080)))
      | ~ v1_funct_2(E_1084,C_1085,B_1080)
      | ~ v1_funct_1(E_1084)
      | ~ m1_subset_1(D_1082,k1_zfmisc_1(A_1083))
      | v1_xboole_0(D_1082)
      | ~ m1_subset_1(C_1085,k1_zfmisc_1(A_1083))
      | v1_xboole_0(C_1085)
      | v1_xboole_0(B_1080)
      | v1_xboole_0(A_1083) ) ),
    inference(resolution,[status(thm)],[c_46,c_5459])).

tff(c_5821,plain,(
    ! [A_1083,C_1085,E_1084] :
      ( k2_partfun1(k4_subset_1(A_1083,C_1085,'#skF_4'),'#skF_2',k1_tmap_1(A_1083,'#skF_2',C_1085,'#skF_4',E_1084,'#skF_6'),C_1085) = E_1084
      | ~ v1_funct_1(k1_tmap_1(A_1083,'#skF_2',C_1085,'#skF_4',E_1084,'#skF_6'))
      | k2_partfun1(C_1085,'#skF_2',E_1084,k9_subset_1(A_1083,C_1085,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_1083,C_1085,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1084,k1_zfmisc_1(k2_zfmisc_1(C_1085,'#skF_2')))
      | ~ v1_funct_2(E_1084,C_1085,'#skF_2')
      | ~ v1_funct_1(E_1084)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1083))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1085,k1_zfmisc_1(A_1083))
      | v1_xboole_0(C_1085)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1083) ) ),
    inference(resolution,[status(thm)],[c_52,c_5817])).

tff(c_5827,plain,(
    ! [A_1083,C_1085,E_1084] :
      ( k2_partfun1(k4_subset_1(A_1083,C_1085,'#skF_4'),'#skF_2',k1_tmap_1(A_1083,'#skF_2',C_1085,'#skF_4',E_1084,'#skF_6'),C_1085) = E_1084
      | ~ v1_funct_1(k1_tmap_1(A_1083,'#skF_2',C_1085,'#skF_4',E_1084,'#skF_6'))
      | k2_partfun1(C_1085,'#skF_2',E_1084,k9_subset_1(A_1083,C_1085,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1083,C_1085,'#skF_4'))
      | ~ m1_subset_1(E_1084,k1_zfmisc_1(k2_zfmisc_1(C_1085,'#skF_2')))
      | ~ v1_funct_2(E_1084,C_1085,'#skF_2')
      | ~ v1_funct_1(E_1084)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1083))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1085,k1_zfmisc_1(A_1083))
      | v1_xboole_0(C_1085)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1083) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4633,c_5821])).

tff(c_6164,plain,(
    ! [A_1150,C_1151,E_1152] :
      ( k2_partfun1(k4_subset_1(A_1150,C_1151,'#skF_4'),'#skF_2',k1_tmap_1(A_1150,'#skF_2',C_1151,'#skF_4',E_1152,'#skF_6'),C_1151) = E_1152
      | ~ v1_funct_1(k1_tmap_1(A_1150,'#skF_2',C_1151,'#skF_4',E_1152,'#skF_6'))
      | k2_partfun1(C_1151,'#skF_2',E_1152,k9_subset_1(A_1150,C_1151,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1150,C_1151,'#skF_4'))
      | ~ m1_subset_1(E_1152,k1_zfmisc_1(k2_zfmisc_1(C_1151,'#skF_2')))
      | ~ v1_funct_2(E_1152,C_1151,'#skF_2')
      | ~ v1_funct_1(E_1152)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1150))
      | ~ m1_subset_1(C_1151,k1_zfmisc_1(A_1150))
      | v1_xboole_0(C_1151)
      | v1_xboole_0(A_1150) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_5827])).

tff(c_6171,plain,(
    ! [A_1150] :
      ( k2_partfun1(k4_subset_1(A_1150,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1150,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1150,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1150,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1150,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1150))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1150))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1150) ) ),
    inference(resolution,[status(thm)],[c_58,c_6164])).

tff(c_6181,plain,(
    ! [A_1150] :
      ( k2_partfun1(k4_subset_1(A_1150,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1150,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1150,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1150,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1150,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1150))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1150))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_4636,c_6171])).

tff(c_6250,plain,(
    ! [A_1158] :
      ( k2_partfun1(k4_subset_1(A_1158,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1158,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1158,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1158,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1158,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1158))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1158))
      | v1_xboole_0(A_1158) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_6181])).

tff(c_1356,plain,(
    ! [A_378,B_379] :
      ( k7_relat_1(A_378,B_379) = k1_xboole_0
      | ~ r1_xboole_0(B_379,k1_relat_1(A_378))
      | ~ v1_relat_1(A_378) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2204,plain,(
    ! [A_470,A_471] :
      ( k7_relat_1(A_470,A_471) = k1_xboole_0
      | ~ v1_relat_1(A_470)
      | k3_xboole_0(A_471,k1_relat_1(A_470)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_1356])).

tff(c_2228,plain,(
    ! [A_472] :
      ( k7_relat_1(A_472,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_472) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1220,c_2204])).

tff(c_2236,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1299,c_2228])).

tff(c_1341,plain,(
    ! [A_373,B_374] :
      ( r1_xboole_0(A_373,B_374)
      | ~ r1_subset_1(A_373,B_374)
      | v1_xboole_0(B_374)
      | v1_xboole_0(A_373) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2311,plain,(
    ! [A_481,B_482] :
      ( k3_xboole_0(A_481,B_482) = k1_xboole_0
      | ~ r1_subset_1(A_481,B_482)
      | v1_xboole_0(B_482)
      | v1_xboole_0(A_481) ) ),
    inference(resolution,[status(thm)],[c_1341,c_2])).

tff(c_2317,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_2311])).

tff(c_2320,plain,
    ( k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_2317])).

tff(c_2321,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_68,c_2320])).

tff(c_2235,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1300,c_2228])).

tff(c_1380,plain,(
    ! [A_382,B_383,C_384] :
      ( k9_subset_1(A_382,B_383,C_384) = k3_xboole_0(B_383,C_384)
      | ~ m1_subset_1(C_384,k1_zfmisc_1(A_382)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1391,plain,(
    ! [B_383] : k9_subset_1('#skF_1',B_383,'#skF_4') = k3_xboole_0(B_383,'#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_1380])).

tff(c_2454,plain,(
    ! [C_497,B_492,F_493,E_496,D_494,A_495] :
      ( v1_funct_1(k1_tmap_1(A_495,B_492,C_497,D_494,E_496,F_493))
      | ~ m1_subset_1(F_493,k1_zfmisc_1(k2_zfmisc_1(D_494,B_492)))
      | ~ v1_funct_2(F_493,D_494,B_492)
      | ~ v1_funct_1(F_493)
      | ~ m1_subset_1(E_496,k1_zfmisc_1(k2_zfmisc_1(C_497,B_492)))
      | ~ v1_funct_2(E_496,C_497,B_492)
      | ~ v1_funct_1(E_496)
      | ~ m1_subset_1(D_494,k1_zfmisc_1(A_495))
      | v1_xboole_0(D_494)
      | ~ m1_subset_1(C_497,k1_zfmisc_1(A_495))
      | v1_xboole_0(C_497)
      | v1_xboole_0(B_492)
      | v1_xboole_0(A_495) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_2456,plain,(
    ! [A_495,C_497,E_496] :
      ( v1_funct_1(k1_tmap_1(A_495,'#skF_2',C_497,'#skF_4',E_496,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_496,k1_zfmisc_1(k2_zfmisc_1(C_497,'#skF_2')))
      | ~ v1_funct_2(E_496,C_497,'#skF_2')
      | ~ v1_funct_1(E_496)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_495))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_497,k1_zfmisc_1(A_495))
      | v1_xboole_0(C_497)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_495) ) ),
    inference(resolution,[status(thm)],[c_52,c_2454])).

tff(c_2461,plain,(
    ! [A_495,C_497,E_496] :
      ( v1_funct_1(k1_tmap_1(A_495,'#skF_2',C_497,'#skF_4',E_496,'#skF_6'))
      | ~ m1_subset_1(E_496,k1_zfmisc_1(k2_zfmisc_1(C_497,'#skF_2')))
      | ~ v1_funct_2(E_496,C_497,'#skF_2')
      | ~ v1_funct_1(E_496)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_495))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_497,k1_zfmisc_1(A_495))
      | v1_xboole_0(C_497)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_495) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_2456])).

tff(c_2467,plain,(
    ! [A_498,C_499,E_500] :
      ( v1_funct_1(k1_tmap_1(A_498,'#skF_2',C_499,'#skF_4',E_500,'#skF_6'))
      | ~ m1_subset_1(E_500,k1_zfmisc_1(k2_zfmisc_1(C_499,'#skF_2')))
      | ~ v1_funct_2(E_500,C_499,'#skF_2')
      | ~ v1_funct_1(E_500)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_498))
      | ~ m1_subset_1(C_499,k1_zfmisc_1(A_498))
      | v1_xboole_0(C_499)
      | v1_xboole_0(A_498) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_2461])).

tff(c_2471,plain,(
    ! [A_498] :
      ( v1_funct_1(k1_tmap_1(A_498,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_498))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_498))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_498) ) ),
    inference(resolution,[status(thm)],[c_58,c_2467])).

tff(c_2478,plain,(
    ! [A_498] :
      ( v1_funct_1(k1_tmap_1(A_498,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_498))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_498))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_498) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_2471])).

tff(c_2487,plain,(
    ! [A_502] :
      ( v1_funct_1(k1_tmap_1(A_502,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_502))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_502))
      | v1_xboole_0(A_502) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2478])).

tff(c_2490,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_2487])).

tff(c_2493,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2490])).

tff(c_2494,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2493])).

tff(c_2282,plain,(
    ! [A_475,B_476,C_477,D_478] :
      ( k2_partfun1(A_475,B_476,C_477,D_478) = k7_relat_1(C_477,D_478)
      | ~ m1_subset_1(C_477,k1_zfmisc_1(k2_zfmisc_1(A_475,B_476)))
      | ~ v1_funct_1(C_477) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2286,plain,(
    ! [D_478] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_478) = k7_relat_1('#skF_5',D_478)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_58,c_2282])).

tff(c_2292,plain,(
    ! [D_478] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_478) = k7_relat_1('#skF_5',D_478) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2286])).

tff(c_2284,plain,(
    ! [D_478] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_478) = k7_relat_1('#skF_6',D_478)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_52,c_2282])).

tff(c_2289,plain,(
    ! [D_478] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_478) = k7_relat_1('#skF_6',D_478) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2284])).

tff(c_2682,plain,(
    ! [A_543,C_547,E_544,D_546,B_545,F_542] :
      ( k2_partfun1(k4_subset_1(A_543,C_547,D_546),B_545,k1_tmap_1(A_543,B_545,C_547,D_546,E_544,F_542),D_546) = F_542
      | ~ m1_subset_1(k1_tmap_1(A_543,B_545,C_547,D_546,E_544,F_542),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_543,C_547,D_546),B_545)))
      | ~ v1_funct_2(k1_tmap_1(A_543,B_545,C_547,D_546,E_544,F_542),k4_subset_1(A_543,C_547,D_546),B_545)
      | ~ v1_funct_1(k1_tmap_1(A_543,B_545,C_547,D_546,E_544,F_542))
      | k2_partfun1(D_546,B_545,F_542,k9_subset_1(A_543,C_547,D_546)) != k2_partfun1(C_547,B_545,E_544,k9_subset_1(A_543,C_547,D_546))
      | ~ m1_subset_1(F_542,k1_zfmisc_1(k2_zfmisc_1(D_546,B_545)))
      | ~ v1_funct_2(F_542,D_546,B_545)
      | ~ v1_funct_1(F_542)
      | ~ m1_subset_1(E_544,k1_zfmisc_1(k2_zfmisc_1(C_547,B_545)))
      | ~ v1_funct_2(E_544,C_547,B_545)
      | ~ v1_funct_1(E_544)
      | ~ m1_subset_1(D_546,k1_zfmisc_1(A_543))
      | v1_xboole_0(D_546)
      | ~ m1_subset_1(C_547,k1_zfmisc_1(A_543))
      | v1_xboole_0(C_547)
      | v1_xboole_0(B_545)
      | v1_xboole_0(A_543) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_3033,plain,(
    ! [A_644,E_645,D_643,F_642,C_646,B_641] :
      ( k2_partfun1(k4_subset_1(A_644,C_646,D_643),B_641,k1_tmap_1(A_644,B_641,C_646,D_643,E_645,F_642),D_643) = F_642
      | ~ v1_funct_2(k1_tmap_1(A_644,B_641,C_646,D_643,E_645,F_642),k4_subset_1(A_644,C_646,D_643),B_641)
      | ~ v1_funct_1(k1_tmap_1(A_644,B_641,C_646,D_643,E_645,F_642))
      | k2_partfun1(D_643,B_641,F_642,k9_subset_1(A_644,C_646,D_643)) != k2_partfun1(C_646,B_641,E_645,k9_subset_1(A_644,C_646,D_643))
      | ~ m1_subset_1(F_642,k1_zfmisc_1(k2_zfmisc_1(D_643,B_641)))
      | ~ v1_funct_2(F_642,D_643,B_641)
      | ~ v1_funct_1(F_642)
      | ~ m1_subset_1(E_645,k1_zfmisc_1(k2_zfmisc_1(C_646,B_641)))
      | ~ v1_funct_2(E_645,C_646,B_641)
      | ~ v1_funct_1(E_645)
      | ~ m1_subset_1(D_643,k1_zfmisc_1(A_644))
      | v1_xboole_0(D_643)
      | ~ m1_subset_1(C_646,k1_zfmisc_1(A_644))
      | v1_xboole_0(C_646)
      | v1_xboole_0(B_641)
      | v1_xboole_0(A_644) ) ),
    inference(resolution,[status(thm)],[c_44,c_2682])).

tff(c_3371,plain,(
    ! [C_706,A_704,D_703,F_702,B_701,E_705] :
      ( k2_partfun1(k4_subset_1(A_704,C_706,D_703),B_701,k1_tmap_1(A_704,B_701,C_706,D_703,E_705,F_702),D_703) = F_702
      | ~ v1_funct_1(k1_tmap_1(A_704,B_701,C_706,D_703,E_705,F_702))
      | k2_partfun1(D_703,B_701,F_702,k9_subset_1(A_704,C_706,D_703)) != k2_partfun1(C_706,B_701,E_705,k9_subset_1(A_704,C_706,D_703))
      | ~ m1_subset_1(F_702,k1_zfmisc_1(k2_zfmisc_1(D_703,B_701)))
      | ~ v1_funct_2(F_702,D_703,B_701)
      | ~ v1_funct_1(F_702)
      | ~ m1_subset_1(E_705,k1_zfmisc_1(k2_zfmisc_1(C_706,B_701)))
      | ~ v1_funct_2(E_705,C_706,B_701)
      | ~ v1_funct_1(E_705)
      | ~ m1_subset_1(D_703,k1_zfmisc_1(A_704))
      | v1_xboole_0(D_703)
      | ~ m1_subset_1(C_706,k1_zfmisc_1(A_704))
      | v1_xboole_0(C_706)
      | v1_xboole_0(B_701)
      | v1_xboole_0(A_704) ) ),
    inference(resolution,[status(thm)],[c_46,c_3033])).

tff(c_3375,plain,(
    ! [A_704,C_706,E_705] :
      ( k2_partfun1(k4_subset_1(A_704,C_706,'#skF_4'),'#skF_2',k1_tmap_1(A_704,'#skF_2',C_706,'#skF_4',E_705,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_704,'#skF_2',C_706,'#skF_4',E_705,'#skF_6'))
      | k2_partfun1(C_706,'#skF_2',E_705,k9_subset_1(A_704,C_706,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_704,C_706,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_705,k1_zfmisc_1(k2_zfmisc_1(C_706,'#skF_2')))
      | ~ v1_funct_2(E_705,C_706,'#skF_2')
      | ~ v1_funct_1(E_705)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_704))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_706,k1_zfmisc_1(A_704))
      | v1_xboole_0(C_706)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_704) ) ),
    inference(resolution,[status(thm)],[c_52,c_3371])).

tff(c_3381,plain,(
    ! [A_704,C_706,E_705] :
      ( k2_partfun1(k4_subset_1(A_704,C_706,'#skF_4'),'#skF_2',k1_tmap_1(A_704,'#skF_2',C_706,'#skF_4',E_705,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_704,'#skF_2',C_706,'#skF_4',E_705,'#skF_6'))
      | k2_partfun1(C_706,'#skF_2',E_705,k9_subset_1(A_704,C_706,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_704,C_706,'#skF_4'))
      | ~ m1_subset_1(E_705,k1_zfmisc_1(k2_zfmisc_1(C_706,'#skF_2')))
      | ~ v1_funct_2(E_705,C_706,'#skF_2')
      | ~ v1_funct_1(E_705)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_704))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_706,k1_zfmisc_1(A_704))
      | v1_xboole_0(C_706)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_704) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_2289,c_3375])).

tff(c_3750,plain,(
    ! [A_751,C_752,E_753] :
      ( k2_partfun1(k4_subset_1(A_751,C_752,'#skF_4'),'#skF_2',k1_tmap_1(A_751,'#skF_2',C_752,'#skF_4',E_753,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_751,'#skF_2',C_752,'#skF_4',E_753,'#skF_6'))
      | k2_partfun1(C_752,'#skF_2',E_753,k9_subset_1(A_751,C_752,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_751,C_752,'#skF_4'))
      | ~ m1_subset_1(E_753,k1_zfmisc_1(k2_zfmisc_1(C_752,'#skF_2')))
      | ~ v1_funct_2(E_753,C_752,'#skF_2')
      | ~ v1_funct_1(E_753)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_751))
      | ~ m1_subset_1(C_752,k1_zfmisc_1(A_751))
      | v1_xboole_0(C_752)
      | v1_xboole_0(A_751) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_3381])).

tff(c_3757,plain,(
    ! [A_751] :
      ( k2_partfun1(k4_subset_1(A_751,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_751,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_751,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_751,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_751,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_751))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_751))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_751) ) ),
    inference(resolution,[status(thm)],[c_58,c_3750])).

tff(c_3767,plain,(
    ! [A_751] :
      ( k2_partfun1(k4_subset_1(A_751,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_751,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_751,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_751,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_751,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_751))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_751))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_751) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_2292,c_3757])).

tff(c_3769,plain,(
    ! [A_754] :
      ( k2_partfun1(k4_subset_1(A_754,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_754,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_754,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_754,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_754,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_754))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_754))
      | v1_xboole_0(A_754) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3767])).

tff(c_267,plain,(
    ! [C_241,A_242,B_243] :
      ( v1_relat_1(C_241)
      | ~ m1_subset_1(C_241,k1_zfmisc_1(k2_zfmisc_1(A_242,B_243))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_274,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_267])).

tff(c_162,plain,(
    ! [B_236,A_237] : k3_xboole_0(B_236,A_237) = k3_xboole_0(A_237,B_236) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_14])).

tff(c_178,plain,(
    ! [A_237] : k3_xboole_0(k1_xboole_0,A_237) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_6])).

tff(c_299,plain,(
    ! [A_252,B_253] :
      ( k7_relat_1(A_252,B_253) = k1_xboole_0
      | ~ r1_xboole_0(B_253,k1_relat_1(A_252))
      | ~ v1_relat_1(A_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_969,plain,(
    ! [A_339,A_340] :
      ( k7_relat_1(A_339,A_340) = k1_xboole_0
      | ~ v1_relat_1(A_339)
      | k3_xboole_0(A_340,k1_relat_1(A_339)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_299])).

tff(c_993,plain,(
    ! [A_341] :
      ( k7_relat_1(A_341,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_341) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_969])).

tff(c_1001,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_274,c_993])).

tff(c_305,plain,(
    ! [A_254,B_255] :
      ( r1_xboole_0(A_254,B_255)
      | ~ r1_subset_1(A_254,B_255)
      | v1_xboole_0(B_255)
      | v1_xboole_0(A_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1063,plain,(
    ! [A_348,B_349] :
      ( k3_xboole_0(A_348,B_349) = k1_xboole_0
      | ~ r1_subset_1(A_348,B_349)
      | v1_xboole_0(B_349)
      | v1_xboole_0(A_348) ) ),
    inference(resolution,[status(thm)],[c_305,c_2])).

tff(c_1066,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_1063])).

tff(c_1068,plain,
    ( k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_1066])).

tff(c_1069,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_68,c_1068])).

tff(c_275,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_267])).

tff(c_1000,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_275,c_993])).

tff(c_1034,plain,(
    ! [A_342,B_343,C_344,D_345] :
      ( k2_partfun1(A_342,B_343,C_344,D_345) = k7_relat_1(C_344,D_345)
      | ~ m1_subset_1(C_344,k1_zfmisc_1(k2_zfmisc_1(A_342,B_343)))
      | ~ v1_funct_1(C_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1038,plain,(
    ! [D_345] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_345) = k7_relat_1('#skF_5',D_345)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_58,c_1034])).

tff(c_1044,plain,(
    ! [D_345] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_345) = k7_relat_1('#skF_5',D_345) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1038])).

tff(c_1036,plain,(
    ! [D_345] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_345) = k7_relat_1('#skF_6',D_345)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_52,c_1034])).

tff(c_1041,plain,(
    ! [D_345] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_345) = k7_relat_1('#skF_6',D_345) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1036])).

tff(c_904,plain,(
    ! [A_332,B_333,C_334] :
      ( k9_subset_1(A_332,B_333,C_334) = k3_xboole_0(B_333,C_334)
      | ~ m1_subset_1(C_334,k1_zfmisc_1(A_332)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_915,plain,(
    ! [B_333] : k9_subset_1('#skF_1',B_333,'#skF_4') = k3_xboole_0(B_333,'#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_904])).

tff(c_50,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_161,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_931,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_915,c_915,c_161])).

tff(c_932,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_4','#skF_3')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_144,c_931])).

tff(c_1201,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1001,c_1069,c_1000,c_1069,c_1044,c_1041,c_932])).

tff(c_1202,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1340,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1202])).

tff(c_3780,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3769,c_1340])).

tff(c_3794,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_2236,c_2321,c_144,c_2235,c_2321,c_144,c_1391,c_1391,c_2494,c_3780])).

tff(c_3796,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_3794])).

tff(c_3797,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1202])).

tff(c_6259,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6250,c_3797])).

tff(c_6270,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_4727,c_4781,c_144,c_4726,c_4781,c_144,c_4303,c_4303,c_4956,c_6259])).

tff(c_6272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_6270])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:52:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.92/2.91  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.09/2.93  
% 8.09/2.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.09/2.93  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.09/2.93  
% 8.09/2.93  %Foreground sorts:
% 8.09/2.93  
% 8.09/2.93  
% 8.09/2.93  %Background operators:
% 8.09/2.93  
% 8.09/2.93  
% 8.09/2.93  %Foreground operators:
% 8.09/2.93  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 8.09/2.93  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.09/2.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.09/2.93  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.09/2.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.09/2.93  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.09/2.93  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 8.09/2.93  tff('#skF_5', type, '#skF_5': $i).
% 8.09/2.93  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.09/2.93  tff('#skF_6', type, '#skF_6': $i).
% 8.09/2.93  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.09/2.93  tff('#skF_2', type, '#skF_2': $i).
% 8.09/2.93  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 8.09/2.93  tff('#skF_3', type, '#skF_3': $i).
% 8.09/2.93  tff('#skF_1', type, '#skF_1': $i).
% 8.09/2.93  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.09/2.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.09/2.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.09/2.93  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.09/2.93  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.09/2.93  tff('#skF_4', type, '#skF_4': $i).
% 8.09/2.93  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.09/2.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.09/2.93  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 8.09/2.93  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.09/2.93  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.09/2.93  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.09/2.93  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.09/2.93  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 8.09/2.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.09/2.93  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.09/2.93  
% 8.09/2.96  tff(f_225, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 8.09/2.96  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.09/2.96  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 8.09/2.96  tff(f_46, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 8.09/2.96  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 8.09/2.96  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.09/2.96  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 8.09/2.96  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 8.09/2.96  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 8.09/2.96  tff(f_183, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 8.09/2.96  tff(f_101, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 8.09/2.96  tff(f_149, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 8.09/2.96  tff(c_76, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.09/2.96  tff(c_70, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.09/2.96  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.09/2.96  tff(c_52, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.09/2.96  tff(c_1292, plain, (![C_362, A_363, B_364]: (v1_relat_1(C_362) | ~m1_subset_1(C_362, k1_zfmisc_1(k2_zfmisc_1(A_363, B_364))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.09/2.96  tff(c_1299, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_1292])).
% 8.09/2.96  tff(c_8, plain, (![B_5, A_4]: (k2_tarski(B_5, A_4)=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.09/2.96  tff(c_118, plain, (![A_230, B_231]: (k1_setfam_1(k2_tarski(A_230, B_231))=k3_xboole_0(A_230, B_231))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.09/2.96  tff(c_138, plain, (![B_234, A_235]: (k1_setfam_1(k2_tarski(B_234, A_235))=k3_xboole_0(A_235, B_234))), inference(superposition, [status(thm), theory('equality')], [c_8, c_118])).
% 8.09/2.96  tff(c_14, plain, (![A_12, B_13]: (k1_setfam_1(k2_tarski(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.09/2.96  tff(c_1204, plain, (![B_359, A_360]: (k3_xboole_0(B_359, A_360)=k3_xboole_0(A_360, B_359))), inference(superposition, [status(thm), theory('equality')], [c_138, c_14])).
% 8.09/2.96  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.09/2.96  tff(c_1220, plain, (![A_360]: (k3_xboole_0(k1_xboole_0, A_360)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1204, c_6])).
% 8.09/2.96  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.09/2.96  tff(c_3818, plain, (![A_760, B_761]: (k7_relat_1(A_760, B_761)=k1_xboole_0 | ~r1_xboole_0(B_761, k1_relat_1(A_760)) | ~v1_relat_1(A_760))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.09/2.96  tff(c_4695, plain, (![A_864, A_865]: (k7_relat_1(A_864, A_865)=k1_xboole_0 | ~v1_relat_1(A_864) | k3_xboole_0(A_865, k1_relat_1(A_864))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_3818])).
% 8.09/2.96  tff(c_4719, plain, (![A_866]: (k7_relat_1(A_866, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_866))), inference(superposition, [status(thm), theory('equality')], [c_1220, c_4695])).
% 8.09/2.96  tff(c_4727, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_1299, c_4719])).
% 8.09/2.96  tff(c_72, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.09/2.96  tff(c_68, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.09/2.96  tff(c_144, plain, (![B_234, A_235]: (k3_xboole_0(B_234, A_235)=k3_xboole_0(A_235, B_234))), inference(superposition, [status(thm), theory('equality')], [c_138, c_14])).
% 8.09/2.96  tff(c_64, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.09/2.96  tff(c_3799, plain, (![A_755, B_756]: (r1_xboole_0(A_755, B_756) | ~r1_subset_1(A_755, B_756) | v1_xboole_0(B_756) | v1_xboole_0(A_755))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.09/2.96  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.09/2.96  tff(c_4775, plain, (![A_870, B_871]: (k3_xboole_0(A_870, B_871)=k1_xboole_0 | ~r1_subset_1(A_870, B_871) | v1_xboole_0(B_871) | v1_xboole_0(A_870))), inference(resolution, [status(thm)], [c_3799, c_2])).
% 8.09/2.96  tff(c_4778, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_64, c_4775])).
% 8.09/2.96  tff(c_4780, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_144, c_4778])).
% 8.09/2.96  tff(c_4781, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_72, c_68, c_4780])).
% 8.09/2.96  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.09/2.96  tff(c_1300, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_1292])).
% 8.09/2.96  tff(c_4726, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_1300, c_4719])).
% 8.09/2.96  tff(c_4292, plain, (![A_817, B_818, C_819]: (k9_subset_1(A_817, B_818, C_819)=k3_xboole_0(B_818, C_819) | ~m1_subset_1(C_819, k1_zfmisc_1(A_817)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.09/2.96  tff(c_4303, plain, (![B_818]: (k9_subset_1('#skF_1', B_818, '#skF_4')=k3_xboole_0(B_818, '#skF_4'))), inference(resolution, [status(thm)], [c_66, c_4292])).
% 8.09/2.96  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.09/2.96  tff(c_60, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.09/2.96  tff(c_74, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.09/2.96  tff(c_56, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.09/2.96  tff(c_54, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.09/2.96  tff(c_4897, plain, (![D_880, E_882, A_881, F_879, B_878, C_883]: (v1_funct_1(k1_tmap_1(A_881, B_878, C_883, D_880, E_882, F_879)) | ~m1_subset_1(F_879, k1_zfmisc_1(k2_zfmisc_1(D_880, B_878))) | ~v1_funct_2(F_879, D_880, B_878) | ~v1_funct_1(F_879) | ~m1_subset_1(E_882, k1_zfmisc_1(k2_zfmisc_1(C_883, B_878))) | ~v1_funct_2(E_882, C_883, B_878) | ~v1_funct_1(E_882) | ~m1_subset_1(D_880, k1_zfmisc_1(A_881)) | v1_xboole_0(D_880) | ~m1_subset_1(C_883, k1_zfmisc_1(A_881)) | v1_xboole_0(C_883) | v1_xboole_0(B_878) | v1_xboole_0(A_881))), inference(cnfTransformation, [status(thm)], [f_183])).
% 8.09/2.96  tff(c_4899, plain, (![A_881, C_883, E_882]: (v1_funct_1(k1_tmap_1(A_881, '#skF_2', C_883, '#skF_4', E_882, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_882, k1_zfmisc_1(k2_zfmisc_1(C_883, '#skF_2'))) | ~v1_funct_2(E_882, C_883, '#skF_2') | ~v1_funct_1(E_882) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_881)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_883, k1_zfmisc_1(A_881)) | v1_xboole_0(C_883) | v1_xboole_0('#skF_2') | v1_xboole_0(A_881))), inference(resolution, [status(thm)], [c_52, c_4897])).
% 8.09/2.96  tff(c_4904, plain, (![A_881, C_883, E_882]: (v1_funct_1(k1_tmap_1(A_881, '#skF_2', C_883, '#skF_4', E_882, '#skF_6')) | ~m1_subset_1(E_882, k1_zfmisc_1(k2_zfmisc_1(C_883, '#skF_2'))) | ~v1_funct_2(E_882, C_883, '#skF_2') | ~v1_funct_1(E_882) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_881)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_883, k1_zfmisc_1(A_881)) | v1_xboole_0(C_883) | v1_xboole_0('#skF_2') | v1_xboole_0(A_881))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_4899])).
% 8.09/2.96  tff(c_4929, plain, (![A_886, C_887, E_888]: (v1_funct_1(k1_tmap_1(A_886, '#skF_2', C_887, '#skF_4', E_888, '#skF_6')) | ~m1_subset_1(E_888, k1_zfmisc_1(k2_zfmisc_1(C_887, '#skF_2'))) | ~v1_funct_2(E_888, C_887, '#skF_2') | ~v1_funct_1(E_888) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_886)) | ~m1_subset_1(C_887, k1_zfmisc_1(A_886)) | v1_xboole_0(C_887) | v1_xboole_0(A_886))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_4904])).
% 8.09/2.96  tff(c_4933, plain, (![A_886]: (v1_funct_1(k1_tmap_1(A_886, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_886)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_886)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_886))), inference(resolution, [status(thm)], [c_58, c_4929])).
% 8.09/2.96  tff(c_4940, plain, (![A_886]: (v1_funct_1(k1_tmap_1(A_886, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_886)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_886)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_886))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_4933])).
% 8.09/2.96  tff(c_4949, plain, (![A_890]: (v1_funct_1(k1_tmap_1(A_890, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_890)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_890)) | v1_xboole_0(A_890))), inference(negUnitSimplification, [status(thm)], [c_72, c_4940])).
% 8.09/2.96  tff(c_4952, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_70, c_4949])).
% 8.09/2.96  tff(c_4955, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_4952])).
% 8.09/2.96  tff(c_4956, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_76, c_4955])).
% 8.09/2.96  tff(c_4626, plain, (![A_854, B_855, C_856, D_857]: (k2_partfun1(A_854, B_855, C_856, D_857)=k7_relat_1(C_856, D_857) | ~m1_subset_1(C_856, k1_zfmisc_1(k2_zfmisc_1(A_854, B_855))) | ~v1_funct_1(C_856))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.09/2.96  tff(c_4630, plain, (![D_857]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_857)=k7_relat_1('#skF_5', D_857) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_58, c_4626])).
% 8.09/2.96  tff(c_4636, plain, (![D_857]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_857)=k7_relat_1('#skF_5', D_857))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_4630])).
% 8.09/2.96  tff(c_4628, plain, (![D_857]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_857)=k7_relat_1('#skF_6', D_857) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_52, c_4626])).
% 8.09/2.96  tff(c_4633, plain, (![D_857]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_857)=k7_relat_1('#skF_6', D_857))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_4628])).
% 8.09/2.96  tff(c_46, plain, (![E_166, F_167, B_163, D_165, A_162, C_164]: (v1_funct_2(k1_tmap_1(A_162, B_163, C_164, D_165, E_166, F_167), k4_subset_1(A_162, C_164, D_165), B_163) | ~m1_subset_1(F_167, k1_zfmisc_1(k2_zfmisc_1(D_165, B_163))) | ~v1_funct_2(F_167, D_165, B_163) | ~v1_funct_1(F_167) | ~m1_subset_1(E_166, k1_zfmisc_1(k2_zfmisc_1(C_164, B_163))) | ~v1_funct_2(E_166, C_164, B_163) | ~v1_funct_1(E_166) | ~m1_subset_1(D_165, k1_zfmisc_1(A_162)) | v1_xboole_0(D_165) | ~m1_subset_1(C_164, k1_zfmisc_1(A_162)) | v1_xboole_0(C_164) | v1_xboole_0(B_163) | v1_xboole_0(A_162))), inference(cnfTransformation, [status(thm)], [f_183])).
% 8.09/2.96  tff(c_44, plain, (![E_166, F_167, B_163, D_165, A_162, C_164]: (m1_subset_1(k1_tmap_1(A_162, B_163, C_164, D_165, E_166, F_167), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_162, C_164, D_165), B_163))) | ~m1_subset_1(F_167, k1_zfmisc_1(k2_zfmisc_1(D_165, B_163))) | ~v1_funct_2(F_167, D_165, B_163) | ~v1_funct_1(F_167) | ~m1_subset_1(E_166, k1_zfmisc_1(k2_zfmisc_1(C_164, B_163))) | ~v1_funct_2(E_166, C_164, B_163) | ~v1_funct_1(E_166) | ~m1_subset_1(D_165, k1_zfmisc_1(A_162)) | v1_xboole_0(D_165) | ~m1_subset_1(C_164, k1_zfmisc_1(A_162)) | v1_xboole_0(C_164) | v1_xboole_0(B_163) | v1_xboole_0(A_162))), inference(cnfTransformation, [status(thm)], [f_183])).
% 8.09/2.96  tff(c_5078, plain, (![E_920, B_921, C_923, F_918, A_919, D_922]: (k2_partfun1(k4_subset_1(A_919, C_923, D_922), B_921, k1_tmap_1(A_919, B_921, C_923, D_922, E_920, F_918), C_923)=E_920 | ~m1_subset_1(k1_tmap_1(A_919, B_921, C_923, D_922, E_920, F_918), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_919, C_923, D_922), B_921))) | ~v1_funct_2(k1_tmap_1(A_919, B_921, C_923, D_922, E_920, F_918), k4_subset_1(A_919, C_923, D_922), B_921) | ~v1_funct_1(k1_tmap_1(A_919, B_921, C_923, D_922, E_920, F_918)) | k2_partfun1(D_922, B_921, F_918, k9_subset_1(A_919, C_923, D_922))!=k2_partfun1(C_923, B_921, E_920, k9_subset_1(A_919, C_923, D_922)) | ~m1_subset_1(F_918, k1_zfmisc_1(k2_zfmisc_1(D_922, B_921))) | ~v1_funct_2(F_918, D_922, B_921) | ~v1_funct_1(F_918) | ~m1_subset_1(E_920, k1_zfmisc_1(k2_zfmisc_1(C_923, B_921))) | ~v1_funct_2(E_920, C_923, B_921) | ~v1_funct_1(E_920) | ~m1_subset_1(D_922, k1_zfmisc_1(A_919)) | v1_xboole_0(D_922) | ~m1_subset_1(C_923, k1_zfmisc_1(A_919)) | v1_xboole_0(C_923) | v1_xboole_0(B_921) | v1_xboole_0(A_919))), inference(cnfTransformation, [status(thm)], [f_149])).
% 8.09/2.96  tff(c_5459, plain, (![B_1029, D_1031, F_1030, A_1032, E_1033, C_1034]: (k2_partfun1(k4_subset_1(A_1032, C_1034, D_1031), B_1029, k1_tmap_1(A_1032, B_1029, C_1034, D_1031, E_1033, F_1030), C_1034)=E_1033 | ~v1_funct_2(k1_tmap_1(A_1032, B_1029, C_1034, D_1031, E_1033, F_1030), k4_subset_1(A_1032, C_1034, D_1031), B_1029) | ~v1_funct_1(k1_tmap_1(A_1032, B_1029, C_1034, D_1031, E_1033, F_1030)) | k2_partfun1(D_1031, B_1029, F_1030, k9_subset_1(A_1032, C_1034, D_1031))!=k2_partfun1(C_1034, B_1029, E_1033, k9_subset_1(A_1032, C_1034, D_1031)) | ~m1_subset_1(F_1030, k1_zfmisc_1(k2_zfmisc_1(D_1031, B_1029))) | ~v1_funct_2(F_1030, D_1031, B_1029) | ~v1_funct_1(F_1030) | ~m1_subset_1(E_1033, k1_zfmisc_1(k2_zfmisc_1(C_1034, B_1029))) | ~v1_funct_2(E_1033, C_1034, B_1029) | ~v1_funct_1(E_1033) | ~m1_subset_1(D_1031, k1_zfmisc_1(A_1032)) | v1_xboole_0(D_1031) | ~m1_subset_1(C_1034, k1_zfmisc_1(A_1032)) | v1_xboole_0(C_1034) | v1_xboole_0(B_1029) | v1_xboole_0(A_1032))), inference(resolution, [status(thm)], [c_44, c_5078])).
% 8.09/2.96  tff(c_5817, plain, (![A_1083, D_1082, F_1081, E_1084, B_1080, C_1085]: (k2_partfun1(k4_subset_1(A_1083, C_1085, D_1082), B_1080, k1_tmap_1(A_1083, B_1080, C_1085, D_1082, E_1084, F_1081), C_1085)=E_1084 | ~v1_funct_1(k1_tmap_1(A_1083, B_1080, C_1085, D_1082, E_1084, F_1081)) | k2_partfun1(D_1082, B_1080, F_1081, k9_subset_1(A_1083, C_1085, D_1082))!=k2_partfun1(C_1085, B_1080, E_1084, k9_subset_1(A_1083, C_1085, D_1082)) | ~m1_subset_1(F_1081, k1_zfmisc_1(k2_zfmisc_1(D_1082, B_1080))) | ~v1_funct_2(F_1081, D_1082, B_1080) | ~v1_funct_1(F_1081) | ~m1_subset_1(E_1084, k1_zfmisc_1(k2_zfmisc_1(C_1085, B_1080))) | ~v1_funct_2(E_1084, C_1085, B_1080) | ~v1_funct_1(E_1084) | ~m1_subset_1(D_1082, k1_zfmisc_1(A_1083)) | v1_xboole_0(D_1082) | ~m1_subset_1(C_1085, k1_zfmisc_1(A_1083)) | v1_xboole_0(C_1085) | v1_xboole_0(B_1080) | v1_xboole_0(A_1083))), inference(resolution, [status(thm)], [c_46, c_5459])).
% 8.09/2.96  tff(c_5821, plain, (![A_1083, C_1085, E_1084]: (k2_partfun1(k4_subset_1(A_1083, C_1085, '#skF_4'), '#skF_2', k1_tmap_1(A_1083, '#skF_2', C_1085, '#skF_4', E_1084, '#skF_6'), C_1085)=E_1084 | ~v1_funct_1(k1_tmap_1(A_1083, '#skF_2', C_1085, '#skF_4', E_1084, '#skF_6')) | k2_partfun1(C_1085, '#skF_2', E_1084, k9_subset_1(A_1083, C_1085, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_1083, C_1085, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1084, k1_zfmisc_1(k2_zfmisc_1(C_1085, '#skF_2'))) | ~v1_funct_2(E_1084, C_1085, '#skF_2') | ~v1_funct_1(E_1084) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1083)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1085, k1_zfmisc_1(A_1083)) | v1_xboole_0(C_1085) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1083))), inference(resolution, [status(thm)], [c_52, c_5817])).
% 8.09/2.96  tff(c_5827, plain, (![A_1083, C_1085, E_1084]: (k2_partfun1(k4_subset_1(A_1083, C_1085, '#skF_4'), '#skF_2', k1_tmap_1(A_1083, '#skF_2', C_1085, '#skF_4', E_1084, '#skF_6'), C_1085)=E_1084 | ~v1_funct_1(k1_tmap_1(A_1083, '#skF_2', C_1085, '#skF_4', E_1084, '#skF_6')) | k2_partfun1(C_1085, '#skF_2', E_1084, k9_subset_1(A_1083, C_1085, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1083, C_1085, '#skF_4')) | ~m1_subset_1(E_1084, k1_zfmisc_1(k2_zfmisc_1(C_1085, '#skF_2'))) | ~v1_funct_2(E_1084, C_1085, '#skF_2') | ~v1_funct_1(E_1084) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1083)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1085, k1_zfmisc_1(A_1083)) | v1_xboole_0(C_1085) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1083))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_4633, c_5821])).
% 8.09/2.96  tff(c_6164, plain, (![A_1150, C_1151, E_1152]: (k2_partfun1(k4_subset_1(A_1150, C_1151, '#skF_4'), '#skF_2', k1_tmap_1(A_1150, '#skF_2', C_1151, '#skF_4', E_1152, '#skF_6'), C_1151)=E_1152 | ~v1_funct_1(k1_tmap_1(A_1150, '#skF_2', C_1151, '#skF_4', E_1152, '#skF_6')) | k2_partfun1(C_1151, '#skF_2', E_1152, k9_subset_1(A_1150, C_1151, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1150, C_1151, '#skF_4')) | ~m1_subset_1(E_1152, k1_zfmisc_1(k2_zfmisc_1(C_1151, '#skF_2'))) | ~v1_funct_2(E_1152, C_1151, '#skF_2') | ~v1_funct_1(E_1152) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1150)) | ~m1_subset_1(C_1151, k1_zfmisc_1(A_1150)) | v1_xboole_0(C_1151) | v1_xboole_0(A_1150))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_5827])).
% 8.09/2.96  tff(c_6171, plain, (![A_1150]: (k2_partfun1(k4_subset_1(A_1150, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1150, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1150, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_1150, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1150, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1150)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1150)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1150))), inference(resolution, [status(thm)], [c_58, c_6164])).
% 8.09/2.96  tff(c_6181, plain, (![A_1150]: (k2_partfun1(k4_subset_1(A_1150, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1150, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1150, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1150, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1150, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1150)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1150)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1150))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_4636, c_6171])).
% 8.09/2.96  tff(c_6250, plain, (![A_1158]: (k2_partfun1(k4_subset_1(A_1158, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1158, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1158, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1158, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1158, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1158)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1158)) | v1_xboole_0(A_1158))), inference(negUnitSimplification, [status(thm)], [c_72, c_6181])).
% 8.09/2.96  tff(c_1356, plain, (![A_378, B_379]: (k7_relat_1(A_378, B_379)=k1_xboole_0 | ~r1_xboole_0(B_379, k1_relat_1(A_378)) | ~v1_relat_1(A_378))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.09/2.96  tff(c_2204, plain, (![A_470, A_471]: (k7_relat_1(A_470, A_471)=k1_xboole_0 | ~v1_relat_1(A_470) | k3_xboole_0(A_471, k1_relat_1(A_470))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_1356])).
% 8.09/2.96  tff(c_2228, plain, (![A_472]: (k7_relat_1(A_472, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_472))), inference(superposition, [status(thm), theory('equality')], [c_1220, c_2204])).
% 8.09/2.96  tff(c_2236, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_1299, c_2228])).
% 8.09/2.96  tff(c_1341, plain, (![A_373, B_374]: (r1_xboole_0(A_373, B_374) | ~r1_subset_1(A_373, B_374) | v1_xboole_0(B_374) | v1_xboole_0(A_373))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.09/2.96  tff(c_2311, plain, (![A_481, B_482]: (k3_xboole_0(A_481, B_482)=k1_xboole_0 | ~r1_subset_1(A_481, B_482) | v1_xboole_0(B_482) | v1_xboole_0(A_481))), inference(resolution, [status(thm)], [c_1341, c_2])).
% 8.09/2.96  tff(c_2317, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_64, c_2311])).
% 8.09/2.96  tff(c_2320, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_144, c_2317])).
% 8.09/2.96  tff(c_2321, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_72, c_68, c_2320])).
% 8.09/2.96  tff(c_2235, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_1300, c_2228])).
% 8.09/2.96  tff(c_1380, plain, (![A_382, B_383, C_384]: (k9_subset_1(A_382, B_383, C_384)=k3_xboole_0(B_383, C_384) | ~m1_subset_1(C_384, k1_zfmisc_1(A_382)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.09/2.96  tff(c_1391, plain, (![B_383]: (k9_subset_1('#skF_1', B_383, '#skF_4')=k3_xboole_0(B_383, '#skF_4'))), inference(resolution, [status(thm)], [c_66, c_1380])).
% 8.09/2.96  tff(c_2454, plain, (![C_497, B_492, F_493, E_496, D_494, A_495]: (v1_funct_1(k1_tmap_1(A_495, B_492, C_497, D_494, E_496, F_493)) | ~m1_subset_1(F_493, k1_zfmisc_1(k2_zfmisc_1(D_494, B_492))) | ~v1_funct_2(F_493, D_494, B_492) | ~v1_funct_1(F_493) | ~m1_subset_1(E_496, k1_zfmisc_1(k2_zfmisc_1(C_497, B_492))) | ~v1_funct_2(E_496, C_497, B_492) | ~v1_funct_1(E_496) | ~m1_subset_1(D_494, k1_zfmisc_1(A_495)) | v1_xboole_0(D_494) | ~m1_subset_1(C_497, k1_zfmisc_1(A_495)) | v1_xboole_0(C_497) | v1_xboole_0(B_492) | v1_xboole_0(A_495))), inference(cnfTransformation, [status(thm)], [f_183])).
% 8.09/2.96  tff(c_2456, plain, (![A_495, C_497, E_496]: (v1_funct_1(k1_tmap_1(A_495, '#skF_2', C_497, '#skF_4', E_496, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_496, k1_zfmisc_1(k2_zfmisc_1(C_497, '#skF_2'))) | ~v1_funct_2(E_496, C_497, '#skF_2') | ~v1_funct_1(E_496) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_495)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_497, k1_zfmisc_1(A_495)) | v1_xboole_0(C_497) | v1_xboole_0('#skF_2') | v1_xboole_0(A_495))), inference(resolution, [status(thm)], [c_52, c_2454])).
% 8.09/2.96  tff(c_2461, plain, (![A_495, C_497, E_496]: (v1_funct_1(k1_tmap_1(A_495, '#skF_2', C_497, '#skF_4', E_496, '#skF_6')) | ~m1_subset_1(E_496, k1_zfmisc_1(k2_zfmisc_1(C_497, '#skF_2'))) | ~v1_funct_2(E_496, C_497, '#skF_2') | ~v1_funct_1(E_496) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_495)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_497, k1_zfmisc_1(A_495)) | v1_xboole_0(C_497) | v1_xboole_0('#skF_2') | v1_xboole_0(A_495))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_2456])).
% 8.09/2.96  tff(c_2467, plain, (![A_498, C_499, E_500]: (v1_funct_1(k1_tmap_1(A_498, '#skF_2', C_499, '#skF_4', E_500, '#skF_6')) | ~m1_subset_1(E_500, k1_zfmisc_1(k2_zfmisc_1(C_499, '#skF_2'))) | ~v1_funct_2(E_500, C_499, '#skF_2') | ~v1_funct_1(E_500) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_498)) | ~m1_subset_1(C_499, k1_zfmisc_1(A_498)) | v1_xboole_0(C_499) | v1_xboole_0(A_498))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_2461])).
% 8.09/2.96  tff(c_2471, plain, (![A_498]: (v1_funct_1(k1_tmap_1(A_498, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_498)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_498)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_498))), inference(resolution, [status(thm)], [c_58, c_2467])).
% 8.09/2.96  tff(c_2478, plain, (![A_498]: (v1_funct_1(k1_tmap_1(A_498, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_498)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_498)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_498))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_2471])).
% 8.09/2.96  tff(c_2487, plain, (![A_502]: (v1_funct_1(k1_tmap_1(A_502, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_502)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_502)) | v1_xboole_0(A_502))), inference(negUnitSimplification, [status(thm)], [c_72, c_2478])).
% 8.09/2.96  tff(c_2490, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_70, c_2487])).
% 8.09/2.96  tff(c_2493, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2490])).
% 8.09/2.96  tff(c_2494, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_76, c_2493])).
% 8.09/2.96  tff(c_2282, plain, (![A_475, B_476, C_477, D_478]: (k2_partfun1(A_475, B_476, C_477, D_478)=k7_relat_1(C_477, D_478) | ~m1_subset_1(C_477, k1_zfmisc_1(k2_zfmisc_1(A_475, B_476))) | ~v1_funct_1(C_477))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.09/2.96  tff(c_2286, plain, (![D_478]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_478)=k7_relat_1('#skF_5', D_478) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_58, c_2282])).
% 8.09/2.96  tff(c_2292, plain, (![D_478]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_478)=k7_relat_1('#skF_5', D_478))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2286])).
% 8.09/2.96  tff(c_2284, plain, (![D_478]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_478)=k7_relat_1('#skF_6', D_478) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_52, c_2282])).
% 8.09/2.96  tff(c_2289, plain, (![D_478]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_478)=k7_relat_1('#skF_6', D_478))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2284])).
% 8.09/2.96  tff(c_2682, plain, (![A_543, C_547, E_544, D_546, B_545, F_542]: (k2_partfun1(k4_subset_1(A_543, C_547, D_546), B_545, k1_tmap_1(A_543, B_545, C_547, D_546, E_544, F_542), D_546)=F_542 | ~m1_subset_1(k1_tmap_1(A_543, B_545, C_547, D_546, E_544, F_542), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_543, C_547, D_546), B_545))) | ~v1_funct_2(k1_tmap_1(A_543, B_545, C_547, D_546, E_544, F_542), k4_subset_1(A_543, C_547, D_546), B_545) | ~v1_funct_1(k1_tmap_1(A_543, B_545, C_547, D_546, E_544, F_542)) | k2_partfun1(D_546, B_545, F_542, k9_subset_1(A_543, C_547, D_546))!=k2_partfun1(C_547, B_545, E_544, k9_subset_1(A_543, C_547, D_546)) | ~m1_subset_1(F_542, k1_zfmisc_1(k2_zfmisc_1(D_546, B_545))) | ~v1_funct_2(F_542, D_546, B_545) | ~v1_funct_1(F_542) | ~m1_subset_1(E_544, k1_zfmisc_1(k2_zfmisc_1(C_547, B_545))) | ~v1_funct_2(E_544, C_547, B_545) | ~v1_funct_1(E_544) | ~m1_subset_1(D_546, k1_zfmisc_1(A_543)) | v1_xboole_0(D_546) | ~m1_subset_1(C_547, k1_zfmisc_1(A_543)) | v1_xboole_0(C_547) | v1_xboole_0(B_545) | v1_xboole_0(A_543))), inference(cnfTransformation, [status(thm)], [f_149])).
% 8.09/2.96  tff(c_3033, plain, (![A_644, E_645, D_643, F_642, C_646, B_641]: (k2_partfun1(k4_subset_1(A_644, C_646, D_643), B_641, k1_tmap_1(A_644, B_641, C_646, D_643, E_645, F_642), D_643)=F_642 | ~v1_funct_2(k1_tmap_1(A_644, B_641, C_646, D_643, E_645, F_642), k4_subset_1(A_644, C_646, D_643), B_641) | ~v1_funct_1(k1_tmap_1(A_644, B_641, C_646, D_643, E_645, F_642)) | k2_partfun1(D_643, B_641, F_642, k9_subset_1(A_644, C_646, D_643))!=k2_partfun1(C_646, B_641, E_645, k9_subset_1(A_644, C_646, D_643)) | ~m1_subset_1(F_642, k1_zfmisc_1(k2_zfmisc_1(D_643, B_641))) | ~v1_funct_2(F_642, D_643, B_641) | ~v1_funct_1(F_642) | ~m1_subset_1(E_645, k1_zfmisc_1(k2_zfmisc_1(C_646, B_641))) | ~v1_funct_2(E_645, C_646, B_641) | ~v1_funct_1(E_645) | ~m1_subset_1(D_643, k1_zfmisc_1(A_644)) | v1_xboole_0(D_643) | ~m1_subset_1(C_646, k1_zfmisc_1(A_644)) | v1_xboole_0(C_646) | v1_xboole_0(B_641) | v1_xboole_0(A_644))), inference(resolution, [status(thm)], [c_44, c_2682])).
% 8.09/2.96  tff(c_3371, plain, (![C_706, A_704, D_703, F_702, B_701, E_705]: (k2_partfun1(k4_subset_1(A_704, C_706, D_703), B_701, k1_tmap_1(A_704, B_701, C_706, D_703, E_705, F_702), D_703)=F_702 | ~v1_funct_1(k1_tmap_1(A_704, B_701, C_706, D_703, E_705, F_702)) | k2_partfun1(D_703, B_701, F_702, k9_subset_1(A_704, C_706, D_703))!=k2_partfun1(C_706, B_701, E_705, k9_subset_1(A_704, C_706, D_703)) | ~m1_subset_1(F_702, k1_zfmisc_1(k2_zfmisc_1(D_703, B_701))) | ~v1_funct_2(F_702, D_703, B_701) | ~v1_funct_1(F_702) | ~m1_subset_1(E_705, k1_zfmisc_1(k2_zfmisc_1(C_706, B_701))) | ~v1_funct_2(E_705, C_706, B_701) | ~v1_funct_1(E_705) | ~m1_subset_1(D_703, k1_zfmisc_1(A_704)) | v1_xboole_0(D_703) | ~m1_subset_1(C_706, k1_zfmisc_1(A_704)) | v1_xboole_0(C_706) | v1_xboole_0(B_701) | v1_xboole_0(A_704))), inference(resolution, [status(thm)], [c_46, c_3033])).
% 8.09/2.96  tff(c_3375, plain, (![A_704, C_706, E_705]: (k2_partfun1(k4_subset_1(A_704, C_706, '#skF_4'), '#skF_2', k1_tmap_1(A_704, '#skF_2', C_706, '#skF_4', E_705, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_704, '#skF_2', C_706, '#skF_4', E_705, '#skF_6')) | k2_partfun1(C_706, '#skF_2', E_705, k9_subset_1(A_704, C_706, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_704, C_706, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_705, k1_zfmisc_1(k2_zfmisc_1(C_706, '#skF_2'))) | ~v1_funct_2(E_705, C_706, '#skF_2') | ~v1_funct_1(E_705) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_704)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_706, k1_zfmisc_1(A_704)) | v1_xboole_0(C_706) | v1_xboole_0('#skF_2') | v1_xboole_0(A_704))), inference(resolution, [status(thm)], [c_52, c_3371])).
% 8.09/2.96  tff(c_3381, plain, (![A_704, C_706, E_705]: (k2_partfun1(k4_subset_1(A_704, C_706, '#skF_4'), '#skF_2', k1_tmap_1(A_704, '#skF_2', C_706, '#skF_4', E_705, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_704, '#skF_2', C_706, '#skF_4', E_705, '#skF_6')) | k2_partfun1(C_706, '#skF_2', E_705, k9_subset_1(A_704, C_706, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_704, C_706, '#skF_4')) | ~m1_subset_1(E_705, k1_zfmisc_1(k2_zfmisc_1(C_706, '#skF_2'))) | ~v1_funct_2(E_705, C_706, '#skF_2') | ~v1_funct_1(E_705) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_704)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_706, k1_zfmisc_1(A_704)) | v1_xboole_0(C_706) | v1_xboole_0('#skF_2') | v1_xboole_0(A_704))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_2289, c_3375])).
% 8.09/2.96  tff(c_3750, plain, (![A_751, C_752, E_753]: (k2_partfun1(k4_subset_1(A_751, C_752, '#skF_4'), '#skF_2', k1_tmap_1(A_751, '#skF_2', C_752, '#skF_4', E_753, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_751, '#skF_2', C_752, '#skF_4', E_753, '#skF_6')) | k2_partfun1(C_752, '#skF_2', E_753, k9_subset_1(A_751, C_752, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_751, C_752, '#skF_4')) | ~m1_subset_1(E_753, k1_zfmisc_1(k2_zfmisc_1(C_752, '#skF_2'))) | ~v1_funct_2(E_753, C_752, '#skF_2') | ~v1_funct_1(E_753) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_751)) | ~m1_subset_1(C_752, k1_zfmisc_1(A_751)) | v1_xboole_0(C_752) | v1_xboole_0(A_751))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_3381])).
% 8.09/2.96  tff(c_3757, plain, (![A_751]: (k2_partfun1(k4_subset_1(A_751, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_751, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_751, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_751, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_751, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_751)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_751)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_751))), inference(resolution, [status(thm)], [c_58, c_3750])).
% 8.09/2.96  tff(c_3767, plain, (![A_751]: (k2_partfun1(k4_subset_1(A_751, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_751, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_751, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_751, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_751, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_751)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_751)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_751))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_2292, c_3757])).
% 8.09/2.96  tff(c_3769, plain, (![A_754]: (k2_partfun1(k4_subset_1(A_754, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_754, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_754, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_754, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_754, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_754)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_754)) | v1_xboole_0(A_754))), inference(negUnitSimplification, [status(thm)], [c_72, c_3767])).
% 8.09/2.96  tff(c_267, plain, (![C_241, A_242, B_243]: (v1_relat_1(C_241) | ~m1_subset_1(C_241, k1_zfmisc_1(k2_zfmisc_1(A_242, B_243))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.09/2.96  tff(c_274, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_267])).
% 8.09/2.96  tff(c_162, plain, (![B_236, A_237]: (k3_xboole_0(B_236, A_237)=k3_xboole_0(A_237, B_236))), inference(superposition, [status(thm), theory('equality')], [c_138, c_14])).
% 8.09/2.96  tff(c_178, plain, (![A_237]: (k3_xboole_0(k1_xboole_0, A_237)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_162, c_6])).
% 8.09/2.96  tff(c_299, plain, (![A_252, B_253]: (k7_relat_1(A_252, B_253)=k1_xboole_0 | ~r1_xboole_0(B_253, k1_relat_1(A_252)) | ~v1_relat_1(A_252))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.09/2.96  tff(c_969, plain, (![A_339, A_340]: (k7_relat_1(A_339, A_340)=k1_xboole_0 | ~v1_relat_1(A_339) | k3_xboole_0(A_340, k1_relat_1(A_339))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_299])).
% 8.09/2.96  tff(c_993, plain, (![A_341]: (k7_relat_1(A_341, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_341))), inference(superposition, [status(thm), theory('equality')], [c_178, c_969])).
% 8.09/2.96  tff(c_1001, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_274, c_993])).
% 8.09/2.96  tff(c_305, plain, (![A_254, B_255]: (r1_xboole_0(A_254, B_255) | ~r1_subset_1(A_254, B_255) | v1_xboole_0(B_255) | v1_xboole_0(A_254))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.09/2.96  tff(c_1063, plain, (![A_348, B_349]: (k3_xboole_0(A_348, B_349)=k1_xboole_0 | ~r1_subset_1(A_348, B_349) | v1_xboole_0(B_349) | v1_xboole_0(A_348))), inference(resolution, [status(thm)], [c_305, c_2])).
% 8.09/2.96  tff(c_1066, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_64, c_1063])).
% 8.09/2.96  tff(c_1068, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_144, c_1066])).
% 8.09/2.96  tff(c_1069, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_72, c_68, c_1068])).
% 8.09/2.96  tff(c_275, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_267])).
% 8.09/2.96  tff(c_1000, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_275, c_993])).
% 8.09/2.96  tff(c_1034, plain, (![A_342, B_343, C_344, D_345]: (k2_partfun1(A_342, B_343, C_344, D_345)=k7_relat_1(C_344, D_345) | ~m1_subset_1(C_344, k1_zfmisc_1(k2_zfmisc_1(A_342, B_343))) | ~v1_funct_1(C_344))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.09/2.96  tff(c_1038, plain, (![D_345]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_345)=k7_relat_1('#skF_5', D_345) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_58, c_1034])).
% 8.09/2.96  tff(c_1044, plain, (![D_345]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_345)=k7_relat_1('#skF_5', D_345))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1038])).
% 8.09/2.96  tff(c_1036, plain, (![D_345]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_345)=k7_relat_1('#skF_6', D_345) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_52, c_1034])).
% 8.09/2.96  tff(c_1041, plain, (![D_345]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_345)=k7_relat_1('#skF_6', D_345))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1036])).
% 8.09/2.96  tff(c_904, plain, (![A_332, B_333, C_334]: (k9_subset_1(A_332, B_333, C_334)=k3_xboole_0(B_333, C_334) | ~m1_subset_1(C_334, k1_zfmisc_1(A_332)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.09/2.96  tff(c_915, plain, (![B_333]: (k9_subset_1('#skF_1', B_333, '#skF_4')=k3_xboole_0(B_333, '#skF_4'))), inference(resolution, [status(thm)], [c_66, c_904])).
% 8.09/2.96  tff(c_50, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.09/2.96  tff(c_161, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_50])).
% 8.09/2.96  tff(c_931, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_915, c_915, c_161])).
% 8.09/2.96  tff(c_932, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_4', '#skF_3'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_144, c_931])).
% 8.09/2.96  tff(c_1201, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1001, c_1069, c_1000, c_1069, c_1044, c_1041, c_932])).
% 8.09/2.96  tff(c_1202, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_50])).
% 8.09/2.96  tff(c_1340, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_1202])).
% 8.09/2.96  tff(c_3780, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3769, c_1340])).
% 8.09/2.96  tff(c_3794, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_2236, c_2321, c_144, c_2235, c_2321, c_144, c_1391, c_1391, c_2494, c_3780])).
% 8.09/2.96  tff(c_3796, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_3794])).
% 8.09/2.96  tff(c_3797, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_1202])).
% 8.09/2.96  tff(c_6259, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6250, c_3797])).
% 8.09/2.96  tff(c_6270, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_4727, c_4781, c_144, c_4726, c_4781, c_144, c_4303, c_4303, c_4956, c_6259])).
% 8.09/2.96  tff(c_6272, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_6270])).
% 8.09/2.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.09/2.96  
% 8.09/2.96  Inference rules
% 8.09/2.96  ----------------------
% 8.09/2.96  #Ref     : 0
% 8.09/2.96  #Sup     : 1291
% 8.09/2.96  #Fact    : 0
% 8.09/2.96  #Define  : 0
% 8.09/2.96  #Split   : 41
% 8.09/2.96  #Chain   : 0
% 8.09/2.96  #Close   : 0
% 8.09/2.96  
% 8.09/2.96  Ordering : KBO
% 8.09/2.96  
% 8.09/2.96  Simplification rules
% 8.09/2.96  ----------------------
% 8.09/2.96  #Subsume      : 130
% 8.09/2.96  #Demod        : 955
% 8.09/2.96  #Tautology    : 671
% 8.09/2.96  #SimpNegUnit  : 239
% 8.09/2.96  #BackRed      : 17
% 8.09/2.96  
% 8.09/2.96  #Partial instantiations: 0
% 8.09/2.96  #Strategies tried      : 1
% 8.09/2.96  
% 8.09/2.96  Timing (in seconds)
% 8.09/2.96  ----------------------
% 8.09/2.97  Preprocessing        : 0.44
% 8.09/2.97  Parsing              : 0.21
% 8.09/2.97  CNF conversion       : 0.06
% 8.09/2.97  Main loop            : 1.72
% 8.09/2.97  Inferencing          : 0.60
% 8.09/2.97  Reduction            : 0.62
% 8.09/2.97  Demodulation         : 0.46
% 8.09/2.97  BG Simplification    : 0.06
% 8.09/2.97  Subsumption          : 0.34
% 8.09/2.97  Abstraction          : 0.07
% 8.09/2.97  MUC search           : 0.00
% 8.09/2.97  Cooper               : 0.00
% 8.09/2.97  Total                : 2.23
% 8.09/2.97  Index Insertion      : 0.00
% 8.09/2.97  Index Deletion       : 0.00
% 8.09/2.97  Index Matching       : 0.00
% 8.09/2.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
