%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:13 EST 2020

% Result     : Theorem 7.97s
% Output     : CNFRefutation 7.97s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 437 expanded)
%              Number of leaves         :   43 ( 181 expanded)
%              Depth                    :   12
%              Number of atoms          :  572 (2450 expanded)
%              Number of equality atoms :   99 ( 450 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r1_subset_1,type,(
    r1_subset_1: ( $i * $i ) > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_33,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

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

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

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

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_675,plain,(
    ! [C_314,A_315,B_316] :
      ( v1_relat_1(C_314)
      | ~ m1_subset_1(C_314,k1_zfmisc_1(k2_zfmisc_1(A_315,B_316))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_683,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_675])).

tff(c_6,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_84,plain,(
    ! [A_226,B_227] : r1_xboole_0(k4_xboole_0(A_226,B_227),B_227) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_87,plain,(
    ! [A_3] : r1_xboole_0(k1_xboole_0,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_84])).

tff(c_727,plain,(
    ! [A_325,B_326] :
      ( k7_relat_1(A_325,B_326) = k1_xboole_0
      | ~ r1_xboole_0(B_326,k1_relat_1(A_325))
      | ~ v1_relat_1(A_325) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_743,plain,(
    ! [A_327] :
      ( k7_relat_1(A_327,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_327) ) ),
    inference(resolution,[status(thm)],[c_87,c_727])).

tff(c_750,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_683,c_743])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_682,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_675])).

tff(c_751,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_682,c_743])).

tff(c_72,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_64,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_3128,plain,(
    ! [A_693,B_694] :
      ( r1_xboole_0(A_693,B_694)
      | ~ r1_subset_1(A_693,B_694)
      | v1_xboole_0(B_694)
      | v1_xboole_0(A_693) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4193,plain,(
    ! [A_800,B_801] :
      ( k3_xboole_0(A_800,B_801) = k1_xboole_0
      | ~ r1_subset_1(A_800,B_801)
      | v1_xboole_0(B_801)
      | v1_xboole_0(A_800) ) ),
    inference(resolution,[status(thm)],[c_3128,c_2])).

tff(c_4199,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_4193])).

tff(c_4203,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_68,c_4199])).

tff(c_3943,plain,(
    ! [A_783,B_784,C_785] :
      ( k9_subset_1(A_783,B_784,C_785) = k3_xboole_0(B_784,C_785)
      | ~ m1_subset_1(C_785,k1_zfmisc_1(A_783)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3954,plain,(
    ! [B_784] : k9_subset_1('#skF_1',B_784,'#skF_4') = k3_xboole_0(B_784,'#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_3943])).

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

tff(c_4321,plain,(
    ! [D_819,A_820,C_822,F_818,B_817,E_821] :
      ( v1_funct_1(k1_tmap_1(A_820,B_817,C_822,D_819,E_821,F_818))
      | ~ m1_subset_1(F_818,k1_zfmisc_1(k2_zfmisc_1(D_819,B_817)))
      | ~ v1_funct_2(F_818,D_819,B_817)
      | ~ v1_funct_1(F_818)
      | ~ m1_subset_1(E_821,k1_zfmisc_1(k2_zfmisc_1(C_822,B_817)))
      | ~ v1_funct_2(E_821,C_822,B_817)
      | ~ v1_funct_1(E_821)
      | ~ m1_subset_1(D_819,k1_zfmisc_1(A_820))
      | v1_xboole_0(D_819)
      | ~ m1_subset_1(C_822,k1_zfmisc_1(A_820))
      | v1_xboole_0(C_822)
      | v1_xboole_0(B_817)
      | v1_xboole_0(A_820) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_4323,plain,(
    ! [A_820,C_822,E_821] :
      ( v1_funct_1(k1_tmap_1(A_820,'#skF_2',C_822,'#skF_4',E_821,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_821,k1_zfmisc_1(k2_zfmisc_1(C_822,'#skF_2')))
      | ~ v1_funct_2(E_821,C_822,'#skF_2')
      | ~ v1_funct_1(E_821)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_820))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_822,k1_zfmisc_1(A_820))
      | v1_xboole_0(C_822)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_820) ) ),
    inference(resolution,[status(thm)],[c_52,c_4321])).

tff(c_4328,plain,(
    ! [A_820,C_822,E_821] :
      ( v1_funct_1(k1_tmap_1(A_820,'#skF_2',C_822,'#skF_4',E_821,'#skF_6'))
      | ~ m1_subset_1(E_821,k1_zfmisc_1(k2_zfmisc_1(C_822,'#skF_2')))
      | ~ v1_funct_2(E_821,C_822,'#skF_2')
      | ~ v1_funct_1(E_821)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_820))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_822,k1_zfmisc_1(A_820))
      | v1_xboole_0(C_822)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_820) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4323])).

tff(c_4334,plain,(
    ! [A_823,C_824,E_825] :
      ( v1_funct_1(k1_tmap_1(A_823,'#skF_2',C_824,'#skF_4',E_825,'#skF_6'))
      | ~ m1_subset_1(E_825,k1_zfmisc_1(k2_zfmisc_1(C_824,'#skF_2')))
      | ~ v1_funct_2(E_825,C_824,'#skF_2')
      | ~ v1_funct_1(E_825)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_823))
      | ~ m1_subset_1(C_824,k1_zfmisc_1(A_823))
      | v1_xboole_0(C_824)
      | v1_xboole_0(A_823) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_4328])).

tff(c_4338,plain,(
    ! [A_823] :
      ( v1_funct_1(k1_tmap_1(A_823,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_823))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_823))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_823) ) ),
    inference(resolution,[status(thm)],[c_58,c_4334])).

tff(c_4345,plain,(
    ! [A_823] :
      ( v1_funct_1(k1_tmap_1(A_823,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_823))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_823))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_823) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_4338])).

tff(c_4355,plain,(
    ! [A_833] :
      ( v1_funct_1(k1_tmap_1(A_833,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_833))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_833))
      | v1_xboole_0(A_833) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_4345])).

tff(c_4358,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_4355])).

tff(c_4361,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_4358])).

tff(c_4362,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_4361])).

tff(c_4208,plain,(
    ! [A_802,B_803,C_804,D_805] :
      ( k2_partfun1(A_802,B_803,C_804,D_805) = k7_relat_1(C_804,D_805)
      | ~ m1_subset_1(C_804,k1_zfmisc_1(k2_zfmisc_1(A_802,B_803)))
      | ~ v1_funct_1(C_804) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_4212,plain,(
    ! [D_805] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_805) = k7_relat_1('#skF_5',D_805)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_58,c_4208])).

tff(c_4218,plain,(
    ! [D_805] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_805) = k7_relat_1('#skF_5',D_805) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_4212])).

tff(c_4210,plain,(
    ! [D_805] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_805) = k7_relat_1('#skF_6',D_805)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_52,c_4208])).

tff(c_4215,plain,(
    ! [D_805] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_805) = k7_relat_1('#skF_6',D_805) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_4210])).

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

tff(c_4518,plain,(
    ! [B_862,F_859,A_860,C_864,D_863,E_861] :
      ( k2_partfun1(k4_subset_1(A_860,C_864,D_863),B_862,k1_tmap_1(A_860,B_862,C_864,D_863,E_861,F_859),C_864) = E_861
      | ~ m1_subset_1(k1_tmap_1(A_860,B_862,C_864,D_863,E_861,F_859),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_860,C_864,D_863),B_862)))
      | ~ v1_funct_2(k1_tmap_1(A_860,B_862,C_864,D_863,E_861,F_859),k4_subset_1(A_860,C_864,D_863),B_862)
      | ~ v1_funct_1(k1_tmap_1(A_860,B_862,C_864,D_863,E_861,F_859))
      | k2_partfun1(D_863,B_862,F_859,k9_subset_1(A_860,C_864,D_863)) != k2_partfun1(C_864,B_862,E_861,k9_subset_1(A_860,C_864,D_863))
      | ~ m1_subset_1(F_859,k1_zfmisc_1(k2_zfmisc_1(D_863,B_862)))
      | ~ v1_funct_2(F_859,D_863,B_862)
      | ~ v1_funct_1(F_859)
      | ~ m1_subset_1(E_861,k1_zfmisc_1(k2_zfmisc_1(C_864,B_862)))
      | ~ v1_funct_2(E_861,C_864,B_862)
      | ~ v1_funct_1(E_861)
      | ~ m1_subset_1(D_863,k1_zfmisc_1(A_860))
      | v1_xboole_0(D_863)
      | ~ m1_subset_1(C_864,k1_zfmisc_1(A_860))
      | v1_xboole_0(C_864)
      | v1_xboole_0(B_862)
      | v1_xboole_0(A_860) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_4954,plain,(
    ! [D_965,B_963,E_967,C_968,A_966,F_964] :
      ( k2_partfun1(k4_subset_1(A_966,C_968,D_965),B_963,k1_tmap_1(A_966,B_963,C_968,D_965,E_967,F_964),C_968) = E_967
      | ~ v1_funct_2(k1_tmap_1(A_966,B_963,C_968,D_965,E_967,F_964),k4_subset_1(A_966,C_968,D_965),B_963)
      | ~ v1_funct_1(k1_tmap_1(A_966,B_963,C_968,D_965,E_967,F_964))
      | k2_partfun1(D_965,B_963,F_964,k9_subset_1(A_966,C_968,D_965)) != k2_partfun1(C_968,B_963,E_967,k9_subset_1(A_966,C_968,D_965))
      | ~ m1_subset_1(F_964,k1_zfmisc_1(k2_zfmisc_1(D_965,B_963)))
      | ~ v1_funct_2(F_964,D_965,B_963)
      | ~ v1_funct_1(F_964)
      | ~ m1_subset_1(E_967,k1_zfmisc_1(k2_zfmisc_1(C_968,B_963)))
      | ~ v1_funct_2(E_967,C_968,B_963)
      | ~ v1_funct_1(E_967)
      | ~ m1_subset_1(D_965,k1_zfmisc_1(A_966))
      | v1_xboole_0(D_965)
      | ~ m1_subset_1(C_968,k1_zfmisc_1(A_966))
      | v1_xboole_0(C_968)
      | v1_xboole_0(B_963)
      | v1_xboole_0(A_966) ) ),
    inference(resolution,[status(thm)],[c_44,c_4518])).

tff(c_5332,plain,(
    ! [E_1024,B_1020,F_1021,D_1022,C_1025,A_1023] :
      ( k2_partfun1(k4_subset_1(A_1023,C_1025,D_1022),B_1020,k1_tmap_1(A_1023,B_1020,C_1025,D_1022,E_1024,F_1021),C_1025) = E_1024
      | ~ v1_funct_1(k1_tmap_1(A_1023,B_1020,C_1025,D_1022,E_1024,F_1021))
      | k2_partfun1(D_1022,B_1020,F_1021,k9_subset_1(A_1023,C_1025,D_1022)) != k2_partfun1(C_1025,B_1020,E_1024,k9_subset_1(A_1023,C_1025,D_1022))
      | ~ m1_subset_1(F_1021,k1_zfmisc_1(k2_zfmisc_1(D_1022,B_1020)))
      | ~ v1_funct_2(F_1021,D_1022,B_1020)
      | ~ v1_funct_1(F_1021)
      | ~ m1_subset_1(E_1024,k1_zfmisc_1(k2_zfmisc_1(C_1025,B_1020)))
      | ~ v1_funct_2(E_1024,C_1025,B_1020)
      | ~ v1_funct_1(E_1024)
      | ~ m1_subset_1(D_1022,k1_zfmisc_1(A_1023))
      | v1_xboole_0(D_1022)
      | ~ m1_subset_1(C_1025,k1_zfmisc_1(A_1023))
      | v1_xboole_0(C_1025)
      | v1_xboole_0(B_1020)
      | v1_xboole_0(A_1023) ) ),
    inference(resolution,[status(thm)],[c_46,c_4954])).

tff(c_5336,plain,(
    ! [A_1023,C_1025,E_1024] :
      ( k2_partfun1(k4_subset_1(A_1023,C_1025,'#skF_4'),'#skF_2',k1_tmap_1(A_1023,'#skF_2',C_1025,'#skF_4',E_1024,'#skF_6'),C_1025) = E_1024
      | ~ v1_funct_1(k1_tmap_1(A_1023,'#skF_2',C_1025,'#skF_4',E_1024,'#skF_6'))
      | k2_partfun1(C_1025,'#skF_2',E_1024,k9_subset_1(A_1023,C_1025,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_1023,C_1025,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1024,k1_zfmisc_1(k2_zfmisc_1(C_1025,'#skF_2')))
      | ~ v1_funct_2(E_1024,C_1025,'#skF_2')
      | ~ v1_funct_1(E_1024)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1023))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1025,k1_zfmisc_1(A_1023))
      | v1_xboole_0(C_1025)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1023) ) ),
    inference(resolution,[status(thm)],[c_52,c_5332])).

tff(c_5342,plain,(
    ! [A_1023,C_1025,E_1024] :
      ( k2_partfun1(k4_subset_1(A_1023,C_1025,'#skF_4'),'#skF_2',k1_tmap_1(A_1023,'#skF_2',C_1025,'#skF_4',E_1024,'#skF_6'),C_1025) = E_1024
      | ~ v1_funct_1(k1_tmap_1(A_1023,'#skF_2',C_1025,'#skF_4',E_1024,'#skF_6'))
      | k2_partfun1(C_1025,'#skF_2',E_1024,k9_subset_1(A_1023,C_1025,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1023,C_1025,'#skF_4'))
      | ~ m1_subset_1(E_1024,k1_zfmisc_1(k2_zfmisc_1(C_1025,'#skF_2')))
      | ~ v1_funct_2(E_1024,C_1025,'#skF_2')
      | ~ v1_funct_1(E_1024)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1023))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1025,k1_zfmisc_1(A_1023))
      | v1_xboole_0(C_1025)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1023) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4215,c_5336])).

tff(c_5714,plain,(
    ! [A_1072,C_1073,E_1074] :
      ( k2_partfun1(k4_subset_1(A_1072,C_1073,'#skF_4'),'#skF_2',k1_tmap_1(A_1072,'#skF_2',C_1073,'#skF_4',E_1074,'#skF_6'),C_1073) = E_1074
      | ~ v1_funct_1(k1_tmap_1(A_1072,'#skF_2',C_1073,'#skF_4',E_1074,'#skF_6'))
      | k2_partfun1(C_1073,'#skF_2',E_1074,k9_subset_1(A_1072,C_1073,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1072,C_1073,'#skF_4'))
      | ~ m1_subset_1(E_1074,k1_zfmisc_1(k2_zfmisc_1(C_1073,'#skF_2')))
      | ~ v1_funct_2(E_1074,C_1073,'#skF_2')
      | ~ v1_funct_1(E_1074)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1072))
      | ~ m1_subset_1(C_1073,k1_zfmisc_1(A_1072))
      | v1_xboole_0(C_1073)
      | v1_xboole_0(A_1072) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_5342])).

tff(c_5721,plain,(
    ! [A_1072] :
      ( k2_partfun1(k4_subset_1(A_1072,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1072,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1072,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1072,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1072,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1072))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1072))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1072) ) ),
    inference(resolution,[status(thm)],[c_58,c_5714])).

tff(c_5731,plain,(
    ! [A_1072] :
      ( k2_partfun1(k4_subset_1(A_1072,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1072,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1072,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1072,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1072,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1072))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1072))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1072) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_4218,c_5721])).

tff(c_5744,plain,(
    ! [A_1081] :
      ( k2_partfun1(k4_subset_1(A_1081,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1081,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1081,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1081,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1081,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1081))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1081))
      | v1_xboole_0(A_1081) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_5731])).

tff(c_774,plain,(
    ! [A_331,B_332] :
      ( r1_xboole_0(A_331,B_332)
      | ~ r1_subset_1(A_331,B_332)
      | v1_xboole_0(B_332)
      | v1_xboole_0(A_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1656,plain,(
    ! [A_417,B_418] :
      ( k3_xboole_0(A_417,B_418) = k1_xboole_0
      | ~ r1_subset_1(A_417,B_418)
      | v1_xboole_0(B_418)
      | v1_xboole_0(A_417) ) ),
    inference(resolution,[status(thm)],[c_774,c_2])).

tff(c_1662,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_1656])).

tff(c_1667,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_68,c_1662])).

tff(c_802,plain,(
    ! [A_335,B_336,C_337] :
      ( k9_subset_1(A_335,B_336,C_337) = k3_xboole_0(B_336,C_337)
      | ~ m1_subset_1(C_337,k1_zfmisc_1(A_335)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_813,plain,(
    ! [B_336] : k9_subset_1('#skF_1',B_336,'#skF_4') = k3_xboole_0(B_336,'#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_802])).

tff(c_1705,plain,(
    ! [A_427,D_426,B_424,C_429,F_425,E_428] :
      ( v1_funct_1(k1_tmap_1(A_427,B_424,C_429,D_426,E_428,F_425))
      | ~ m1_subset_1(F_425,k1_zfmisc_1(k2_zfmisc_1(D_426,B_424)))
      | ~ v1_funct_2(F_425,D_426,B_424)
      | ~ v1_funct_1(F_425)
      | ~ m1_subset_1(E_428,k1_zfmisc_1(k2_zfmisc_1(C_429,B_424)))
      | ~ v1_funct_2(E_428,C_429,B_424)
      | ~ v1_funct_1(E_428)
      | ~ m1_subset_1(D_426,k1_zfmisc_1(A_427))
      | v1_xboole_0(D_426)
      | ~ m1_subset_1(C_429,k1_zfmisc_1(A_427))
      | v1_xboole_0(C_429)
      | v1_xboole_0(B_424)
      | v1_xboole_0(A_427) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_1707,plain,(
    ! [A_427,C_429,E_428] :
      ( v1_funct_1(k1_tmap_1(A_427,'#skF_2',C_429,'#skF_4',E_428,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_428,k1_zfmisc_1(k2_zfmisc_1(C_429,'#skF_2')))
      | ~ v1_funct_2(E_428,C_429,'#skF_2')
      | ~ v1_funct_1(E_428)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_427))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_429,k1_zfmisc_1(A_427))
      | v1_xboole_0(C_429)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_427) ) ),
    inference(resolution,[status(thm)],[c_52,c_1705])).

tff(c_1712,plain,(
    ! [A_427,C_429,E_428] :
      ( v1_funct_1(k1_tmap_1(A_427,'#skF_2',C_429,'#skF_4',E_428,'#skF_6'))
      | ~ m1_subset_1(E_428,k1_zfmisc_1(k2_zfmisc_1(C_429,'#skF_2')))
      | ~ v1_funct_2(E_428,C_429,'#skF_2')
      | ~ v1_funct_1(E_428)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_427))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_429,k1_zfmisc_1(A_427))
      | v1_xboole_0(C_429)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_427) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_1707])).

tff(c_1770,plain,(
    ! [A_443,C_444,E_445] :
      ( v1_funct_1(k1_tmap_1(A_443,'#skF_2',C_444,'#skF_4',E_445,'#skF_6'))
      | ~ m1_subset_1(E_445,k1_zfmisc_1(k2_zfmisc_1(C_444,'#skF_2')))
      | ~ v1_funct_2(E_445,C_444,'#skF_2')
      | ~ v1_funct_1(E_445)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_443))
      | ~ m1_subset_1(C_444,k1_zfmisc_1(A_443))
      | v1_xboole_0(C_444)
      | v1_xboole_0(A_443) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_1712])).

tff(c_1774,plain,(
    ! [A_443] :
      ( v1_funct_1(k1_tmap_1(A_443,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_443))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_443))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_443) ) ),
    inference(resolution,[status(thm)],[c_58,c_1770])).

tff(c_1781,plain,(
    ! [A_443] :
      ( v1_funct_1(k1_tmap_1(A_443,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_443))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_443))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_443) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1774])).

tff(c_1790,plain,(
    ! [A_447] :
      ( v1_funct_1(k1_tmap_1(A_447,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_447))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_447))
      | v1_xboole_0(A_447) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1781])).

tff(c_1793,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_1790])).

tff(c_1796,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1793])).

tff(c_1797,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1796])).

tff(c_1519,plain,(
    ! [A_404,B_405,C_406,D_407] :
      ( k2_partfun1(A_404,B_405,C_406,D_407) = k7_relat_1(C_406,D_407)
      | ~ m1_subset_1(C_406,k1_zfmisc_1(k2_zfmisc_1(A_404,B_405)))
      | ~ v1_funct_1(C_406) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1523,plain,(
    ! [D_407] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_407) = k7_relat_1('#skF_5',D_407)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_58,c_1519])).

tff(c_1529,plain,(
    ! [D_407] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_407) = k7_relat_1('#skF_5',D_407) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1523])).

tff(c_1521,plain,(
    ! [D_407] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_407) = k7_relat_1('#skF_6',D_407)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_52,c_1519])).

tff(c_1526,plain,(
    ! [D_407] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_407) = k7_relat_1('#skF_6',D_407) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1521])).

tff(c_1875,plain,(
    ! [F_463,E_465,D_467,C_468,B_466,A_464] :
      ( k2_partfun1(k4_subset_1(A_464,C_468,D_467),B_466,k1_tmap_1(A_464,B_466,C_468,D_467,E_465,F_463),D_467) = F_463
      | ~ m1_subset_1(k1_tmap_1(A_464,B_466,C_468,D_467,E_465,F_463),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_464,C_468,D_467),B_466)))
      | ~ v1_funct_2(k1_tmap_1(A_464,B_466,C_468,D_467,E_465,F_463),k4_subset_1(A_464,C_468,D_467),B_466)
      | ~ v1_funct_1(k1_tmap_1(A_464,B_466,C_468,D_467,E_465,F_463))
      | k2_partfun1(D_467,B_466,F_463,k9_subset_1(A_464,C_468,D_467)) != k2_partfun1(C_468,B_466,E_465,k9_subset_1(A_464,C_468,D_467))
      | ~ m1_subset_1(F_463,k1_zfmisc_1(k2_zfmisc_1(D_467,B_466)))
      | ~ v1_funct_2(F_463,D_467,B_466)
      | ~ v1_funct_1(F_463)
      | ~ m1_subset_1(E_465,k1_zfmisc_1(k2_zfmisc_1(C_468,B_466)))
      | ~ v1_funct_2(E_465,C_468,B_466)
      | ~ v1_funct_1(E_465)
      | ~ m1_subset_1(D_467,k1_zfmisc_1(A_464))
      | v1_xboole_0(D_467)
      | ~ m1_subset_1(C_468,k1_zfmisc_1(A_464))
      | v1_xboole_0(C_468)
      | v1_xboole_0(B_466)
      | v1_xboole_0(A_464) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_2192,plain,(
    ! [F_582,D_583,A_584,C_586,E_585,B_581] :
      ( k2_partfun1(k4_subset_1(A_584,C_586,D_583),B_581,k1_tmap_1(A_584,B_581,C_586,D_583,E_585,F_582),D_583) = F_582
      | ~ v1_funct_2(k1_tmap_1(A_584,B_581,C_586,D_583,E_585,F_582),k4_subset_1(A_584,C_586,D_583),B_581)
      | ~ v1_funct_1(k1_tmap_1(A_584,B_581,C_586,D_583,E_585,F_582))
      | k2_partfun1(D_583,B_581,F_582,k9_subset_1(A_584,C_586,D_583)) != k2_partfun1(C_586,B_581,E_585,k9_subset_1(A_584,C_586,D_583))
      | ~ m1_subset_1(F_582,k1_zfmisc_1(k2_zfmisc_1(D_583,B_581)))
      | ~ v1_funct_2(F_582,D_583,B_581)
      | ~ v1_funct_1(F_582)
      | ~ m1_subset_1(E_585,k1_zfmisc_1(k2_zfmisc_1(C_586,B_581)))
      | ~ v1_funct_2(E_585,C_586,B_581)
      | ~ v1_funct_1(E_585)
      | ~ m1_subset_1(D_583,k1_zfmisc_1(A_584))
      | v1_xboole_0(D_583)
      | ~ m1_subset_1(C_586,k1_zfmisc_1(A_584))
      | v1_xboole_0(C_586)
      | v1_xboole_0(B_581)
      | v1_xboole_0(A_584) ) ),
    inference(resolution,[status(thm)],[c_44,c_1875])).

tff(c_2709,plain,(
    ! [F_636,D_637,C_640,A_638,E_639,B_635] :
      ( k2_partfun1(k4_subset_1(A_638,C_640,D_637),B_635,k1_tmap_1(A_638,B_635,C_640,D_637,E_639,F_636),D_637) = F_636
      | ~ v1_funct_1(k1_tmap_1(A_638,B_635,C_640,D_637,E_639,F_636))
      | k2_partfun1(D_637,B_635,F_636,k9_subset_1(A_638,C_640,D_637)) != k2_partfun1(C_640,B_635,E_639,k9_subset_1(A_638,C_640,D_637))
      | ~ m1_subset_1(F_636,k1_zfmisc_1(k2_zfmisc_1(D_637,B_635)))
      | ~ v1_funct_2(F_636,D_637,B_635)
      | ~ v1_funct_1(F_636)
      | ~ m1_subset_1(E_639,k1_zfmisc_1(k2_zfmisc_1(C_640,B_635)))
      | ~ v1_funct_2(E_639,C_640,B_635)
      | ~ v1_funct_1(E_639)
      | ~ m1_subset_1(D_637,k1_zfmisc_1(A_638))
      | v1_xboole_0(D_637)
      | ~ m1_subset_1(C_640,k1_zfmisc_1(A_638))
      | v1_xboole_0(C_640)
      | v1_xboole_0(B_635)
      | v1_xboole_0(A_638) ) ),
    inference(resolution,[status(thm)],[c_46,c_2192])).

tff(c_2713,plain,(
    ! [A_638,C_640,E_639] :
      ( k2_partfun1(k4_subset_1(A_638,C_640,'#skF_4'),'#skF_2',k1_tmap_1(A_638,'#skF_2',C_640,'#skF_4',E_639,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_638,'#skF_2',C_640,'#skF_4',E_639,'#skF_6'))
      | k2_partfun1(C_640,'#skF_2',E_639,k9_subset_1(A_638,C_640,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_638,C_640,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_639,k1_zfmisc_1(k2_zfmisc_1(C_640,'#skF_2')))
      | ~ v1_funct_2(E_639,C_640,'#skF_2')
      | ~ v1_funct_1(E_639)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_638))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_640,k1_zfmisc_1(A_638))
      | v1_xboole_0(C_640)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_638) ) ),
    inference(resolution,[status(thm)],[c_52,c_2709])).

tff(c_2719,plain,(
    ! [A_638,C_640,E_639] :
      ( k2_partfun1(k4_subset_1(A_638,C_640,'#skF_4'),'#skF_2',k1_tmap_1(A_638,'#skF_2',C_640,'#skF_4',E_639,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_638,'#skF_2',C_640,'#skF_4',E_639,'#skF_6'))
      | k2_partfun1(C_640,'#skF_2',E_639,k9_subset_1(A_638,C_640,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_638,C_640,'#skF_4'))
      | ~ m1_subset_1(E_639,k1_zfmisc_1(k2_zfmisc_1(C_640,'#skF_2')))
      | ~ v1_funct_2(E_639,C_640,'#skF_2')
      | ~ v1_funct_1(E_639)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_638))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_640,k1_zfmisc_1(A_638))
      | v1_xboole_0(C_640)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_638) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_1526,c_2713])).

tff(c_3044,plain,(
    ! [A_684,C_685,E_686] :
      ( k2_partfun1(k4_subset_1(A_684,C_685,'#skF_4'),'#skF_2',k1_tmap_1(A_684,'#skF_2',C_685,'#skF_4',E_686,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_684,'#skF_2',C_685,'#skF_4',E_686,'#skF_6'))
      | k2_partfun1(C_685,'#skF_2',E_686,k9_subset_1(A_684,C_685,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_684,C_685,'#skF_4'))
      | ~ m1_subset_1(E_686,k1_zfmisc_1(k2_zfmisc_1(C_685,'#skF_2')))
      | ~ v1_funct_2(E_686,C_685,'#skF_2')
      | ~ v1_funct_1(E_686)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_684))
      | ~ m1_subset_1(C_685,k1_zfmisc_1(A_684))
      | v1_xboole_0(C_685)
      | v1_xboole_0(A_684) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_2719])).

tff(c_3051,plain,(
    ! [A_684] :
      ( k2_partfun1(k4_subset_1(A_684,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_684,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_684,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_684,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_684,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_684))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_684))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_684) ) ),
    inference(resolution,[status(thm)],[c_58,c_3044])).

tff(c_3061,plain,(
    ! [A_684] :
      ( k2_partfun1(k4_subset_1(A_684,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_684,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_684,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_684,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_684,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_684))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_684))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_684) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1529,c_3051])).

tff(c_3063,plain,(
    ! [A_687] :
      ( k2_partfun1(k4_subset_1(A_687,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_687,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_687,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_687,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_687,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_687))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_687))
      | v1_xboole_0(A_687) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3061])).

tff(c_131,plain,(
    ! [C_238,A_239,B_240] :
      ( v1_relat_1(C_238)
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(A_239,B_240))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_139,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_131])).

tff(c_179,plain,(
    ! [A_249,B_250] :
      ( k7_relat_1(A_249,B_250) = k1_xboole_0
      | ~ r1_xboole_0(B_250,k1_relat_1(A_249))
      | ~ v1_relat_1(A_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_195,plain,(
    ! [A_251] :
      ( k7_relat_1(A_251,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_251) ) ),
    inference(resolution,[status(thm)],[c_87,c_179])).

tff(c_202,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_139,c_195])).

tff(c_610,plain,(
    ! [A_302,B_303,C_304,D_305] :
      ( k2_partfun1(A_302,B_303,C_304,D_305) = k7_relat_1(C_304,D_305)
      | ~ m1_subset_1(C_304,k1_zfmisc_1(k2_zfmisc_1(A_302,B_303)))
      | ~ v1_funct_1(C_304) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_614,plain,(
    ! [D_305] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_305) = k7_relat_1('#skF_5',D_305)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_58,c_610])).

tff(c_620,plain,(
    ! [D_305] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_305) = k7_relat_1('#skF_5',D_305) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_614])).

tff(c_138,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_131])).

tff(c_203,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_138,c_195])).

tff(c_612,plain,(
    ! [D_305] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_305) = k7_relat_1('#skF_6',D_305)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_52,c_610])).

tff(c_617,plain,(
    ! [D_305] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_305) = k7_relat_1('#skF_6',D_305) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_612])).

tff(c_224,plain,(
    ! [A_254,B_255] :
      ( r1_xboole_0(A_254,B_255)
      | ~ r1_subset_1(A_254,B_255)
      | v1_xboole_0(B_255)
      | v1_xboole_0(A_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_590,plain,(
    ! [A_300,B_301] :
      ( k3_xboole_0(A_300,B_301) = k1_xboole_0
      | ~ r1_subset_1(A_300,B_301)
      | v1_xboole_0(B_301)
      | v1_xboole_0(A_300) ) ),
    inference(resolution,[status(thm)],[c_224,c_2])).

tff(c_599,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_590])).

tff(c_605,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_68,c_599])).

tff(c_509,plain,(
    ! [A_289,B_290,C_291] :
      ( k9_subset_1(A_289,B_290,C_291) = k3_xboole_0(B_290,C_291)
      | ~ m1_subset_1(C_291,k1_zfmisc_1(A_289)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_520,plain,(
    ! [B_290] : k9_subset_1('#skF_1',B_290,'#skF_4') = k3_xboole_0(B_290,'#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_509])).

tff(c_50,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_114,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_534,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_520,c_520,c_114])).

tff(c_656,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_620,c_203,c_617,c_605,c_605,c_534])).

tff(c_657,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_752,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_657])).

tff(c_3074,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3063,c_752])).

tff(c_3088,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_750,c_751,c_1667,c_813,c_1667,c_813,c_1797,c_3074])).

tff(c_3090,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_3088])).

tff(c_3091,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_657])).

tff(c_5753,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5744,c_3091])).

tff(c_5764,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_750,c_751,c_4203,c_3954,c_4203,c_3954,c_4362,c_5753])).

tff(c_5766,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_5764])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:50:11 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.97/2.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.97/2.73  
% 7.97/2.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.97/2.73  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.97/2.73  
% 7.97/2.73  %Foreground sorts:
% 7.97/2.73  
% 7.97/2.73  
% 7.97/2.73  %Background operators:
% 7.97/2.73  
% 7.97/2.73  
% 7.97/2.73  %Foreground operators:
% 7.97/2.73  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 7.97/2.73  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.97/2.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.97/2.73  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.97/2.73  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.97/2.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.97/2.73  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.97/2.73  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 7.97/2.73  tff('#skF_5', type, '#skF_5': $i).
% 7.97/2.73  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.97/2.73  tff('#skF_6', type, '#skF_6': $i).
% 7.97/2.73  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.97/2.73  tff('#skF_2', type, '#skF_2': $i).
% 7.97/2.73  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.97/2.73  tff('#skF_3', type, '#skF_3': $i).
% 7.97/2.73  tff('#skF_1', type, '#skF_1': $i).
% 7.97/2.73  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.97/2.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.97/2.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.97/2.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.97/2.73  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.97/2.73  tff('#skF_4', type, '#skF_4': $i).
% 7.97/2.73  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.97/2.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.97/2.73  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 7.97/2.73  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.97/2.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.97/2.73  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.97/2.73  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.97/2.73  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.97/2.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.97/2.73  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.97/2.73  
% 7.97/2.75  tff(f_225, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 7.97/2.75  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.97/2.75  tff(f_31, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 7.97/2.75  tff(f_33, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 7.97/2.75  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 7.97/2.75  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 7.97/2.75  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 7.97/2.75  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 7.97/2.75  tff(f_183, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 7.97/2.75  tff(f_101, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 7.97/2.75  tff(f_149, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 7.97/2.75  tff(c_76, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.97/2.75  tff(c_70, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.97/2.75  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.97/2.75  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.97/2.75  tff(c_675, plain, (![C_314, A_315, B_316]: (v1_relat_1(C_314) | ~m1_subset_1(C_314, k1_zfmisc_1(k2_zfmisc_1(A_315, B_316))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.97/2.75  tff(c_683, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_675])).
% 7.97/2.75  tff(c_6, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.97/2.75  tff(c_84, plain, (![A_226, B_227]: (r1_xboole_0(k4_xboole_0(A_226, B_227), B_227))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.97/2.75  tff(c_87, plain, (![A_3]: (r1_xboole_0(k1_xboole_0, A_3))), inference(superposition, [status(thm), theory('equality')], [c_6, c_84])).
% 7.97/2.75  tff(c_727, plain, (![A_325, B_326]: (k7_relat_1(A_325, B_326)=k1_xboole_0 | ~r1_xboole_0(B_326, k1_relat_1(A_325)) | ~v1_relat_1(A_325))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.97/2.75  tff(c_743, plain, (![A_327]: (k7_relat_1(A_327, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_327))), inference(resolution, [status(thm)], [c_87, c_727])).
% 7.97/2.75  tff(c_750, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_683, c_743])).
% 7.97/2.75  tff(c_52, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.97/2.75  tff(c_682, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_675])).
% 7.97/2.75  tff(c_751, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_682, c_743])).
% 7.97/2.75  tff(c_72, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.97/2.75  tff(c_68, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.97/2.75  tff(c_64, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.97/2.75  tff(c_3128, plain, (![A_693, B_694]: (r1_xboole_0(A_693, B_694) | ~r1_subset_1(A_693, B_694) | v1_xboole_0(B_694) | v1_xboole_0(A_693))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.97/2.75  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.97/2.75  tff(c_4193, plain, (![A_800, B_801]: (k3_xboole_0(A_800, B_801)=k1_xboole_0 | ~r1_subset_1(A_800, B_801) | v1_xboole_0(B_801) | v1_xboole_0(A_800))), inference(resolution, [status(thm)], [c_3128, c_2])).
% 7.97/2.75  tff(c_4199, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_64, c_4193])).
% 7.97/2.75  tff(c_4203, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_72, c_68, c_4199])).
% 7.97/2.75  tff(c_3943, plain, (![A_783, B_784, C_785]: (k9_subset_1(A_783, B_784, C_785)=k3_xboole_0(B_784, C_785) | ~m1_subset_1(C_785, k1_zfmisc_1(A_783)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.97/2.75  tff(c_3954, plain, (![B_784]: (k9_subset_1('#skF_1', B_784, '#skF_4')=k3_xboole_0(B_784, '#skF_4'))), inference(resolution, [status(thm)], [c_66, c_3943])).
% 7.97/2.75  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.97/2.75  tff(c_60, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.97/2.75  tff(c_74, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.97/2.75  tff(c_56, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.97/2.75  tff(c_54, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.97/2.75  tff(c_4321, plain, (![D_819, A_820, C_822, F_818, B_817, E_821]: (v1_funct_1(k1_tmap_1(A_820, B_817, C_822, D_819, E_821, F_818)) | ~m1_subset_1(F_818, k1_zfmisc_1(k2_zfmisc_1(D_819, B_817))) | ~v1_funct_2(F_818, D_819, B_817) | ~v1_funct_1(F_818) | ~m1_subset_1(E_821, k1_zfmisc_1(k2_zfmisc_1(C_822, B_817))) | ~v1_funct_2(E_821, C_822, B_817) | ~v1_funct_1(E_821) | ~m1_subset_1(D_819, k1_zfmisc_1(A_820)) | v1_xboole_0(D_819) | ~m1_subset_1(C_822, k1_zfmisc_1(A_820)) | v1_xboole_0(C_822) | v1_xboole_0(B_817) | v1_xboole_0(A_820))), inference(cnfTransformation, [status(thm)], [f_183])).
% 7.97/2.75  tff(c_4323, plain, (![A_820, C_822, E_821]: (v1_funct_1(k1_tmap_1(A_820, '#skF_2', C_822, '#skF_4', E_821, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_821, k1_zfmisc_1(k2_zfmisc_1(C_822, '#skF_2'))) | ~v1_funct_2(E_821, C_822, '#skF_2') | ~v1_funct_1(E_821) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_820)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_822, k1_zfmisc_1(A_820)) | v1_xboole_0(C_822) | v1_xboole_0('#skF_2') | v1_xboole_0(A_820))), inference(resolution, [status(thm)], [c_52, c_4321])).
% 7.97/2.75  tff(c_4328, plain, (![A_820, C_822, E_821]: (v1_funct_1(k1_tmap_1(A_820, '#skF_2', C_822, '#skF_4', E_821, '#skF_6')) | ~m1_subset_1(E_821, k1_zfmisc_1(k2_zfmisc_1(C_822, '#skF_2'))) | ~v1_funct_2(E_821, C_822, '#skF_2') | ~v1_funct_1(E_821) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_820)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_822, k1_zfmisc_1(A_820)) | v1_xboole_0(C_822) | v1_xboole_0('#skF_2') | v1_xboole_0(A_820))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_4323])).
% 7.97/2.75  tff(c_4334, plain, (![A_823, C_824, E_825]: (v1_funct_1(k1_tmap_1(A_823, '#skF_2', C_824, '#skF_4', E_825, '#skF_6')) | ~m1_subset_1(E_825, k1_zfmisc_1(k2_zfmisc_1(C_824, '#skF_2'))) | ~v1_funct_2(E_825, C_824, '#skF_2') | ~v1_funct_1(E_825) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_823)) | ~m1_subset_1(C_824, k1_zfmisc_1(A_823)) | v1_xboole_0(C_824) | v1_xboole_0(A_823))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_4328])).
% 7.97/2.75  tff(c_4338, plain, (![A_823]: (v1_funct_1(k1_tmap_1(A_823, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_823)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_823)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_823))), inference(resolution, [status(thm)], [c_58, c_4334])).
% 7.97/2.75  tff(c_4345, plain, (![A_823]: (v1_funct_1(k1_tmap_1(A_823, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_823)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_823)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_823))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_4338])).
% 7.97/2.75  tff(c_4355, plain, (![A_833]: (v1_funct_1(k1_tmap_1(A_833, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_833)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_833)) | v1_xboole_0(A_833))), inference(negUnitSimplification, [status(thm)], [c_72, c_4345])).
% 7.97/2.75  tff(c_4358, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_70, c_4355])).
% 7.97/2.75  tff(c_4361, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_4358])).
% 7.97/2.75  tff(c_4362, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_76, c_4361])).
% 7.97/2.75  tff(c_4208, plain, (![A_802, B_803, C_804, D_805]: (k2_partfun1(A_802, B_803, C_804, D_805)=k7_relat_1(C_804, D_805) | ~m1_subset_1(C_804, k1_zfmisc_1(k2_zfmisc_1(A_802, B_803))) | ~v1_funct_1(C_804))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.97/2.75  tff(c_4212, plain, (![D_805]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_805)=k7_relat_1('#skF_5', D_805) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_58, c_4208])).
% 7.97/2.75  tff(c_4218, plain, (![D_805]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_805)=k7_relat_1('#skF_5', D_805))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_4212])).
% 7.97/2.75  tff(c_4210, plain, (![D_805]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_805)=k7_relat_1('#skF_6', D_805) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_52, c_4208])).
% 7.97/2.75  tff(c_4215, plain, (![D_805]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_805)=k7_relat_1('#skF_6', D_805))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_4210])).
% 7.97/2.75  tff(c_46, plain, (![E_166, F_167, B_163, D_165, A_162, C_164]: (v1_funct_2(k1_tmap_1(A_162, B_163, C_164, D_165, E_166, F_167), k4_subset_1(A_162, C_164, D_165), B_163) | ~m1_subset_1(F_167, k1_zfmisc_1(k2_zfmisc_1(D_165, B_163))) | ~v1_funct_2(F_167, D_165, B_163) | ~v1_funct_1(F_167) | ~m1_subset_1(E_166, k1_zfmisc_1(k2_zfmisc_1(C_164, B_163))) | ~v1_funct_2(E_166, C_164, B_163) | ~v1_funct_1(E_166) | ~m1_subset_1(D_165, k1_zfmisc_1(A_162)) | v1_xboole_0(D_165) | ~m1_subset_1(C_164, k1_zfmisc_1(A_162)) | v1_xboole_0(C_164) | v1_xboole_0(B_163) | v1_xboole_0(A_162))), inference(cnfTransformation, [status(thm)], [f_183])).
% 7.97/2.75  tff(c_44, plain, (![E_166, F_167, B_163, D_165, A_162, C_164]: (m1_subset_1(k1_tmap_1(A_162, B_163, C_164, D_165, E_166, F_167), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_162, C_164, D_165), B_163))) | ~m1_subset_1(F_167, k1_zfmisc_1(k2_zfmisc_1(D_165, B_163))) | ~v1_funct_2(F_167, D_165, B_163) | ~v1_funct_1(F_167) | ~m1_subset_1(E_166, k1_zfmisc_1(k2_zfmisc_1(C_164, B_163))) | ~v1_funct_2(E_166, C_164, B_163) | ~v1_funct_1(E_166) | ~m1_subset_1(D_165, k1_zfmisc_1(A_162)) | v1_xboole_0(D_165) | ~m1_subset_1(C_164, k1_zfmisc_1(A_162)) | v1_xboole_0(C_164) | v1_xboole_0(B_163) | v1_xboole_0(A_162))), inference(cnfTransformation, [status(thm)], [f_183])).
% 7.97/2.75  tff(c_4518, plain, (![B_862, F_859, A_860, C_864, D_863, E_861]: (k2_partfun1(k4_subset_1(A_860, C_864, D_863), B_862, k1_tmap_1(A_860, B_862, C_864, D_863, E_861, F_859), C_864)=E_861 | ~m1_subset_1(k1_tmap_1(A_860, B_862, C_864, D_863, E_861, F_859), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_860, C_864, D_863), B_862))) | ~v1_funct_2(k1_tmap_1(A_860, B_862, C_864, D_863, E_861, F_859), k4_subset_1(A_860, C_864, D_863), B_862) | ~v1_funct_1(k1_tmap_1(A_860, B_862, C_864, D_863, E_861, F_859)) | k2_partfun1(D_863, B_862, F_859, k9_subset_1(A_860, C_864, D_863))!=k2_partfun1(C_864, B_862, E_861, k9_subset_1(A_860, C_864, D_863)) | ~m1_subset_1(F_859, k1_zfmisc_1(k2_zfmisc_1(D_863, B_862))) | ~v1_funct_2(F_859, D_863, B_862) | ~v1_funct_1(F_859) | ~m1_subset_1(E_861, k1_zfmisc_1(k2_zfmisc_1(C_864, B_862))) | ~v1_funct_2(E_861, C_864, B_862) | ~v1_funct_1(E_861) | ~m1_subset_1(D_863, k1_zfmisc_1(A_860)) | v1_xboole_0(D_863) | ~m1_subset_1(C_864, k1_zfmisc_1(A_860)) | v1_xboole_0(C_864) | v1_xboole_0(B_862) | v1_xboole_0(A_860))), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.97/2.75  tff(c_4954, plain, (![D_965, B_963, E_967, C_968, A_966, F_964]: (k2_partfun1(k4_subset_1(A_966, C_968, D_965), B_963, k1_tmap_1(A_966, B_963, C_968, D_965, E_967, F_964), C_968)=E_967 | ~v1_funct_2(k1_tmap_1(A_966, B_963, C_968, D_965, E_967, F_964), k4_subset_1(A_966, C_968, D_965), B_963) | ~v1_funct_1(k1_tmap_1(A_966, B_963, C_968, D_965, E_967, F_964)) | k2_partfun1(D_965, B_963, F_964, k9_subset_1(A_966, C_968, D_965))!=k2_partfun1(C_968, B_963, E_967, k9_subset_1(A_966, C_968, D_965)) | ~m1_subset_1(F_964, k1_zfmisc_1(k2_zfmisc_1(D_965, B_963))) | ~v1_funct_2(F_964, D_965, B_963) | ~v1_funct_1(F_964) | ~m1_subset_1(E_967, k1_zfmisc_1(k2_zfmisc_1(C_968, B_963))) | ~v1_funct_2(E_967, C_968, B_963) | ~v1_funct_1(E_967) | ~m1_subset_1(D_965, k1_zfmisc_1(A_966)) | v1_xboole_0(D_965) | ~m1_subset_1(C_968, k1_zfmisc_1(A_966)) | v1_xboole_0(C_968) | v1_xboole_0(B_963) | v1_xboole_0(A_966))), inference(resolution, [status(thm)], [c_44, c_4518])).
% 7.97/2.75  tff(c_5332, plain, (![E_1024, B_1020, F_1021, D_1022, C_1025, A_1023]: (k2_partfun1(k4_subset_1(A_1023, C_1025, D_1022), B_1020, k1_tmap_1(A_1023, B_1020, C_1025, D_1022, E_1024, F_1021), C_1025)=E_1024 | ~v1_funct_1(k1_tmap_1(A_1023, B_1020, C_1025, D_1022, E_1024, F_1021)) | k2_partfun1(D_1022, B_1020, F_1021, k9_subset_1(A_1023, C_1025, D_1022))!=k2_partfun1(C_1025, B_1020, E_1024, k9_subset_1(A_1023, C_1025, D_1022)) | ~m1_subset_1(F_1021, k1_zfmisc_1(k2_zfmisc_1(D_1022, B_1020))) | ~v1_funct_2(F_1021, D_1022, B_1020) | ~v1_funct_1(F_1021) | ~m1_subset_1(E_1024, k1_zfmisc_1(k2_zfmisc_1(C_1025, B_1020))) | ~v1_funct_2(E_1024, C_1025, B_1020) | ~v1_funct_1(E_1024) | ~m1_subset_1(D_1022, k1_zfmisc_1(A_1023)) | v1_xboole_0(D_1022) | ~m1_subset_1(C_1025, k1_zfmisc_1(A_1023)) | v1_xboole_0(C_1025) | v1_xboole_0(B_1020) | v1_xboole_0(A_1023))), inference(resolution, [status(thm)], [c_46, c_4954])).
% 7.97/2.75  tff(c_5336, plain, (![A_1023, C_1025, E_1024]: (k2_partfun1(k4_subset_1(A_1023, C_1025, '#skF_4'), '#skF_2', k1_tmap_1(A_1023, '#skF_2', C_1025, '#skF_4', E_1024, '#skF_6'), C_1025)=E_1024 | ~v1_funct_1(k1_tmap_1(A_1023, '#skF_2', C_1025, '#skF_4', E_1024, '#skF_6')) | k2_partfun1(C_1025, '#skF_2', E_1024, k9_subset_1(A_1023, C_1025, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_1023, C_1025, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1024, k1_zfmisc_1(k2_zfmisc_1(C_1025, '#skF_2'))) | ~v1_funct_2(E_1024, C_1025, '#skF_2') | ~v1_funct_1(E_1024) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1023)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1025, k1_zfmisc_1(A_1023)) | v1_xboole_0(C_1025) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1023))), inference(resolution, [status(thm)], [c_52, c_5332])).
% 7.97/2.75  tff(c_5342, plain, (![A_1023, C_1025, E_1024]: (k2_partfun1(k4_subset_1(A_1023, C_1025, '#skF_4'), '#skF_2', k1_tmap_1(A_1023, '#skF_2', C_1025, '#skF_4', E_1024, '#skF_6'), C_1025)=E_1024 | ~v1_funct_1(k1_tmap_1(A_1023, '#skF_2', C_1025, '#skF_4', E_1024, '#skF_6')) | k2_partfun1(C_1025, '#skF_2', E_1024, k9_subset_1(A_1023, C_1025, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1023, C_1025, '#skF_4')) | ~m1_subset_1(E_1024, k1_zfmisc_1(k2_zfmisc_1(C_1025, '#skF_2'))) | ~v1_funct_2(E_1024, C_1025, '#skF_2') | ~v1_funct_1(E_1024) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1023)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1025, k1_zfmisc_1(A_1023)) | v1_xboole_0(C_1025) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1023))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_4215, c_5336])).
% 7.97/2.75  tff(c_5714, plain, (![A_1072, C_1073, E_1074]: (k2_partfun1(k4_subset_1(A_1072, C_1073, '#skF_4'), '#skF_2', k1_tmap_1(A_1072, '#skF_2', C_1073, '#skF_4', E_1074, '#skF_6'), C_1073)=E_1074 | ~v1_funct_1(k1_tmap_1(A_1072, '#skF_2', C_1073, '#skF_4', E_1074, '#skF_6')) | k2_partfun1(C_1073, '#skF_2', E_1074, k9_subset_1(A_1072, C_1073, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1072, C_1073, '#skF_4')) | ~m1_subset_1(E_1074, k1_zfmisc_1(k2_zfmisc_1(C_1073, '#skF_2'))) | ~v1_funct_2(E_1074, C_1073, '#skF_2') | ~v1_funct_1(E_1074) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1072)) | ~m1_subset_1(C_1073, k1_zfmisc_1(A_1072)) | v1_xboole_0(C_1073) | v1_xboole_0(A_1072))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_5342])).
% 7.97/2.75  tff(c_5721, plain, (![A_1072]: (k2_partfun1(k4_subset_1(A_1072, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1072, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1072, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_1072, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1072, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1072)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1072)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1072))), inference(resolution, [status(thm)], [c_58, c_5714])).
% 7.97/2.75  tff(c_5731, plain, (![A_1072]: (k2_partfun1(k4_subset_1(A_1072, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1072, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1072, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1072, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1072, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1072)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1072)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1072))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_4218, c_5721])).
% 7.97/2.75  tff(c_5744, plain, (![A_1081]: (k2_partfun1(k4_subset_1(A_1081, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1081, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1081, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1081, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1081, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1081)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1081)) | v1_xboole_0(A_1081))), inference(negUnitSimplification, [status(thm)], [c_72, c_5731])).
% 7.97/2.75  tff(c_774, plain, (![A_331, B_332]: (r1_xboole_0(A_331, B_332) | ~r1_subset_1(A_331, B_332) | v1_xboole_0(B_332) | v1_xboole_0(A_331))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.97/2.75  tff(c_1656, plain, (![A_417, B_418]: (k3_xboole_0(A_417, B_418)=k1_xboole_0 | ~r1_subset_1(A_417, B_418) | v1_xboole_0(B_418) | v1_xboole_0(A_417))), inference(resolution, [status(thm)], [c_774, c_2])).
% 7.97/2.75  tff(c_1662, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_64, c_1656])).
% 7.97/2.75  tff(c_1667, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_72, c_68, c_1662])).
% 7.97/2.75  tff(c_802, plain, (![A_335, B_336, C_337]: (k9_subset_1(A_335, B_336, C_337)=k3_xboole_0(B_336, C_337) | ~m1_subset_1(C_337, k1_zfmisc_1(A_335)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.97/2.75  tff(c_813, plain, (![B_336]: (k9_subset_1('#skF_1', B_336, '#skF_4')=k3_xboole_0(B_336, '#skF_4'))), inference(resolution, [status(thm)], [c_66, c_802])).
% 7.97/2.75  tff(c_1705, plain, (![A_427, D_426, B_424, C_429, F_425, E_428]: (v1_funct_1(k1_tmap_1(A_427, B_424, C_429, D_426, E_428, F_425)) | ~m1_subset_1(F_425, k1_zfmisc_1(k2_zfmisc_1(D_426, B_424))) | ~v1_funct_2(F_425, D_426, B_424) | ~v1_funct_1(F_425) | ~m1_subset_1(E_428, k1_zfmisc_1(k2_zfmisc_1(C_429, B_424))) | ~v1_funct_2(E_428, C_429, B_424) | ~v1_funct_1(E_428) | ~m1_subset_1(D_426, k1_zfmisc_1(A_427)) | v1_xboole_0(D_426) | ~m1_subset_1(C_429, k1_zfmisc_1(A_427)) | v1_xboole_0(C_429) | v1_xboole_0(B_424) | v1_xboole_0(A_427))), inference(cnfTransformation, [status(thm)], [f_183])).
% 7.97/2.75  tff(c_1707, plain, (![A_427, C_429, E_428]: (v1_funct_1(k1_tmap_1(A_427, '#skF_2', C_429, '#skF_4', E_428, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_428, k1_zfmisc_1(k2_zfmisc_1(C_429, '#skF_2'))) | ~v1_funct_2(E_428, C_429, '#skF_2') | ~v1_funct_1(E_428) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_427)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_429, k1_zfmisc_1(A_427)) | v1_xboole_0(C_429) | v1_xboole_0('#skF_2') | v1_xboole_0(A_427))), inference(resolution, [status(thm)], [c_52, c_1705])).
% 7.97/2.75  tff(c_1712, plain, (![A_427, C_429, E_428]: (v1_funct_1(k1_tmap_1(A_427, '#skF_2', C_429, '#skF_4', E_428, '#skF_6')) | ~m1_subset_1(E_428, k1_zfmisc_1(k2_zfmisc_1(C_429, '#skF_2'))) | ~v1_funct_2(E_428, C_429, '#skF_2') | ~v1_funct_1(E_428) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_427)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_429, k1_zfmisc_1(A_427)) | v1_xboole_0(C_429) | v1_xboole_0('#skF_2') | v1_xboole_0(A_427))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_1707])).
% 7.97/2.75  tff(c_1770, plain, (![A_443, C_444, E_445]: (v1_funct_1(k1_tmap_1(A_443, '#skF_2', C_444, '#skF_4', E_445, '#skF_6')) | ~m1_subset_1(E_445, k1_zfmisc_1(k2_zfmisc_1(C_444, '#skF_2'))) | ~v1_funct_2(E_445, C_444, '#skF_2') | ~v1_funct_1(E_445) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_443)) | ~m1_subset_1(C_444, k1_zfmisc_1(A_443)) | v1_xboole_0(C_444) | v1_xboole_0(A_443))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_1712])).
% 7.97/2.75  tff(c_1774, plain, (![A_443]: (v1_funct_1(k1_tmap_1(A_443, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_443)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_443)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_443))), inference(resolution, [status(thm)], [c_58, c_1770])).
% 7.97/2.75  tff(c_1781, plain, (![A_443]: (v1_funct_1(k1_tmap_1(A_443, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_443)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_443)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_443))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1774])).
% 7.97/2.76  tff(c_1790, plain, (![A_447]: (v1_funct_1(k1_tmap_1(A_447, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_447)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_447)) | v1_xboole_0(A_447))), inference(negUnitSimplification, [status(thm)], [c_72, c_1781])).
% 7.97/2.76  tff(c_1793, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_70, c_1790])).
% 7.97/2.76  tff(c_1796, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1793])).
% 7.97/2.76  tff(c_1797, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_76, c_1796])).
% 7.97/2.76  tff(c_1519, plain, (![A_404, B_405, C_406, D_407]: (k2_partfun1(A_404, B_405, C_406, D_407)=k7_relat_1(C_406, D_407) | ~m1_subset_1(C_406, k1_zfmisc_1(k2_zfmisc_1(A_404, B_405))) | ~v1_funct_1(C_406))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.97/2.76  tff(c_1523, plain, (![D_407]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_407)=k7_relat_1('#skF_5', D_407) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_58, c_1519])).
% 7.97/2.76  tff(c_1529, plain, (![D_407]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_407)=k7_relat_1('#skF_5', D_407))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1523])).
% 7.97/2.76  tff(c_1521, plain, (![D_407]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_407)=k7_relat_1('#skF_6', D_407) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_52, c_1519])).
% 7.97/2.76  tff(c_1526, plain, (![D_407]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_407)=k7_relat_1('#skF_6', D_407))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1521])).
% 7.97/2.76  tff(c_1875, plain, (![F_463, E_465, D_467, C_468, B_466, A_464]: (k2_partfun1(k4_subset_1(A_464, C_468, D_467), B_466, k1_tmap_1(A_464, B_466, C_468, D_467, E_465, F_463), D_467)=F_463 | ~m1_subset_1(k1_tmap_1(A_464, B_466, C_468, D_467, E_465, F_463), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_464, C_468, D_467), B_466))) | ~v1_funct_2(k1_tmap_1(A_464, B_466, C_468, D_467, E_465, F_463), k4_subset_1(A_464, C_468, D_467), B_466) | ~v1_funct_1(k1_tmap_1(A_464, B_466, C_468, D_467, E_465, F_463)) | k2_partfun1(D_467, B_466, F_463, k9_subset_1(A_464, C_468, D_467))!=k2_partfun1(C_468, B_466, E_465, k9_subset_1(A_464, C_468, D_467)) | ~m1_subset_1(F_463, k1_zfmisc_1(k2_zfmisc_1(D_467, B_466))) | ~v1_funct_2(F_463, D_467, B_466) | ~v1_funct_1(F_463) | ~m1_subset_1(E_465, k1_zfmisc_1(k2_zfmisc_1(C_468, B_466))) | ~v1_funct_2(E_465, C_468, B_466) | ~v1_funct_1(E_465) | ~m1_subset_1(D_467, k1_zfmisc_1(A_464)) | v1_xboole_0(D_467) | ~m1_subset_1(C_468, k1_zfmisc_1(A_464)) | v1_xboole_0(C_468) | v1_xboole_0(B_466) | v1_xboole_0(A_464))), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.97/2.76  tff(c_2192, plain, (![F_582, D_583, A_584, C_586, E_585, B_581]: (k2_partfun1(k4_subset_1(A_584, C_586, D_583), B_581, k1_tmap_1(A_584, B_581, C_586, D_583, E_585, F_582), D_583)=F_582 | ~v1_funct_2(k1_tmap_1(A_584, B_581, C_586, D_583, E_585, F_582), k4_subset_1(A_584, C_586, D_583), B_581) | ~v1_funct_1(k1_tmap_1(A_584, B_581, C_586, D_583, E_585, F_582)) | k2_partfun1(D_583, B_581, F_582, k9_subset_1(A_584, C_586, D_583))!=k2_partfun1(C_586, B_581, E_585, k9_subset_1(A_584, C_586, D_583)) | ~m1_subset_1(F_582, k1_zfmisc_1(k2_zfmisc_1(D_583, B_581))) | ~v1_funct_2(F_582, D_583, B_581) | ~v1_funct_1(F_582) | ~m1_subset_1(E_585, k1_zfmisc_1(k2_zfmisc_1(C_586, B_581))) | ~v1_funct_2(E_585, C_586, B_581) | ~v1_funct_1(E_585) | ~m1_subset_1(D_583, k1_zfmisc_1(A_584)) | v1_xboole_0(D_583) | ~m1_subset_1(C_586, k1_zfmisc_1(A_584)) | v1_xboole_0(C_586) | v1_xboole_0(B_581) | v1_xboole_0(A_584))), inference(resolution, [status(thm)], [c_44, c_1875])).
% 7.97/2.76  tff(c_2709, plain, (![F_636, D_637, C_640, A_638, E_639, B_635]: (k2_partfun1(k4_subset_1(A_638, C_640, D_637), B_635, k1_tmap_1(A_638, B_635, C_640, D_637, E_639, F_636), D_637)=F_636 | ~v1_funct_1(k1_tmap_1(A_638, B_635, C_640, D_637, E_639, F_636)) | k2_partfun1(D_637, B_635, F_636, k9_subset_1(A_638, C_640, D_637))!=k2_partfun1(C_640, B_635, E_639, k9_subset_1(A_638, C_640, D_637)) | ~m1_subset_1(F_636, k1_zfmisc_1(k2_zfmisc_1(D_637, B_635))) | ~v1_funct_2(F_636, D_637, B_635) | ~v1_funct_1(F_636) | ~m1_subset_1(E_639, k1_zfmisc_1(k2_zfmisc_1(C_640, B_635))) | ~v1_funct_2(E_639, C_640, B_635) | ~v1_funct_1(E_639) | ~m1_subset_1(D_637, k1_zfmisc_1(A_638)) | v1_xboole_0(D_637) | ~m1_subset_1(C_640, k1_zfmisc_1(A_638)) | v1_xboole_0(C_640) | v1_xboole_0(B_635) | v1_xboole_0(A_638))), inference(resolution, [status(thm)], [c_46, c_2192])).
% 7.97/2.76  tff(c_2713, plain, (![A_638, C_640, E_639]: (k2_partfun1(k4_subset_1(A_638, C_640, '#skF_4'), '#skF_2', k1_tmap_1(A_638, '#skF_2', C_640, '#skF_4', E_639, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_638, '#skF_2', C_640, '#skF_4', E_639, '#skF_6')) | k2_partfun1(C_640, '#skF_2', E_639, k9_subset_1(A_638, C_640, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_638, C_640, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_639, k1_zfmisc_1(k2_zfmisc_1(C_640, '#skF_2'))) | ~v1_funct_2(E_639, C_640, '#skF_2') | ~v1_funct_1(E_639) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_638)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_640, k1_zfmisc_1(A_638)) | v1_xboole_0(C_640) | v1_xboole_0('#skF_2') | v1_xboole_0(A_638))), inference(resolution, [status(thm)], [c_52, c_2709])).
% 7.97/2.76  tff(c_2719, plain, (![A_638, C_640, E_639]: (k2_partfun1(k4_subset_1(A_638, C_640, '#skF_4'), '#skF_2', k1_tmap_1(A_638, '#skF_2', C_640, '#skF_4', E_639, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_638, '#skF_2', C_640, '#skF_4', E_639, '#skF_6')) | k2_partfun1(C_640, '#skF_2', E_639, k9_subset_1(A_638, C_640, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_638, C_640, '#skF_4')) | ~m1_subset_1(E_639, k1_zfmisc_1(k2_zfmisc_1(C_640, '#skF_2'))) | ~v1_funct_2(E_639, C_640, '#skF_2') | ~v1_funct_1(E_639) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_638)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_640, k1_zfmisc_1(A_638)) | v1_xboole_0(C_640) | v1_xboole_0('#skF_2') | v1_xboole_0(A_638))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_1526, c_2713])).
% 7.97/2.76  tff(c_3044, plain, (![A_684, C_685, E_686]: (k2_partfun1(k4_subset_1(A_684, C_685, '#skF_4'), '#skF_2', k1_tmap_1(A_684, '#skF_2', C_685, '#skF_4', E_686, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_684, '#skF_2', C_685, '#skF_4', E_686, '#skF_6')) | k2_partfun1(C_685, '#skF_2', E_686, k9_subset_1(A_684, C_685, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_684, C_685, '#skF_4')) | ~m1_subset_1(E_686, k1_zfmisc_1(k2_zfmisc_1(C_685, '#skF_2'))) | ~v1_funct_2(E_686, C_685, '#skF_2') | ~v1_funct_1(E_686) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_684)) | ~m1_subset_1(C_685, k1_zfmisc_1(A_684)) | v1_xboole_0(C_685) | v1_xboole_0(A_684))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_2719])).
% 7.97/2.76  tff(c_3051, plain, (![A_684]: (k2_partfun1(k4_subset_1(A_684, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_684, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_684, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_684, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_684, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_684)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_684)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_684))), inference(resolution, [status(thm)], [c_58, c_3044])).
% 7.97/2.76  tff(c_3061, plain, (![A_684]: (k2_partfun1(k4_subset_1(A_684, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_684, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_684, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_684, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_684, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_684)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_684)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_684))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1529, c_3051])).
% 7.97/2.76  tff(c_3063, plain, (![A_687]: (k2_partfun1(k4_subset_1(A_687, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_687, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_687, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_687, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_687, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_687)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_687)) | v1_xboole_0(A_687))), inference(negUnitSimplification, [status(thm)], [c_72, c_3061])).
% 7.97/2.76  tff(c_131, plain, (![C_238, A_239, B_240]: (v1_relat_1(C_238) | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(A_239, B_240))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.97/2.76  tff(c_139, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_131])).
% 7.97/2.76  tff(c_179, plain, (![A_249, B_250]: (k7_relat_1(A_249, B_250)=k1_xboole_0 | ~r1_xboole_0(B_250, k1_relat_1(A_249)) | ~v1_relat_1(A_249))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.97/2.76  tff(c_195, plain, (![A_251]: (k7_relat_1(A_251, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_251))), inference(resolution, [status(thm)], [c_87, c_179])).
% 7.97/2.76  tff(c_202, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_139, c_195])).
% 7.97/2.76  tff(c_610, plain, (![A_302, B_303, C_304, D_305]: (k2_partfun1(A_302, B_303, C_304, D_305)=k7_relat_1(C_304, D_305) | ~m1_subset_1(C_304, k1_zfmisc_1(k2_zfmisc_1(A_302, B_303))) | ~v1_funct_1(C_304))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.97/2.76  tff(c_614, plain, (![D_305]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_305)=k7_relat_1('#skF_5', D_305) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_58, c_610])).
% 7.97/2.76  tff(c_620, plain, (![D_305]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_305)=k7_relat_1('#skF_5', D_305))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_614])).
% 7.97/2.76  tff(c_138, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_131])).
% 7.97/2.76  tff(c_203, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_138, c_195])).
% 7.97/2.76  tff(c_612, plain, (![D_305]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_305)=k7_relat_1('#skF_6', D_305) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_52, c_610])).
% 7.97/2.76  tff(c_617, plain, (![D_305]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_305)=k7_relat_1('#skF_6', D_305))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_612])).
% 7.97/2.76  tff(c_224, plain, (![A_254, B_255]: (r1_xboole_0(A_254, B_255) | ~r1_subset_1(A_254, B_255) | v1_xboole_0(B_255) | v1_xboole_0(A_254))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.97/2.76  tff(c_590, plain, (![A_300, B_301]: (k3_xboole_0(A_300, B_301)=k1_xboole_0 | ~r1_subset_1(A_300, B_301) | v1_xboole_0(B_301) | v1_xboole_0(A_300))), inference(resolution, [status(thm)], [c_224, c_2])).
% 7.97/2.76  tff(c_599, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_64, c_590])).
% 7.97/2.76  tff(c_605, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_72, c_68, c_599])).
% 7.97/2.76  tff(c_509, plain, (![A_289, B_290, C_291]: (k9_subset_1(A_289, B_290, C_291)=k3_xboole_0(B_290, C_291) | ~m1_subset_1(C_291, k1_zfmisc_1(A_289)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.97/2.76  tff(c_520, plain, (![B_290]: (k9_subset_1('#skF_1', B_290, '#skF_4')=k3_xboole_0(B_290, '#skF_4'))), inference(resolution, [status(thm)], [c_66, c_509])).
% 7.97/2.76  tff(c_50, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.97/2.76  tff(c_114, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_50])).
% 7.97/2.76  tff(c_534, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_520, c_520, c_114])).
% 7.97/2.76  tff(c_656, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_202, c_620, c_203, c_617, c_605, c_605, c_534])).
% 7.97/2.76  tff(c_657, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_50])).
% 7.97/2.76  tff(c_752, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_657])).
% 7.97/2.76  tff(c_3074, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3063, c_752])).
% 7.97/2.76  tff(c_3088, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_750, c_751, c_1667, c_813, c_1667, c_813, c_1797, c_3074])).
% 7.97/2.76  tff(c_3090, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_3088])).
% 7.97/2.76  tff(c_3091, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_657])).
% 7.97/2.76  tff(c_5753, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5744, c_3091])).
% 7.97/2.76  tff(c_5764, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_750, c_751, c_4203, c_3954, c_4203, c_3954, c_4362, c_5753])).
% 7.97/2.76  tff(c_5766, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_5764])).
% 7.97/2.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.97/2.76  
% 7.97/2.76  Inference rules
% 7.97/2.76  ----------------------
% 7.97/2.76  #Ref     : 0
% 7.97/2.76  #Sup     : 1144
% 7.97/2.76  #Fact    : 0
% 7.97/2.76  #Define  : 0
% 7.97/2.76  #Split   : 46
% 7.97/2.76  #Chain   : 0
% 7.97/2.76  #Close   : 0
% 7.97/2.76  
% 7.97/2.76  Ordering : KBO
% 7.97/2.76  
% 7.97/2.76  Simplification rules
% 7.97/2.76  ----------------------
% 7.97/2.76  #Subsume      : 98
% 7.97/2.76  #Demod        : 997
% 7.97/2.76  #Tautology    : 613
% 7.97/2.76  #SimpNegUnit  : 240
% 7.97/2.76  #BackRed      : 14
% 7.97/2.76  
% 7.97/2.76  #Partial instantiations: 0
% 7.97/2.76  #Strategies tried      : 1
% 7.97/2.76  
% 7.97/2.76  Timing (in seconds)
% 7.97/2.76  ----------------------
% 7.97/2.76  Preprocessing        : 0.42
% 7.97/2.76  Parsing              : 0.21
% 7.97/2.76  CNF conversion       : 0.06
% 7.97/2.76  Main loop            : 1.57
% 7.97/2.76  Inferencing          : 0.56
% 7.97/2.76  Reduction            : 0.52
% 7.97/2.76  Demodulation         : 0.39
% 7.97/2.76  BG Simplification    : 0.06
% 7.97/2.76  Subsumption          : 0.33
% 7.97/2.76  Abstraction          : 0.08
% 7.97/2.76  MUC search           : 0.00
% 7.97/2.76  Cooper               : 0.00
% 7.97/2.76  Total                : 2.04
% 7.97/2.76  Index Insertion      : 0.00
% 7.97/2.76  Index Deletion       : 0.00
% 7.97/2.76  Index Matching       : 0.00
% 7.97/2.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
