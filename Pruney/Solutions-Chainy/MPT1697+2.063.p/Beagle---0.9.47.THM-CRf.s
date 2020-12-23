%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:19 EST 2020

% Result     : Theorem 7.87s
% Output     : CNFRefutation 8.12s
% Verified   : 
% Statistics : Number of formulae       :  209 ( 545 expanded)
%              Number of leaves         :   46 ( 217 expanded)
%              Depth                    :   12
%              Number of atoms          :  675 (2870 expanded)
%              Number of equality atoms :  132 ( 510 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r1_subset_1,type,(
    r1_subset_1: ( $i * $i ) > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_222,negated_conjecture,(
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

tff(f_36,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_180,axiom,(
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

tff(f_98,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_146,axiom,(
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

tff(c_76,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_70,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_66,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_10,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1032,plain,(
    ! [A_388,B_389] :
      ( r2_hidden('#skF_2'(A_388,B_389),B_389)
      | r1_xboole_0(A_388,B_389) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1036,plain,(
    ! [B_389,A_388] :
      ( ~ v1_xboole_0(B_389)
      | r1_xboole_0(A_388,B_389) ) ),
    inference(resolution,[status(thm)],[c_1032,c_2])).

tff(c_52,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_1053,plain,(
    ! [C_395,A_396,B_397] :
      ( v1_relat_1(C_395)
      | ~ m1_subset_1(C_395,k1_zfmisc_1(k2_zfmisc_1(A_396,B_397))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1060,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_52,c_1053])).

tff(c_3617,plain,(
    ! [C_800,A_801,B_802] :
      ( v4_relat_1(C_800,A_801)
      | ~ m1_subset_1(C_800,k1_zfmisc_1(k2_zfmisc_1(A_801,B_802))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_3624,plain,(
    v4_relat_1('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_3617])).

tff(c_3636,plain,(
    ! [B_806,A_807] :
      ( k7_relat_1(B_806,A_807) = B_806
      | ~ v4_relat_1(B_806,A_807)
      | ~ v1_relat_1(B_806) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3642,plain,
    ( k7_relat_1('#skF_8','#skF_6') = '#skF_8'
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_3624,c_3636])).

tff(c_3648,plain,(
    k7_relat_1('#skF_8','#skF_6') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1060,c_3642])).

tff(c_3691,plain,(
    ! [C_815,A_816,B_817] :
      ( k7_relat_1(k7_relat_1(C_815,A_816),B_817) = k1_xboole_0
      | ~ r1_xboole_0(A_816,B_817)
      | ~ v1_relat_1(C_815) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3706,plain,(
    ! [B_817] :
      ( k7_relat_1('#skF_8',B_817) = k1_xboole_0
      | ~ r1_xboole_0('#skF_6',B_817)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3648,c_3691])).

tff(c_3716,plain,(
    ! [B_818] :
      ( k7_relat_1('#skF_8',B_818) = k1_xboole_0
      | ~ r1_xboole_0('#skF_6',B_818) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1060,c_3706])).

tff(c_3739,plain,(
    ! [B_819] :
      ( k7_relat_1('#skF_8',B_819) = k1_xboole_0
      | ~ v1_xboole_0(B_819) ) ),
    inference(resolution,[status(thm)],[c_1036,c_3716])).

tff(c_3743,plain,(
    k7_relat_1('#skF_8',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_3739])).

tff(c_72,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_64,plain,(
    r1_subset_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_3666,plain,(
    ! [A_811,B_812] :
      ( r1_xboole_0(A_811,B_812)
      | ~ r1_subset_1(A_811,B_812)
      | v1_xboole_0(B_812)
      | v1_xboole_0(A_811) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4047,plain,(
    ! [A_847,B_848] :
      ( k3_xboole_0(A_847,B_848) = k1_xboole_0
      | ~ r1_subset_1(A_847,B_848)
      | v1_xboole_0(B_848)
      | v1_xboole_0(A_847) ) ),
    inference(resolution,[status(thm)],[c_3666,c_6])).

tff(c_4050,plain,
    ( k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0
    | v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_4047])).

tff(c_4053,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_68,c_4050])).

tff(c_58,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_1061,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_1053])).

tff(c_3625,plain,(
    v4_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_3617])).

tff(c_3639,plain,
    ( k7_relat_1('#skF_7','#skF_5') = '#skF_7'
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_3625,c_3636])).

tff(c_3645,plain,(
    k7_relat_1('#skF_7','#skF_5') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1061,c_3639])).

tff(c_3709,plain,(
    ! [B_817] :
      ( k7_relat_1('#skF_7',B_817) = k1_xboole_0
      | ~ r1_xboole_0('#skF_5',B_817)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3645,c_3691])).

tff(c_3754,plain,(
    ! [B_821] :
      ( k7_relat_1('#skF_7',B_821) = k1_xboole_0
      | ~ r1_xboole_0('#skF_5',B_821) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1061,c_3709])).

tff(c_3777,plain,(
    ! [B_822] :
      ( k7_relat_1('#skF_7',B_822) = k1_xboole_0
      | ~ v1_xboole_0(B_822) ) ),
    inference(resolution,[status(thm)],[c_1036,c_3754])).

tff(c_3781,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_3777])).

tff(c_3829,plain,(
    ! [A_825,B_826,C_827] :
      ( k9_subset_1(A_825,B_826,C_827) = k3_xboole_0(B_826,C_827)
      | ~ m1_subset_1(C_827,k1_zfmisc_1(A_825)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_3840,plain,(
    ! [B_826] : k9_subset_1('#skF_3',B_826,'#skF_6') = k3_xboole_0(B_826,'#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_3829])).

tff(c_62,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_60,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_56,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_54,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_4086,plain,(
    ! [E_858,F_859,C_856,A_857,B_854,D_855] :
      ( v1_funct_1(k1_tmap_1(A_857,B_854,C_856,D_855,E_858,F_859))
      | ~ m1_subset_1(F_859,k1_zfmisc_1(k2_zfmisc_1(D_855,B_854)))
      | ~ v1_funct_2(F_859,D_855,B_854)
      | ~ v1_funct_1(F_859)
      | ~ m1_subset_1(E_858,k1_zfmisc_1(k2_zfmisc_1(C_856,B_854)))
      | ~ v1_funct_2(E_858,C_856,B_854)
      | ~ v1_funct_1(E_858)
      | ~ m1_subset_1(D_855,k1_zfmisc_1(A_857))
      | v1_xboole_0(D_855)
      | ~ m1_subset_1(C_856,k1_zfmisc_1(A_857))
      | v1_xboole_0(C_856)
      | v1_xboole_0(B_854)
      | v1_xboole_0(A_857) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_4088,plain,(
    ! [A_857,C_856,E_858] :
      ( v1_funct_1(k1_tmap_1(A_857,'#skF_4',C_856,'#skF_6',E_858,'#skF_8'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_858,k1_zfmisc_1(k2_zfmisc_1(C_856,'#skF_4')))
      | ~ v1_funct_2(E_858,C_856,'#skF_4')
      | ~ v1_funct_1(E_858)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_857))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_856,k1_zfmisc_1(A_857))
      | v1_xboole_0(C_856)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_857) ) ),
    inference(resolution,[status(thm)],[c_52,c_4086])).

tff(c_4093,plain,(
    ! [A_857,C_856,E_858] :
      ( v1_funct_1(k1_tmap_1(A_857,'#skF_4',C_856,'#skF_6',E_858,'#skF_8'))
      | ~ m1_subset_1(E_858,k1_zfmisc_1(k2_zfmisc_1(C_856,'#skF_4')))
      | ~ v1_funct_2(E_858,C_856,'#skF_4')
      | ~ v1_funct_1(E_858)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_857))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_856,k1_zfmisc_1(A_857))
      | v1_xboole_0(C_856)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_857) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4088])).

tff(c_4474,plain,(
    ! [A_923,C_924,E_925] :
      ( v1_funct_1(k1_tmap_1(A_923,'#skF_4',C_924,'#skF_6',E_925,'#skF_8'))
      | ~ m1_subset_1(E_925,k1_zfmisc_1(k2_zfmisc_1(C_924,'#skF_4')))
      | ~ v1_funct_2(E_925,C_924,'#skF_4')
      | ~ v1_funct_1(E_925)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_923))
      | ~ m1_subset_1(C_924,k1_zfmisc_1(A_923))
      | v1_xboole_0(C_924)
      | v1_xboole_0(A_923) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_4093])).

tff(c_4481,plain,(
    ! [A_923] :
      ( v1_funct_1(k1_tmap_1(A_923,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_923))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_923))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_923) ) ),
    inference(resolution,[status(thm)],[c_58,c_4474])).

tff(c_4491,plain,(
    ! [A_923] :
      ( v1_funct_1(k1_tmap_1(A_923,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_923))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_923))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_923) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_4481])).

tff(c_4721,plain,(
    ! [A_964] :
      ( v1_funct_1(k1_tmap_1(A_964,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_964))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_964))
      | v1_xboole_0(A_964) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_4491])).

tff(c_4724,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_4721])).

tff(c_4727,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_4724])).

tff(c_4728,plain,(
    v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_4727])).

tff(c_3986,plain,(
    ! [A_838,B_839,C_840,D_841] :
      ( k2_partfun1(A_838,B_839,C_840,D_841) = k7_relat_1(C_840,D_841)
      | ~ m1_subset_1(C_840,k1_zfmisc_1(k2_zfmisc_1(A_838,B_839)))
      | ~ v1_funct_1(C_840) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3990,plain,(
    ! [D_841] :
      ( k2_partfun1('#skF_5','#skF_4','#skF_7',D_841) = k7_relat_1('#skF_7',D_841)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_58,c_3986])).

tff(c_3996,plain,(
    ! [D_841] : k2_partfun1('#skF_5','#skF_4','#skF_7',D_841) = k7_relat_1('#skF_7',D_841) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_3990])).

tff(c_3988,plain,(
    ! [D_841] :
      ( k2_partfun1('#skF_6','#skF_4','#skF_8',D_841) = k7_relat_1('#skF_8',D_841)
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_52,c_3986])).

tff(c_3993,plain,(
    ! [D_841] : k2_partfun1('#skF_6','#skF_4','#skF_8',D_841) = k7_relat_1('#skF_8',D_841) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3988])).

tff(c_46,plain,(
    ! [E_165,C_163,F_166,A_161,B_162,D_164] :
      ( v1_funct_2(k1_tmap_1(A_161,B_162,C_163,D_164,E_165,F_166),k4_subset_1(A_161,C_163,D_164),B_162)
      | ~ m1_subset_1(F_166,k1_zfmisc_1(k2_zfmisc_1(D_164,B_162)))
      | ~ v1_funct_2(F_166,D_164,B_162)
      | ~ v1_funct_1(F_166)
      | ~ m1_subset_1(E_165,k1_zfmisc_1(k2_zfmisc_1(C_163,B_162)))
      | ~ v1_funct_2(E_165,C_163,B_162)
      | ~ v1_funct_1(E_165)
      | ~ m1_subset_1(D_164,k1_zfmisc_1(A_161))
      | v1_xboole_0(D_164)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(A_161))
      | v1_xboole_0(C_163)
      | v1_xboole_0(B_162)
      | v1_xboole_0(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_44,plain,(
    ! [E_165,C_163,F_166,A_161,B_162,D_164] :
      ( m1_subset_1(k1_tmap_1(A_161,B_162,C_163,D_164,E_165,F_166),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_161,C_163,D_164),B_162)))
      | ~ m1_subset_1(F_166,k1_zfmisc_1(k2_zfmisc_1(D_164,B_162)))
      | ~ v1_funct_2(F_166,D_164,B_162)
      | ~ v1_funct_1(F_166)
      | ~ m1_subset_1(E_165,k1_zfmisc_1(k2_zfmisc_1(C_163,B_162)))
      | ~ v1_funct_2(E_165,C_163,B_162)
      | ~ v1_funct_1(E_165)
      | ~ m1_subset_1(D_164,k1_zfmisc_1(A_161))
      | v1_xboole_0(D_164)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(A_161))
      | v1_xboole_0(C_163)
      | v1_xboole_0(B_162)
      | v1_xboole_0(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_4446,plain,(
    ! [D_914,C_910,A_909,B_912,F_911,E_913] :
      ( k2_partfun1(k4_subset_1(A_909,C_910,D_914),B_912,k1_tmap_1(A_909,B_912,C_910,D_914,E_913,F_911),C_910) = E_913
      | ~ m1_subset_1(k1_tmap_1(A_909,B_912,C_910,D_914,E_913,F_911),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_909,C_910,D_914),B_912)))
      | ~ v1_funct_2(k1_tmap_1(A_909,B_912,C_910,D_914,E_913,F_911),k4_subset_1(A_909,C_910,D_914),B_912)
      | ~ v1_funct_1(k1_tmap_1(A_909,B_912,C_910,D_914,E_913,F_911))
      | k2_partfun1(D_914,B_912,F_911,k9_subset_1(A_909,C_910,D_914)) != k2_partfun1(C_910,B_912,E_913,k9_subset_1(A_909,C_910,D_914))
      | ~ m1_subset_1(F_911,k1_zfmisc_1(k2_zfmisc_1(D_914,B_912)))
      | ~ v1_funct_2(F_911,D_914,B_912)
      | ~ v1_funct_1(F_911)
      | ~ m1_subset_1(E_913,k1_zfmisc_1(k2_zfmisc_1(C_910,B_912)))
      | ~ v1_funct_2(E_913,C_910,B_912)
      | ~ v1_funct_1(E_913)
      | ~ m1_subset_1(D_914,k1_zfmisc_1(A_909))
      | v1_xboole_0(D_914)
      | ~ m1_subset_1(C_910,k1_zfmisc_1(A_909))
      | v1_xboole_0(C_910)
      | v1_xboole_0(B_912)
      | v1_xboole_0(A_909) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_5082,plain,(
    ! [B_1037,D_1038,C_1039,F_1042,E_1041,A_1040] :
      ( k2_partfun1(k4_subset_1(A_1040,C_1039,D_1038),B_1037,k1_tmap_1(A_1040,B_1037,C_1039,D_1038,E_1041,F_1042),C_1039) = E_1041
      | ~ v1_funct_2(k1_tmap_1(A_1040,B_1037,C_1039,D_1038,E_1041,F_1042),k4_subset_1(A_1040,C_1039,D_1038),B_1037)
      | ~ v1_funct_1(k1_tmap_1(A_1040,B_1037,C_1039,D_1038,E_1041,F_1042))
      | k2_partfun1(D_1038,B_1037,F_1042,k9_subset_1(A_1040,C_1039,D_1038)) != k2_partfun1(C_1039,B_1037,E_1041,k9_subset_1(A_1040,C_1039,D_1038))
      | ~ m1_subset_1(F_1042,k1_zfmisc_1(k2_zfmisc_1(D_1038,B_1037)))
      | ~ v1_funct_2(F_1042,D_1038,B_1037)
      | ~ v1_funct_1(F_1042)
      | ~ m1_subset_1(E_1041,k1_zfmisc_1(k2_zfmisc_1(C_1039,B_1037)))
      | ~ v1_funct_2(E_1041,C_1039,B_1037)
      | ~ v1_funct_1(E_1041)
      | ~ m1_subset_1(D_1038,k1_zfmisc_1(A_1040))
      | v1_xboole_0(D_1038)
      | ~ m1_subset_1(C_1039,k1_zfmisc_1(A_1040))
      | v1_xboole_0(C_1039)
      | v1_xboole_0(B_1037)
      | v1_xboole_0(A_1040) ) ),
    inference(resolution,[status(thm)],[c_44,c_4446])).

tff(c_5611,plain,(
    ! [F_1109,B_1104,E_1108,D_1105,C_1106,A_1107] :
      ( k2_partfun1(k4_subset_1(A_1107,C_1106,D_1105),B_1104,k1_tmap_1(A_1107,B_1104,C_1106,D_1105,E_1108,F_1109),C_1106) = E_1108
      | ~ v1_funct_1(k1_tmap_1(A_1107,B_1104,C_1106,D_1105,E_1108,F_1109))
      | k2_partfun1(D_1105,B_1104,F_1109,k9_subset_1(A_1107,C_1106,D_1105)) != k2_partfun1(C_1106,B_1104,E_1108,k9_subset_1(A_1107,C_1106,D_1105))
      | ~ m1_subset_1(F_1109,k1_zfmisc_1(k2_zfmisc_1(D_1105,B_1104)))
      | ~ v1_funct_2(F_1109,D_1105,B_1104)
      | ~ v1_funct_1(F_1109)
      | ~ m1_subset_1(E_1108,k1_zfmisc_1(k2_zfmisc_1(C_1106,B_1104)))
      | ~ v1_funct_2(E_1108,C_1106,B_1104)
      | ~ v1_funct_1(E_1108)
      | ~ m1_subset_1(D_1105,k1_zfmisc_1(A_1107))
      | v1_xboole_0(D_1105)
      | ~ m1_subset_1(C_1106,k1_zfmisc_1(A_1107))
      | v1_xboole_0(C_1106)
      | v1_xboole_0(B_1104)
      | v1_xboole_0(A_1107) ) ),
    inference(resolution,[status(thm)],[c_46,c_5082])).

tff(c_5615,plain,(
    ! [A_1107,C_1106,E_1108] :
      ( k2_partfun1(k4_subset_1(A_1107,C_1106,'#skF_6'),'#skF_4',k1_tmap_1(A_1107,'#skF_4',C_1106,'#skF_6',E_1108,'#skF_8'),C_1106) = E_1108
      | ~ v1_funct_1(k1_tmap_1(A_1107,'#skF_4',C_1106,'#skF_6',E_1108,'#skF_8'))
      | k2_partfun1(C_1106,'#skF_4',E_1108,k9_subset_1(A_1107,C_1106,'#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1(A_1107,C_1106,'#skF_6'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_1108,k1_zfmisc_1(k2_zfmisc_1(C_1106,'#skF_4')))
      | ~ v1_funct_2(E_1108,C_1106,'#skF_4')
      | ~ v1_funct_1(E_1108)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1107))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_1106,k1_zfmisc_1(A_1107))
      | v1_xboole_0(C_1106)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1107) ) ),
    inference(resolution,[status(thm)],[c_52,c_5611])).

tff(c_5621,plain,(
    ! [A_1107,C_1106,E_1108] :
      ( k2_partfun1(k4_subset_1(A_1107,C_1106,'#skF_6'),'#skF_4',k1_tmap_1(A_1107,'#skF_4',C_1106,'#skF_6',E_1108,'#skF_8'),C_1106) = E_1108
      | ~ v1_funct_1(k1_tmap_1(A_1107,'#skF_4',C_1106,'#skF_6',E_1108,'#skF_8'))
      | k2_partfun1(C_1106,'#skF_4',E_1108,k9_subset_1(A_1107,C_1106,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_1107,C_1106,'#skF_6'))
      | ~ m1_subset_1(E_1108,k1_zfmisc_1(k2_zfmisc_1(C_1106,'#skF_4')))
      | ~ v1_funct_2(E_1108,C_1106,'#skF_4')
      | ~ v1_funct_1(E_1108)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1107))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_1106,k1_zfmisc_1(A_1107))
      | v1_xboole_0(C_1106)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_3993,c_5615])).

tff(c_6421,plain,(
    ! [A_1209,C_1210,E_1211] :
      ( k2_partfun1(k4_subset_1(A_1209,C_1210,'#skF_6'),'#skF_4',k1_tmap_1(A_1209,'#skF_4',C_1210,'#skF_6',E_1211,'#skF_8'),C_1210) = E_1211
      | ~ v1_funct_1(k1_tmap_1(A_1209,'#skF_4',C_1210,'#skF_6',E_1211,'#skF_8'))
      | k2_partfun1(C_1210,'#skF_4',E_1211,k9_subset_1(A_1209,C_1210,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_1209,C_1210,'#skF_6'))
      | ~ m1_subset_1(E_1211,k1_zfmisc_1(k2_zfmisc_1(C_1210,'#skF_4')))
      | ~ v1_funct_2(E_1211,C_1210,'#skF_4')
      | ~ v1_funct_1(E_1211)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1209))
      | ~ m1_subset_1(C_1210,k1_zfmisc_1(A_1209))
      | v1_xboole_0(C_1210)
      | v1_xboole_0(A_1209) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_5621])).

tff(c_6428,plain,(
    ! [A_1209] :
      ( k2_partfun1(k4_subset_1(A_1209,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_1209,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1209,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1(A_1209,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_1209,'#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1209))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1209))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_1209) ) ),
    inference(resolution,[status(thm)],[c_58,c_6421])).

tff(c_6438,plain,(
    ! [A_1209] :
      ( k2_partfun1(k4_subset_1(A_1209,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_1209,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1209,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_1209,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_1209,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1209))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1209))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_1209) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_3996,c_6428])).

tff(c_6440,plain,(
    ! [A_1212] :
      ( k2_partfun1(k4_subset_1(A_1212,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_1212,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1212,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_1212,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_1212,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1212))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1212))
      | v1_xboole_0(A_1212) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_6438])).

tff(c_1092,plain,(
    ! [C_405,A_406,B_407] :
      ( v4_relat_1(C_405,A_406)
      | ~ m1_subset_1(C_405,k1_zfmisc_1(k2_zfmisc_1(A_406,B_407))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1099,plain,(
    v4_relat_1('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_1092])).

tff(c_1111,plain,(
    ! [B_411,A_412] :
      ( k7_relat_1(B_411,A_412) = B_411
      | ~ v4_relat_1(B_411,A_412)
      | ~ v1_relat_1(B_411) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1117,plain,
    ( k7_relat_1('#skF_8','#skF_6') = '#skF_8'
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_1099,c_1111])).

tff(c_1123,plain,(
    k7_relat_1('#skF_8','#skF_6') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1060,c_1117])).

tff(c_1242,plain,(
    ! [C_433,A_434,B_435] :
      ( k7_relat_1(k7_relat_1(C_433,A_434),B_435) = k1_xboole_0
      | ~ r1_xboole_0(A_434,B_435)
      | ~ v1_relat_1(C_433) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1257,plain,(
    ! [B_435] :
      ( k7_relat_1('#skF_8',B_435) = k1_xboole_0
      | ~ r1_xboole_0('#skF_6',B_435)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1123,c_1242])).

tff(c_1267,plain,(
    ! [B_436] :
      ( k7_relat_1('#skF_8',B_436) = k1_xboole_0
      | ~ r1_xboole_0('#skF_6',B_436) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1060,c_1257])).

tff(c_1301,plain,(
    ! [B_441] :
      ( k7_relat_1('#skF_8',B_441) = k1_xboole_0
      | ~ v1_xboole_0(B_441) ) ),
    inference(resolution,[status(thm)],[c_1036,c_1267])).

tff(c_1305,plain,(
    k7_relat_1('#skF_8',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_1301])).

tff(c_1141,plain,(
    ! [A_416,B_417] :
      ( r1_xboole_0(A_416,B_417)
      | ~ r1_subset_1(A_416,B_417)
      | v1_xboole_0(B_417)
      | v1_xboole_0(A_416) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1542,plain,(
    ! [A_469,B_470] :
      ( k3_xboole_0(A_469,B_470) = k1_xboole_0
      | ~ r1_subset_1(A_469,B_470)
      | v1_xboole_0(B_470)
      | v1_xboole_0(A_469) ) ),
    inference(resolution,[status(thm)],[c_1141,c_6])).

tff(c_1548,plain,
    ( k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0
    | v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_1542])).

tff(c_1552,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_68,c_1548])).

tff(c_1100,plain,(
    v4_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_1092])).

tff(c_1114,plain,
    ( k7_relat_1('#skF_7','#skF_5') = '#skF_7'
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_1100,c_1111])).

tff(c_1120,plain,(
    k7_relat_1('#skF_7','#skF_5') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1061,c_1114])).

tff(c_1260,plain,(
    ! [B_435] :
      ( k7_relat_1('#skF_7',B_435) = k1_xboole_0
      | ~ r1_xboole_0('#skF_5',B_435)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1120,c_1242])).

tff(c_1315,plain,(
    ! [B_442] :
      ( k7_relat_1('#skF_7',B_442) = k1_xboole_0
      | ~ r1_xboole_0('#skF_5',B_442) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1061,c_1260])).

tff(c_1339,plain,(
    ! [B_444] :
      ( k7_relat_1('#skF_7',B_444) = k1_xboole_0
      | ~ v1_xboole_0(B_444) ) ),
    inference(resolution,[status(thm)],[c_1036,c_1315])).

tff(c_1343,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_1339])).

tff(c_1166,plain,(
    ! [A_420,B_421,C_422] :
      ( k9_subset_1(A_420,B_421,C_422) = k3_xboole_0(B_421,C_422)
      | ~ m1_subset_1(C_422,k1_zfmisc_1(A_420)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1177,plain,(
    ! [B_421] : k9_subset_1('#skF_3',B_421,'#skF_6') = k3_xboole_0(B_421,'#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_1166])).

tff(c_1392,plain,(
    ! [F_452,A_450,D_448,B_447,E_451,C_449] :
      ( v1_funct_1(k1_tmap_1(A_450,B_447,C_449,D_448,E_451,F_452))
      | ~ m1_subset_1(F_452,k1_zfmisc_1(k2_zfmisc_1(D_448,B_447)))
      | ~ v1_funct_2(F_452,D_448,B_447)
      | ~ v1_funct_1(F_452)
      | ~ m1_subset_1(E_451,k1_zfmisc_1(k2_zfmisc_1(C_449,B_447)))
      | ~ v1_funct_2(E_451,C_449,B_447)
      | ~ v1_funct_1(E_451)
      | ~ m1_subset_1(D_448,k1_zfmisc_1(A_450))
      | v1_xboole_0(D_448)
      | ~ m1_subset_1(C_449,k1_zfmisc_1(A_450))
      | v1_xboole_0(C_449)
      | v1_xboole_0(B_447)
      | v1_xboole_0(A_450) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_1394,plain,(
    ! [A_450,C_449,E_451] :
      ( v1_funct_1(k1_tmap_1(A_450,'#skF_4',C_449,'#skF_6',E_451,'#skF_8'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_451,k1_zfmisc_1(k2_zfmisc_1(C_449,'#skF_4')))
      | ~ v1_funct_2(E_451,C_449,'#skF_4')
      | ~ v1_funct_1(E_451)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_450))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_449,k1_zfmisc_1(A_450))
      | v1_xboole_0(C_449)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_450) ) ),
    inference(resolution,[status(thm)],[c_52,c_1392])).

tff(c_1399,plain,(
    ! [A_450,C_449,E_451] :
      ( v1_funct_1(k1_tmap_1(A_450,'#skF_4',C_449,'#skF_6',E_451,'#skF_8'))
      | ~ m1_subset_1(E_451,k1_zfmisc_1(k2_zfmisc_1(C_449,'#skF_4')))
      | ~ v1_funct_2(E_451,C_449,'#skF_4')
      | ~ v1_funct_1(E_451)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_450))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_449,k1_zfmisc_1(A_450))
      | v1_xboole_0(C_449)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_450) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_1394])).

tff(c_1857,plain,(
    ! [A_516,C_517,E_518] :
      ( v1_funct_1(k1_tmap_1(A_516,'#skF_4',C_517,'#skF_6',E_518,'#skF_8'))
      | ~ m1_subset_1(E_518,k1_zfmisc_1(k2_zfmisc_1(C_517,'#skF_4')))
      | ~ v1_funct_2(E_518,C_517,'#skF_4')
      | ~ v1_funct_1(E_518)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_516))
      | ~ m1_subset_1(C_517,k1_zfmisc_1(A_516))
      | v1_xboole_0(C_517)
      | v1_xboole_0(A_516) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_1399])).

tff(c_1864,plain,(
    ! [A_516] :
      ( v1_funct_1(k1_tmap_1(A_516,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_516))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_516))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_516) ) ),
    inference(resolution,[status(thm)],[c_58,c_1857])).

tff(c_1874,plain,(
    ! [A_516] :
      ( v1_funct_1(k1_tmap_1(A_516,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_516))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_516))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_516) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1864])).

tff(c_2076,plain,(
    ! [A_554] :
      ( v1_funct_1(k1_tmap_1(A_554,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_554))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_554))
      | v1_xboole_0(A_554) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1874])).

tff(c_2079,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_2076])).

tff(c_2082,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2079])).

tff(c_2083,plain,(
    v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2082])).

tff(c_1290,plain,(
    ! [A_437,B_438,C_439,D_440] :
      ( k2_partfun1(A_437,B_438,C_439,D_440) = k7_relat_1(C_439,D_440)
      | ~ m1_subset_1(C_439,k1_zfmisc_1(k2_zfmisc_1(A_437,B_438)))
      | ~ v1_funct_1(C_439) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1294,plain,(
    ! [D_440] :
      ( k2_partfun1('#skF_5','#skF_4','#skF_7',D_440) = k7_relat_1('#skF_7',D_440)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_58,c_1290])).

tff(c_1300,plain,(
    ! [D_440] : k2_partfun1('#skF_5','#skF_4','#skF_7',D_440) = k7_relat_1('#skF_7',D_440) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1294])).

tff(c_1292,plain,(
    ! [D_440] :
      ( k2_partfun1('#skF_6','#skF_4','#skF_8',D_440) = k7_relat_1('#skF_8',D_440)
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_52,c_1290])).

tff(c_1297,plain,(
    ! [D_440] : k2_partfun1('#skF_6','#skF_4','#skF_8',D_440) = k7_relat_1('#skF_8',D_440) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1292])).

tff(c_1838,plain,(
    ! [B_508,C_506,A_505,E_509,D_510,F_507] :
      ( k2_partfun1(k4_subset_1(A_505,C_506,D_510),B_508,k1_tmap_1(A_505,B_508,C_506,D_510,E_509,F_507),D_510) = F_507
      | ~ m1_subset_1(k1_tmap_1(A_505,B_508,C_506,D_510,E_509,F_507),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_505,C_506,D_510),B_508)))
      | ~ v1_funct_2(k1_tmap_1(A_505,B_508,C_506,D_510,E_509,F_507),k4_subset_1(A_505,C_506,D_510),B_508)
      | ~ v1_funct_1(k1_tmap_1(A_505,B_508,C_506,D_510,E_509,F_507))
      | k2_partfun1(D_510,B_508,F_507,k9_subset_1(A_505,C_506,D_510)) != k2_partfun1(C_506,B_508,E_509,k9_subset_1(A_505,C_506,D_510))
      | ~ m1_subset_1(F_507,k1_zfmisc_1(k2_zfmisc_1(D_510,B_508)))
      | ~ v1_funct_2(F_507,D_510,B_508)
      | ~ v1_funct_1(F_507)
      | ~ m1_subset_1(E_509,k1_zfmisc_1(k2_zfmisc_1(C_506,B_508)))
      | ~ v1_funct_2(E_509,C_506,B_508)
      | ~ v1_funct_1(E_509)
      | ~ m1_subset_1(D_510,k1_zfmisc_1(A_505))
      | v1_xboole_0(D_510)
      | ~ m1_subset_1(C_506,k1_zfmisc_1(A_505))
      | v1_xboole_0(C_506)
      | v1_xboole_0(B_508)
      | v1_xboole_0(A_505) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_2669,plain,(
    ! [E_673,D_670,B_669,F_674,A_672,C_671] :
      ( k2_partfun1(k4_subset_1(A_672,C_671,D_670),B_669,k1_tmap_1(A_672,B_669,C_671,D_670,E_673,F_674),D_670) = F_674
      | ~ v1_funct_2(k1_tmap_1(A_672,B_669,C_671,D_670,E_673,F_674),k4_subset_1(A_672,C_671,D_670),B_669)
      | ~ v1_funct_1(k1_tmap_1(A_672,B_669,C_671,D_670,E_673,F_674))
      | k2_partfun1(D_670,B_669,F_674,k9_subset_1(A_672,C_671,D_670)) != k2_partfun1(C_671,B_669,E_673,k9_subset_1(A_672,C_671,D_670))
      | ~ m1_subset_1(F_674,k1_zfmisc_1(k2_zfmisc_1(D_670,B_669)))
      | ~ v1_funct_2(F_674,D_670,B_669)
      | ~ v1_funct_1(F_674)
      | ~ m1_subset_1(E_673,k1_zfmisc_1(k2_zfmisc_1(C_671,B_669)))
      | ~ v1_funct_2(E_673,C_671,B_669)
      | ~ v1_funct_1(E_673)
      | ~ m1_subset_1(D_670,k1_zfmisc_1(A_672))
      | v1_xboole_0(D_670)
      | ~ m1_subset_1(C_671,k1_zfmisc_1(A_672))
      | v1_xboole_0(C_671)
      | v1_xboole_0(B_669)
      | v1_xboole_0(A_672) ) ),
    inference(resolution,[status(thm)],[c_44,c_1838])).

tff(c_3215,plain,(
    ! [F_744,C_741,B_739,E_743,D_740,A_742] :
      ( k2_partfun1(k4_subset_1(A_742,C_741,D_740),B_739,k1_tmap_1(A_742,B_739,C_741,D_740,E_743,F_744),D_740) = F_744
      | ~ v1_funct_1(k1_tmap_1(A_742,B_739,C_741,D_740,E_743,F_744))
      | k2_partfun1(D_740,B_739,F_744,k9_subset_1(A_742,C_741,D_740)) != k2_partfun1(C_741,B_739,E_743,k9_subset_1(A_742,C_741,D_740))
      | ~ m1_subset_1(F_744,k1_zfmisc_1(k2_zfmisc_1(D_740,B_739)))
      | ~ v1_funct_2(F_744,D_740,B_739)
      | ~ v1_funct_1(F_744)
      | ~ m1_subset_1(E_743,k1_zfmisc_1(k2_zfmisc_1(C_741,B_739)))
      | ~ v1_funct_2(E_743,C_741,B_739)
      | ~ v1_funct_1(E_743)
      | ~ m1_subset_1(D_740,k1_zfmisc_1(A_742))
      | v1_xboole_0(D_740)
      | ~ m1_subset_1(C_741,k1_zfmisc_1(A_742))
      | v1_xboole_0(C_741)
      | v1_xboole_0(B_739)
      | v1_xboole_0(A_742) ) ),
    inference(resolution,[status(thm)],[c_46,c_2669])).

tff(c_3219,plain,(
    ! [A_742,C_741,E_743] :
      ( k2_partfun1(k4_subset_1(A_742,C_741,'#skF_6'),'#skF_4',k1_tmap_1(A_742,'#skF_4',C_741,'#skF_6',E_743,'#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_742,'#skF_4',C_741,'#skF_6',E_743,'#skF_8'))
      | k2_partfun1(C_741,'#skF_4',E_743,k9_subset_1(A_742,C_741,'#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1(A_742,C_741,'#skF_6'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_743,k1_zfmisc_1(k2_zfmisc_1(C_741,'#skF_4')))
      | ~ v1_funct_2(E_743,C_741,'#skF_4')
      | ~ v1_funct_1(E_743)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_742))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_741,k1_zfmisc_1(A_742))
      | v1_xboole_0(C_741)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_742) ) ),
    inference(resolution,[status(thm)],[c_52,c_3215])).

tff(c_3225,plain,(
    ! [A_742,C_741,E_743] :
      ( k2_partfun1(k4_subset_1(A_742,C_741,'#skF_6'),'#skF_4',k1_tmap_1(A_742,'#skF_4',C_741,'#skF_6',E_743,'#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_742,'#skF_4',C_741,'#skF_6',E_743,'#skF_8'))
      | k2_partfun1(C_741,'#skF_4',E_743,k9_subset_1(A_742,C_741,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_742,C_741,'#skF_6'))
      | ~ m1_subset_1(E_743,k1_zfmisc_1(k2_zfmisc_1(C_741,'#skF_4')))
      | ~ v1_funct_2(E_743,C_741,'#skF_4')
      | ~ v1_funct_1(E_743)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_742))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_741,k1_zfmisc_1(A_742))
      | v1_xboole_0(C_741)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_742) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_1297,c_3219])).

tff(c_3433,plain,(
    ! [A_777,C_778,E_779] :
      ( k2_partfun1(k4_subset_1(A_777,C_778,'#skF_6'),'#skF_4',k1_tmap_1(A_777,'#skF_4',C_778,'#skF_6',E_779,'#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_777,'#skF_4',C_778,'#skF_6',E_779,'#skF_8'))
      | k2_partfun1(C_778,'#skF_4',E_779,k9_subset_1(A_777,C_778,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_777,C_778,'#skF_6'))
      | ~ m1_subset_1(E_779,k1_zfmisc_1(k2_zfmisc_1(C_778,'#skF_4')))
      | ~ v1_funct_2(E_779,C_778,'#skF_4')
      | ~ v1_funct_1(E_779)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_777))
      | ~ m1_subset_1(C_778,k1_zfmisc_1(A_777))
      | v1_xboole_0(C_778)
      | v1_xboole_0(A_777) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_3225])).

tff(c_3440,plain,(
    ! [A_777] :
      ( k2_partfun1(k4_subset_1(A_777,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_777,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_777,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1(A_777,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_777,'#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_777))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_777))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_777) ) ),
    inference(resolution,[status(thm)],[c_58,c_3433])).

tff(c_3450,plain,(
    ! [A_777] :
      ( k2_partfun1(k4_subset_1(A_777,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_777,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_777,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_777,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_777,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_777))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_777))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_777) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1300,c_3440])).

tff(c_3568,plain,(
    ! [A_796] :
      ( k2_partfun1(k4_subset_1(A_796,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_796,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_796,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_796,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_796,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_796))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_796))
      | v1_xboole_0(A_796) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3450])).

tff(c_99,plain,(
    ! [A_233,B_234] :
      ( r2_hidden('#skF_2'(A_233,B_234),B_234)
      | r1_xboole_0(A_233,B_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_103,plain,(
    ! [B_234,A_233] :
      ( ~ v1_xboole_0(B_234)
      | r1_xboole_0(A_233,B_234) ) ),
    inference(resolution,[status(thm)],[c_99,c_2])).

tff(c_125,plain,(
    ! [C_242,A_243,B_244] :
      ( v1_relat_1(C_242)
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1(A_243,B_244))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_132,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_52,c_125])).

tff(c_158,plain,(
    ! [C_250,A_251,B_252] :
      ( v4_relat_1(C_250,A_251)
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(A_251,B_252))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_165,plain,(
    v4_relat_1('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_158])).

tff(c_167,plain,(
    ! [B_253,A_254] :
      ( k7_relat_1(B_253,A_254) = B_253
      | ~ v4_relat_1(B_253,A_254)
      | ~ v1_relat_1(B_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_173,plain,
    ( k7_relat_1('#skF_8','#skF_6') = '#skF_8'
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_165,c_167])).

tff(c_179,plain,(
    k7_relat_1('#skF_8','#skF_6') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_173])).

tff(c_308,plain,(
    ! [C_278,A_279,B_280] :
      ( k7_relat_1(k7_relat_1(C_278,A_279),B_280) = k1_xboole_0
      | ~ r1_xboole_0(A_279,B_280)
      | ~ v1_relat_1(C_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_323,plain,(
    ! [B_280] :
      ( k7_relat_1('#skF_8',B_280) = k1_xboole_0
      | ~ r1_xboole_0('#skF_6',B_280)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_308])).

tff(c_333,plain,(
    ! [B_281] :
      ( k7_relat_1('#skF_8',B_281) = k1_xboole_0
      | ~ r1_xboole_0('#skF_6',B_281) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_323])).

tff(c_356,plain,(
    ! [B_282] :
      ( k7_relat_1('#skF_8',B_282) = k1_xboole_0
      | ~ v1_xboole_0(B_282) ) ),
    inference(resolution,[status(thm)],[c_103,c_333])).

tff(c_360,plain,(
    k7_relat_1('#skF_8',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_356])).

tff(c_220,plain,(
    ! [A_263,B_264] :
      ( r1_xboole_0(A_263,B_264)
      | ~ r1_subset_1(A_263,B_264)
      | v1_xboole_0(B_264)
      | v1_xboole_0(A_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_608,plain,(
    ! [A_314,B_315] :
      ( k3_xboole_0(A_314,B_315) = k1_xboole_0
      | ~ r1_subset_1(A_314,B_315)
      | v1_xboole_0(B_315)
      | v1_xboole_0(A_314) ) ),
    inference(resolution,[status(thm)],[c_220,c_6])).

tff(c_614,plain,
    ( k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0
    | v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_608])).

tff(c_618,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_68,c_614])).

tff(c_133,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_125])).

tff(c_166,plain,(
    v4_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_158])).

tff(c_170,plain,
    ( k7_relat_1('#skF_7','#skF_5') = '#skF_7'
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_166,c_167])).

tff(c_176,plain,(
    k7_relat_1('#skF_7','#skF_5') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_170])).

tff(c_326,plain,(
    ! [B_280] :
      ( k7_relat_1('#skF_7',B_280) = k1_xboole_0
      | ~ r1_xboole_0('#skF_5',B_280)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_308])).

tff(c_381,plain,(
    ! [B_287] :
      ( k7_relat_1('#skF_7',B_287) = k1_xboole_0
      | ~ r1_xboole_0('#skF_5',B_287) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_326])).

tff(c_404,plain,(
    ! [B_288] :
      ( k7_relat_1('#skF_7',B_288) = k1_xboole_0
      | ~ v1_xboole_0(B_288) ) ),
    inference(resolution,[status(thm)],[c_103,c_381])).

tff(c_408,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_404])).

tff(c_361,plain,(
    ! [A_283,B_284,C_285,D_286] :
      ( k2_partfun1(A_283,B_284,C_285,D_286) = k7_relat_1(C_285,D_286)
      | ~ m1_subset_1(C_285,k1_zfmisc_1(k2_zfmisc_1(A_283,B_284)))
      | ~ v1_funct_1(C_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_363,plain,(
    ! [D_286] :
      ( k2_partfun1('#skF_6','#skF_4','#skF_8',D_286) = k7_relat_1('#skF_8',D_286)
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_52,c_361])).

tff(c_368,plain,(
    ! [D_286] : k2_partfun1('#skF_6','#skF_4','#skF_8',D_286) = k7_relat_1('#skF_8',D_286) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_363])).

tff(c_365,plain,(
    ! [D_286] :
      ( k2_partfun1('#skF_5','#skF_4','#skF_7',D_286) = k7_relat_1('#skF_7',D_286)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_58,c_361])).

tff(c_371,plain,(
    ! [D_286] : k2_partfun1('#skF_5','#skF_4','#skF_7',D_286) = k7_relat_1('#skF_7',D_286) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_365])).

tff(c_242,plain,(
    ! [A_268,B_269,C_270] :
      ( k9_subset_1(A_268,B_269,C_270) = k3_xboole_0(B_269,C_270)
      | ~ m1_subset_1(C_270,k1_zfmisc_1(A_268)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_253,plain,(
    ! [B_269] : k9_subset_1('#skF_3',B_269,'#skF_6') = k3_xboole_0(B_269,'#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_242])).

tff(c_50,plain,
    ( k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') != '#skF_8'
    | k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') != '#skF_7'
    | k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_98,plain,(
    k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_255,plain,(
    k2_partfun1('#skF_5','#skF_4','#skF_7',k3_xboole_0('#skF_5','#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_253,c_98])).

tff(c_1025,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_618,c_408,c_618,c_368,c_371,c_255])).

tff(c_1026,plain,
    ( k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') != '#skF_7'
    | k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1072,plain,(
    k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1026])).

tff(c_3579,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3568,c_1072])).

tff(c_3593,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_1305,c_1552,c_1343,c_1552,c_1177,c_1177,c_2083,c_3579])).

tff(c_3595,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_3593])).

tff(c_3596,plain,(
    k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1026])).

tff(c_6449,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6440,c_3596])).

tff(c_6460,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_3743,c_4053,c_3781,c_4053,c_3840,c_3840,c_4728,c_6449])).

tff(c_6462,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_6460])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:08:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.87/2.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.12/2.87  
% 8.12/2.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.12/2.87  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2
% 8.12/2.87  
% 8.12/2.87  %Foreground sorts:
% 8.12/2.87  
% 8.12/2.87  
% 8.12/2.87  %Background operators:
% 8.12/2.87  
% 8.12/2.87  
% 8.12/2.87  %Foreground operators:
% 8.12/2.87  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 8.12/2.87  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.12/2.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.12/2.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.12/2.87  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.12/2.87  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.12/2.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.12/2.87  tff('#skF_7', type, '#skF_7': $i).
% 8.12/2.87  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.12/2.87  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 8.12/2.87  tff('#skF_5', type, '#skF_5': $i).
% 8.12/2.87  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.12/2.87  tff('#skF_6', type, '#skF_6': $i).
% 8.12/2.87  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.12/2.87  tff('#skF_3', type, '#skF_3': $i).
% 8.12/2.87  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.12/2.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.12/2.87  tff('#skF_8', type, '#skF_8': $i).
% 8.12/2.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.12/2.87  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.12/2.87  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.12/2.87  tff('#skF_4', type, '#skF_4': $i).
% 8.12/2.87  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.12/2.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.12/2.87  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.12/2.87  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 8.12/2.87  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.12/2.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.12/2.87  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.12/2.87  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 8.12/2.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.12/2.87  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.12/2.87  
% 8.12/2.90  tff(f_222, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 8.12/2.90  tff(f_36, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.12/2.90  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 8.12/2.90  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.12/2.90  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.12/2.90  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.12/2.90  tff(f_72, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 8.12/2.90  tff(f_66, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 8.12/2.90  tff(f_82, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 8.12/2.90  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.12/2.90  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 8.12/2.90  tff(f_180, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 8.12/2.90  tff(f_98, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 8.12/2.90  tff(f_146, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 8.12/2.90  tff(c_76, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_222])).
% 8.12/2.90  tff(c_70, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_222])).
% 8.12/2.90  tff(c_66, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_222])).
% 8.12/2.90  tff(c_10, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.12/2.90  tff(c_1032, plain, (![A_388, B_389]: (r2_hidden('#skF_2'(A_388, B_389), B_389) | r1_xboole_0(A_388, B_389))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.12/2.90  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.12/2.90  tff(c_1036, plain, (![B_389, A_388]: (~v1_xboole_0(B_389) | r1_xboole_0(A_388, B_389))), inference(resolution, [status(thm)], [c_1032, c_2])).
% 8.12/2.90  tff(c_52, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_222])).
% 8.12/2.90  tff(c_1053, plain, (![C_395, A_396, B_397]: (v1_relat_1(C_395) | ~m1_subset_1(C_395, k1_zfmisc_1(k2_zfmisc_1(A_396, B_397))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.12/2.90  tff(c_1060, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_52, c_1053])).
% 8.12/2.90  tff(c_3617, plain, (![C_800, A_801, B_802]: (v4_relat_1(C_800, A_801) | ~m1_subset_1(C_800, k1_zfmisc_1(k2_zfmisc_1(A_801, B_802))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.12/2.90  tff(c_3624, plain, (v4_relat_1('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_52, c_3617])).
% 8.12/2.90  tff(c_3636, plain, (![B_806, A_807]: (k7_relat_1(B_806, A_807)=B_806 | ~v4_relat_1(B_806, A_807) | ~v1_relat_1(B_806))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.12/2.90  tff(c_3642, plain, (k7_relat_1('#skF_8', '#skF_6')='#skF_8' | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_3624, c_3636])).
% 8.12/2.90  tff(c_3648, plain, (k7_relat_1('#skF_8', '#skF_6')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1060, c_3642])).
% 8.12/2.90  tff(c_3691, plain, (![C_815, A_816, B_817]: (k7_relat_1(k7_relat_1(C_815, A_816), B_817)=k1_xboole_0 | ~r1_xboole_0(A_816, B_817) | ~v1_relat_1(C_815))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.12/2.90  tff(c_3706, plain, (![B_817]: (k7_relat_1('#skF_8', B_817)=k1_xboole_0 | ~r1_xboole_0('#skF_6', B_817) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_3648, c_3691])).
% 8.12/2.90  tff(c_3716, plain, (![B_818]: (k7_relat_1('#skF_8', B_818)=k1_xboole_0 | ~r1_xboole_0('#skF_6', B_818))), inference(demodulation, [status(thm), theory('equality')], [c_1060, c_3706])).
% 8.12/2.90  tff(c_3739, plain, (![B_819]: (k7_relat_1('#skF_8', B_819)=k1_xboole_0 | ~v1_xboole_0(B_819))), inference(resolution, [status(thm)], [c_1036, c_3716])).
% 8.12/2.90  tff(c_3743, plain, (k7_relat_1('#skF_8', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_3739])).
% 8.12/2.90  tff(c_72, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_222])).
% 8.12/2.90  tff(c_68, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_222])).
% 8.12/2.90  tff(c_64, plain, (r1_subset_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_222])).
% 8.12/2.90  tff(c_3666, plain, (![A_811, B_812]: (r1_xboole_0(A_811, B_812) | ~r1_subset_1(A_811, B_812) | v1_xboole_0(B_812) | v1_xboole_0(A_811))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.12/2.90  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.12/2.90  tff(c_4047, plain, (![A_847, B_848]: (k3_xboole_0(A_847, B_848)=k1_xboole_0 | ~r1_subset_1(A_847, B_848) | v1_xboole_0(B_848) | v1_xboole_0(A_847))), inference(resolution, [status(thm)], [c_3666, c_6])).
% 8.12/2.90  tff(c_4050, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0 | v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_64, c_4047])).
% 8.12/2.90  tff(c_4053, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_72, c_68, c_4050])).
% 8.12/2.90  tff(c_58, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_222])).
% 8.12/2.90  tff(c_1061, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_58, c_1053])).
% 8.12/2.90  tff(c_3625, plain, (v4_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_58, c_3617])).
% 8.12/2.90  tff(c_3639, plain, (k7_relat_1('#skF_7', '#skF_5')='#skF_7' | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_3625, c_3636])).
% 8.12/2.90  tff(c_3645, plain, (k7_relat_1('#skF_7', '#skF_5')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_1061, c_3639])).
% 8.12/2.90  tff(c_3709, plain, (![B_817]: (k7_relat_1('#skF_7', B_817)=k1_xboole_0 | ~r1_xboole_0('#skF_5', B_817) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_3645, c_3691])).
% 8.12/2.90  tff(c_3754, plain, (![B_821]: (k7_relat_1('#skF_7', B_821)=k1_xboole_0 | ~r1_xboole_0('#skF_5', B_821))), inference(demodulation, [status(thm), theory('equality')], [c_1061, c_3709])).
% 8.12/2.90  tff(c_3777, plain, (![B_822]: (k7_relat_1('#skF_7', B_822)=k1_xboole_0 | ~v1_xboole_0(B_822))), inference(resolution, [status(thm)], [c_1036, c_3754])).
% 8.12/2.90  tff(c_3781, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_3777])).
% 8.12/2.90  tff(c_3829, plain, (![A_825, B_826, C_827]: (k9_subset_1(A_825, B_826, C_827)=k3_xboole_0(B_826, C_827) | ~m1_subset_1(C_827, k1_zfmisc_1(A_825)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.12/2.90  tff(c_3840, plain, (![B_826]: (k9_subset_1('#skF_3', B_826, '#skF_6')=k3_xboole_0(B_826, '#skF_6'))), inference(resolution, [status(thm)], [c_66, c_3829])).
% 8.12/2.90  tff(c_62, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_222])).
% 8.12/2.90  tff(c_60, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_222])).
% 8.12/2.90  tff(c_74, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_222])).
% 8.12/2.90  tff(c_56, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_222])).
% 8.12/2.90  tff(c_54, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_222])).
% 8.12/2.90  tff(c_4086, plain, (![E_858, F_859, C_856, A_857, B_854, D_855]: (v1_funct_1(k1_tmap_1(A_857, B_854, C_856, D_855, E_858, F_859)) | ~m1_subset_1(F_859, k1_zfmisc_1(k2_zfmisc_1(D_855, B_854))) | ~v1_funct_2(F_859, D_855, B_854) | ~v1_funct_1(F_859) | ~m1_subset_1(E_858, k1_zfmisc_1(k2_zfmisc_1(C_856, B_854))) | ~v1_funct_2(E_858, C_856, B_854) | ~v1_funct_1(E_858) | ~m1_subset_1(D_855, k1_zfmisc_1(A_857)) | v1_xboole_0(D_855) | ~m1_subset_1(C_856, k1_zfmisc_1(A_857)) | v1_xboole_0(C_856) | v1_xboole_0(B_854) | v1_xboole_0(A_857))), inference(cnfTransformation, [status(thm)], [f_180])).
% 8.12/2.90  tff(c_4088, plain, (![A_857, C_856, E_858]: (v1_funct_1(k1_tmap_1(A_857, '#skF_4', C_856, '#skF_6', E_858, '#skF_8')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_858, k1_zfmisc_1(k2_zfmisc_1(C_856, '#skF_4'))) | ~v1_funct_2(E_858, C_856, '#skF_4') | ~v1_funct_1(E_858) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_857)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_856, k1_zfmisc_1(A_857)) | v1_xboole_0(C_856) | v1_xboole_0('#skF_4') | v1_xboole_0(A_857))), inference(resolution, [status(thm)], [c_52, c_4086])).
% 8.12/2.90  tff(c_4093, plain, (![A_857, C_856, E_858]: (v1_funct_1(k1_tmap_1(A_857, '#skF_4', C_856, '#skF_6', E_858, '#skF_8')) | ~m1_subset_1(E_858, k1_zfmisc_1(k2_zfmisc_1(C_856, '#skF_4'))) | ~v1_funct_2(E_858, C_856, '#skF_4') | ~v1_funct_1(E_858) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_857)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_856, k1_zfmisc_1(A_857)) | v1_xboole_0(C_856) | v1_xboole_0('#skF_4') | v1_xboole_0(A_857))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_4088])).
% 8.12/2.90  tff(c_4474, plain, (![A_923, C_924, E_925]: (v1_funct_1(k1_tmap_1(A_923, '#skF_4', C_924, '#skF_6', E_925, '#skF_8')) | ~m1_subset_1(E_925, k1_zfmisc_1(k2_zfmisc_1(C_924, '#skF_4'))) | ~v1_funct_2(E_925, C_924, '#skF_4') | ~v1_funct_1(E_925) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_923)) | ~m1_subset_1(C_924, k1_zfmisc_1(A_923)) | v1_xboole_0(C_924) | v1_xboole_0(A_923))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_4093])).
% 8.12/2.90  tff(c_4481, plain, (![A_923]: (v1_funct_1(k1_tmap_1(A_923, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_923)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_923)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_923))), inference(resolution, [status(thm)], [c_58, c_4474])).
% 8.12/2.90  tff(c_4491, plain, (![A_923]: (v1_funct_1(k1_tmap_1(A_923, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_923)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_923)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_923))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_4481])).
% 8.12/2.90  tff(c_4721, plain, (![A_964]: (v1_funct_1(k1_tmap_1(A_964, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_964)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_964)) | v1_xboole_0(A_964))), inference(negUnitSimplification, [status(thm)], [c_72, c_4491])).
% 8.12/2.90  tff(c_4724, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_70, c_4721])).
% 8.12/2.90  tff(c_4727, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_4724])).
% 8.12/2.90  tff(c_4728, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_76, c_4727])).
% 8.12/2.90  tff(c_3986, plain, (![A_838, B_839, C_840, D_841]: (k2_partfun1(A_838, B_839, C_840, D_841)=k7_relat_1(C_840, D_841) | ~m1_subset_1(C_840, k1_zfmisc_1(k2_zfmisc_1(A_838, B_839))) | ~v1_funct_1(C_840))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.12/2.90  tff(c_3990, plain, (![D_841]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_841)=k7_relat_1('#skF_7', D_841) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_58, c_3986])).
% 8.12/2.90  tff(c_3996, plain, (![D_841]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_841)=k7_relat_1('#skF_7', D_841))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_3990])).
% 8.12/2.90  tff(c_3988, plain, (![D_841]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_841)=k7_relat_1('#skF_8', D_841) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_52, c_3986])).
% 8.12/2.90  tff(c_3993, plain, (![D_841]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_841)=k7_relat_1('#skF_8', D_841))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_3988])).
% 8.12/2.90  tff(c_46, plain, (![E_165, C_163, F_166, A_161, B_162, D_164]: (v1_funct_2(k1_tmap_1(A_161, B_162, C_163, D_164, E_165, F_166), k4_subset_1(A_161, C_163, D_164), B_162) | ~m1_subset_1(F_166, k1_zfmisc_1(k2_zfmisc_1(D_164, B_162))) | ~v1_funct_2(F_166, D_164, B_162) | ~v1_funct_1(F_166) | ~m1_subset_1(E_165, k1_zfmisc_1(k2_zfmisc_1(C_163, B_162))) | ~v1_funct_2(E_165, C_163, B_162) | ~v1_funct_1(E_165) | ~m1_subset_1(D_164, k1_zfmisc_1(A_161)) | v1_xboole_0(D_164) | ~m1_subset_1(C_163, k1_zfmisc_1(A_161)) | v1_xboole_0(C_163) | v1_xboole_0(B_162) | v1_xboole_0(A_161))), inference(cnfTransformation, [status(thm)], [f_180])).
% 8.12/2.90  tff(c_44, plain, (![E_165, C_163, F_166, A_161, B_162, D_164]: (m1_subset_1(k1_tmap_1(A_161, B_162, C_163, D_164, E_165, F_166), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_161, C_163, D_164), B_162))) | ~m1_subset_1(F_166, k1_zfmisc_1(k2_zfmisc_1(D_164, B_162))) | ~v1_funct_2(F_166, D_164, B_162) | ~v1_funct_1(F_166) | ~m1_subset_1(E_165, k1_zfmisc_1(k2_zfmisc_1(C_163, B_162))) | ~v1_funct_2(E_165, C_163, B_162) | ~v1_funct_1(E_165) | ~m1_subset_1(D_164, k1_zfmisc_1(A_161)) | v1_xboole_0(D_164) | ~m1_subset_1(C_163, k1_zfmisc_1(A_161)) | v1_xboole_0(C_163) | v1_xboole_0(B_162) | v1_xboole_0(A_161))), inference(cnfTransformation, [status(thm)], [f_180])).
% 8.12/2.90  tff(c_4446, plain, (![D_914, C_910, A_909, B_912, F_911, E_913]: (k2_partfun1(k4_subset_1(A_909, C_910, D_914), B_912, k1_tmap_1(A_909, B_912, C_910, D_914, E_913, F_911), C_910)=E_913 | ~m1_subset_1(k1_tmap_1(A_909, B_912, C_910, D_914, E_913, F_911), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_909, C_910, D_914), B_912))) | ~v1_funct_2(k1_tmap_1(A_909, B_912, C_910, D_914, E_913, F_911), k4_subset_1(A_909, C_910, D_914), B_912) | ~v1_funct_1(k1_tmap_1(A_909, B_912, C_910, D_914, E_913, F_911)) | k2_partfun1(D_914, B_912, F_911, k9_subset_1(A_909, C_910, D_914))!=k2_partfun1(C_910, B_912, E_913, k9_subset_1(A_909, C_910, D_914)) | ~m1_subset_1(F_911, k1_zfmisc_1(k2_zfmisc_1(D_914, B_912))) | ~v1_funct_2(F_911, D_914, B_912) | ~v1_funct_1(F_911) | ~m1_subset_1(E_913, k1_zfmisc_1(k2_zfmisc_1(C_910, B_912))) | ~v1_funct_2(E_913, C_910, B_912) | ~v1_funct_1(E_913) | ~m1_subset_1(D_914, k1_zfmisc_1(A_909)) | v1_xboole_0(D_914) | ~m1_subset_1(C_910, k1_zfmisc_1(A_909)) | v1_xboole_0(C_910) | v1_xboole_0(B_912) | v1_xboole_0(A_909))), inference(cnfTransformation, [status(thm)], [f_146])).
% 8.12/2.90  tff(c_5082, plain, (![B_1037, D_1038, C_1039, F_1042, E_1041, A_1040]: (k2_partfun1(k4_subset_1(A_1040, C_1039, D_1038), B_1037, k1_tmap_1(A_1040, B_1037, C_1039, D_1038, E_1041, F_1042), C_1039)=E_1041 | ~v1_funct_2(k1_tmap_1(A_1040, B_1037, C_1039, D_1038, E_1041, F_1042), k4_subset_1(A_1040, C_1039, D_1038), B_1037) | ~v1_funct_1(k1_tmap_1(A_1040, B_1037, C_1039, D_1038, E_1041, F_1042)) | k2_partfun1(D_1038, B_1037, F_1042, k9_subset_1(A_1040, C_1039, D_1038))!=k2_partfun1(C_1039, B_1037, E_1041, k9_subset_1(A_1040, C_1039, D_1038)) | ~m1_subset_1(F_1042, k1_zfmisc_1(k2_zfmisc_1(D_1038, B_1037))) | ~v1_funct_2(F_1042, D_1038, B_1037) | ~v1_funct_1(F_1042) | ~m1_subset_1(E_1041, k1_zfmisc_1(k2_zfmisc_1(C_1039, B_1037))) | ~v1_funct_2(E_1041, C_1039, B_1037) | ~v1_funct_1(E_1041) | ~m1_subset_1(D_1038, k1_zfmisc_1(A_1040)) | v1_xboole_0(D_1038) | ~m1_subset_1(C_1039, k1_zfmisc_1(A_1040)) | v1_xboole_0(C_1039) | v1_xboole_0(B_1037) | v1_xboole_0(A_1040))), inference(resolution, [status(thm)], [c_44, c_4446])).
% 8.12/2.90  tff(c_5611, plain, (![F_1109, B_1104, E_1108, D_1105, C_1106, A_1107]: (k2_partfun1(k4_subset_1(A_1107, C_1106, D_1105), B_1104, k1_tmap_1(A_1107, B_1104, C_1106, D_1105, E_1108, F_1109), C_1106)=E_1108 | ~v1_funct_1(k1_tmap_1(A_1107, B_1104, C_1106, D_1105, E_1108, F_1109)) | k2_partfun1(D_1105, B_1104, F_1109, k9_subset_1(A_1107, C_1106, D_1105))!=k2_partfun1(C_1106, B_1104, E_1108, k9_subset_1(A_1107, C_1106, D_1105)) | ~m1_subset_1(F_1109, k1_zfmisc_1(k2_zfmisc_1(D_1105, B_1104))) | ~v1_funct_2(F_1109, D_1105, B_1104) | ~v1_funct_1(F_1109) | ~m1_subset_1(E_1108, k1_zfmisc_1(k2_zfmisc_1(C_1106, B_1104))) | ~v1_funct_2(E_1108, C_1106, B_1104) | ~v1_funct_1(E_1108) | ~m1_subset_1(D_1105, k1_zfmisc_1(A_1107)) | v1_xboole_0(D_1105) | ~m1_subset_1(C_1106, k1_zfmisc_1(A_1107)) | v1_xboole_0(C_1106) | v1_xboole_0(B_1104) | v1_xboole_0(A_1107))), inference(resolution, [status(thm)], [c_46, c_5082])).
% 8.12/2.90  tff(c_5615, plain, (![A_1107, C_1106, E_1108]: (k2_partfun1(k4_subset_1(A_1107, C_1106, '#skF_6'), '#skF_4', k1_tmap_1(A_1107, '#skF_4', C_1106, '#skF_6', E_1108, '#skF_8'), C_1106)=E_1108 | ~v1_funct_1(k1_tmap_1(A_1107, '#skF_4', C_1106, '#skF_6', E_1108, '#skF_8')) | k2_partfun1(C_1106, '#skF_4', E_1108, k9_subset_1(A_1107, C_1106, '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1(A_1107, C_1106, '#skF_6')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_1108, k1_zfmisc_1(k2_zfmisc_1(C_1106, '#skF_4'))) | ~v1_funct_2(E_1108, C_1106, '#skF_4') | ~v1_funct_1(E_1108) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1107)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_1106, k1_zfmisc_1(A_1107)) | v1_xboole_0(C_1106) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1107))), inference(resolution, [status(thm)], [c_52, c_5611])).
% 8.12/2.90  tff(c_5621, plain, (![A_1107, C_1106, E_1108]: (k2_partfun1(k4_subset_1(A_1107, C_1106, '#skF_6'), '#skF_4', k1_tmap_1(A_1107, '#skF_4', C_1106, '#skF_6', E_1108, '#skF_8'), C_1106)=E_1108 | ~v1_funct_1(k1_tmap_1(A_1107, '#skF_4', C_1106, '#skF_6', E_1108, '#skF_8')) | k2_partfun1(C_1106, '#skF_4', E_1108, k9_subset_1(A_1107, C_1106, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_1107, C_1106, '#skF_6')) | ~m1_subset_1(E_1108, k1_zfmisc_1(k2_zfmisc_1(C_1106, '#skF_4'))) | ~v1_funct_2(E_1108, C_1106, '#skF_4') | ~v1_funct_1(E_1108) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1107)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_1106, k1_zfmisc_1(A_1107)) | v1_xboole_0(C_1106) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1107))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_3993, c_5615])).
% 8.12/2.90  tff(c_6421, plain, (![A_1209, C_1210, E_1211]: (k2_partfun1(k4_subset_1(A_1209, C_1210, '#skF_6'), '#skF_4', k1_tmap_1(A_1209, '#skF_4', C_1210, '#skF_6', E_1211, '#skF_8'), C_1210)=E_1211 | ~v1_funct_1(k1_tmap_1(A_1209, '#skF_4', C_1210, '#skF_6', E_1211, '#skF_8')) | k2_partfun1(C_1210, '#skF_4', E_1211, k9_subset_1(A_1209, C_1210, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_1209, C_1210, '#skF_6')) | ~m1_subset_1(E_1211, k1_zfmisc_1(k2_zfmisc_1(C_1210, '#skF_4'))) | ~v1_funct_2(E_1211, C_1210, '#skF_4') | ~v1_funct_1(E_1211) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1209)) | ~m1_subset_1(C_1210, k1_zfmisc_1(A_1209)) | v1_xboole_0(C_1210) | v1_xboole_0(A_1209))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_5621])).
% 8.12/2.90  tff(c_6428, plain, (![A_1209]: (k2_partfun1(k4_subset_1(A_1209, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_1209, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1209, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1(A_1209, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_1209, '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1209)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1209)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_1209))), inference(resolution, [status(thm)], [c_58, c_6421])).
% 8.12/2.90  tff(c_6438, plain, (![A_1209]: (k2_partfun1(k4_subset_1(A_1209, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_1209, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1209, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_1209, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_1209, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1209)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1209)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_1209))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_3996, c_6428])).
% 8.12/2.90  tff(c_6440, plain, (![A_1212]: (k2_partfun1(k4_subset_1(A_1212, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_1212, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1212, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_1212, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_1212, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1212)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1212)) | v1_xboole_0(A_1212))), inference(negUnitSimplification, [status(thm)], [c_72, c_6438])).
% 8.12/2.90  tff(c_1092, plain, (![C_405, A_406, B_407]: (v4_relat_1(C_405, A_406) | ~m1_subset_1(C_405, k1_zfmisc_1(k2_zfmisc_1(A_406, B_407))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.12/2.90  tff(c_1099, plain, (v4_relat_1('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_52, c_1092])).
% 8.12/2.90  tff(c_1111, plain, (![B_411, A_412]: (k7_relat_1(B_411, A_412)=B_411 | ~v4_relat_1(B_411, A_412) | ~v1_relat_1(B_411))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.12/2.90  tff(c_1117, plain, (k7_relat_1('#skF_8', '#skF_6')='#skF_8' | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_1099, c_1111])).
% 8.12/2.90  tff(c_1123, plain, (k7_relat_1('#skF_8', '#skF_6')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1060, c_1117])).
% 8.12/2.90  tff(c_1242, plain, (![C_433, A_434, B_435]: (k7_relat_1(k7_relat_1(C_433, A_434), B_435)=k1_xboole_0 | ~r1_xboole_0(A_434, B_435) | ~v1_relat_1(C_433))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.12/2.90  tff(c_1257, plain, (![B_435]: (k7_relat_1('#skF_8', B_435)=k1_xboole_0 | ~r1_xboole_0('#skF_6', B_435) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1123, c_1242])).
% 8.12/2.90  tff(c_1267, plain, (![B_436]: (k7_relat_1('#skF_8', B_436)=k1_xboole_0 | ~r1_xboole_0('#skF_6', B_436))), inference(demodulation, [status(thm), theory('equality')], [c_1060, c_1257])).
% 8.12/2.90  tff(c_1301, plain, (![B_441]: (k7_relat_1('#skF_8', B_441)=k1_xboole_0 | ~v1_xboole_0(B_441))), inference(resolution, [status(thm)], [c_1036, c_1267])).
% 8.12/2.90  tff(c_1305, plain, (k7_relat_1('#skF_8', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_1301])).
% 8.12/2.90  tff(c_1141, plain, (![A_416, B_417]: (r1_xboole_0(A_416, B_417) | ~r1_subset_1(A_416, B_417) | v1_xboole_0(B_417) | v1_xboole_0(A_416))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.12/2.90  tff(c_1542, plain, (![A_469, B_470]: (k3_xboole_0(A_469, B_470)=k1_xboole_0 | ~r1_subset_1(A_469, B_470) | v1_xboole_0(B_470) | v1_xboole_0(A_469))), inference(resolution, [status(thm)], [c_1141, c_6])).
% 8.12/2.90  tff(c_1548, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0 | v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_64, c_1542])).
% 8.12/2.90  tff(c_1552, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_72, c_68, c_1548])).
% 8.12/2.90  tff(c_1100, plain, (v4_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_58, c_1092])).
% 8.12/2.90  tff(c_1114, plain, (k7_relat_1('#skF_7', '#skF_5')='#skF_7' | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_1100, c_1111])).
% 8.12/2.90  tff(c_1120, plain, (k7_relat_1('#skF_7', '#skF_5')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_1061, c_1114])).
% 8.12/2.90  tff(c_1260, plain, (![B_435]: (k7_relat_1('#skF_7', B_435)=k1_xboole_0 | ~r1_xboole_0('#skF_5', B_435) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1120, c_1242])).
% 8.12/2.90  tff(c_1315, plain, (![B_442]: (k7_relat_1('#skF_7', B_442)=k1_xboole_0 | ~r1_xboole_0('#skF_5', B_442))), inference(demodulation, [status(thm), theory('equality')], [c_1061, c_1260])).
% 8.12/2.90  tff(c_1339, plain, (![B_444]: (k7_relat_1('#skF_7', B_444)=k1_xboole_0 | ~v1_xboole_0(B_444))), inference(resolution, [status(thm)], [c_1036, c_1315])).
% 8.12/2.90  tff(c_1343, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_1339])).
% 8.12/2.90  tff(c_1166, plain, (![A_420, B_421, C_422]: (k9_subset_1(A_420, B_421, C_422)=k3_xboole_0(B_421, C_422) | ~m1_subset_1(C_422, k1_zfmisc_1(A_420)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.12/2.90  tff(c_1177, plain, (![B_421]: (k9_subset_1('#skF_3', B_421, '#skF_6')=k3_xboole_0(B_421, '#skF_6'))), inference(resolution, [status(thm)], [c_66, c_1166])).
% 8.12/2.90  tff(c_1392, plain, (![F_452, A_450, D_448, B_447, E_451, C_449]: (v1_funct_1(k1_tmap_1(A_450, B_447, C_449, D_448, E_451, F_452)) | ~m1_subset_1(F_452, k1_zfmisc_1(k2_zfmisc_1(D_448, B_447))) | ~v1_funct_2(F_452, D_448, B_447) | ~v1_funct_1(F_452) | ~m1_subset_1(E_451, k1_zfmisc_1(k2_zfmisc_1(C_449, B_447))) | ~v1_funct_2(E_451, C_449, B_447) | ~v1_funct_1(E_451) | ~m1_subset_1(D_448, k1_zfmisc_1(A_450)) | v1_xboole_0(D_448) | ~m1_subset_1(C_449, k1_zfmisc_1(A_450)) | v1_xboole_0(C_449) | v1_xboole_0(B_447) | v1_xboole_0(A_450))), inference(cnfTransformation, [status(thm)], [f_180])).
% 8.12/2.90  tff(c_1394, plain, (![A_450, C_449, E_451]: (v1_funct_1(k1_tmap_1(A_450, '#skF_4', C_449, '#skF_6', E_451, '#skF_8')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_451, k1_zfmisc_1(k2_zfmisc_1(C_449, '#skF_4'))) | ~v1_funct_2(E_451, C_449, '#skF_4') | ~v1_funct_1(E_451) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_450)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_449, k1_zfmisc_1(A_450)) | v1_xboole_0(C_449) | v1_xboole_0('#skF_4') | v1_xboole_0(A_450))), inference(resolution, [status(thm)], [c_52, c_1392])).
% 8.12/2.90  tff(c_1399, plain, (![A_450, C_449, E_451]: (v1_funct_1(k1_tmap_1(A_450, '#skF_4', C_449, '#skF_6', E_451, '#skF_8')) | ~m1_subset_1(E_451, k1_zfmisc_1(k2_zfmisc_1(C_449, '#skF_4'))) | ~v1_funct_2(E_451, C_449, '#skF_4') | ~v1_funct_1(E_451) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_450)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_449, k1_zfmisc_1(A_450)) | v1_xboole_0(C_449) | v1_xboole_0('#skF_4') | v1_xboole_0(A_450))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_1394])).
% 8.12/2.90  tff(c_1857, plain, (![A_516, C_517, E_518]: (v1_funct_1(k1_tmap_1(A_516, '#skF_4', C_517, '#skF_6', E_518, '#skF_8')) | ~m1_subset_1(E_518, k1_zfmisc_1(k2_zfmisc_1(C_517, '#skF_4'))) | ~v1_funct_2(E_518, C_517, '#skF_4') | ~v1_funct_1(E_518) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_516)) | ~m1_subset_1(C_517, k1_zfmisc_1(A_516)) | v1_xboole_0(C_517) | v1_xboole_0(A_516))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_1399])).
% 8.12/2.90  tff(c_1864, plain, (![A_516]: (v1_funct_1(k1_tmap_1(A_516, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_516)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_516)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_516))), inference(resolution, [status(thm)], [c_58, c_1857])).
% 8.12/2.90  tff(c_1874, plain, (![A_516]: (v1_funct_1(k1_tmap_1(A_516, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_516)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_516)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_516))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1864])).
% 8.12/2.90  tff(c_2076, plain, (![A_554]: (v1_funct_1(k1_tmap_1(A_554, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_554)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_554)) | v1_xboole_0(A_554))), inference(negUnitSimplification, [status(thm)], [c_72, c_1874])).
% 8.12/2.90  tff(c_2079, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_70, c_2076])).
% 8.12/2.90  tff(c_2082, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2079])).
% 8.12/2.90  tff(c_2083, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_76, c_2082])).
% 8.12/2.90  tff(c_1290, plain, (![A_437, B_438, C_439, D_440]: (k2_partfun1(A_437, B_438, C_439, D_440)=k7_relat_1(C_439, D_440) | ~m1_subset_1(C_439, k1_zfmisc_1(k2_zfmisc_1(A_437, B_438))) | ~v1_funct_1(C_439))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.12/2.90  tff(c_1294, plain, (![D_440]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_440)=k7_relat_1('#skF_7', D_440) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_58, c_1290])).
% 8.12/2.90  tff(c_1300, plain, (![D_440]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_440)=k7_relat_1('#skF_7', D_440))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1294])).
% 8.12/2.90  tff(c_1292, plain, (![D_440]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_440)=k7_relat_1('#skF_8', D_440) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_52, c_1290])).
% 8.12/2.90  tff(c_1297, plain, (![D_440]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_440)=k7_relat_1('#skF_8', D_440))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1292])).
% 8.12/2.90  tff(c_1838, plain, (![B_508, C_506, A_505, E_509, D_510, F_507]: (k2_partfun1(k4_subset_1(A_505, C_506, D_510), B_508, k1_tmap_1(A_505, B_508, C_506, D_510, E_509, F_507), D_510)=F_507 | ~m1_subset_1(k1_tmap_1(A_505, B_508, C_506, D_510, E_509, F_507), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_505, C_506, D_510), B_508))) | ~v1_funct_2(k1_tmap_1(A_505, B_508, C_506, D_510, E_509, F_507), k4_subset_1(A_505, C_506, D_510), B_508) | ~v1_funct_1(k1_tmap_1(A_505, B_508, C_506, D_510, E_509, F_507)) | k2_partfun1(D_510, B_508, F_507, k9_subset_1(A_505, C_506, D_510))!=k2_partfun1(C_506, B_508, E_509, k9_subset_1(A_505, C_506, D_510)) | ~m1_subset_1(F_507, k1_zfmisc_1(k2_zfmisc_1(D_510, B_508))) | ~v1_funct_2(F_507, D_510, B_508) | ~v1_funct_1(F_507) | ~m1_subset_1(E_509, k1_zfmisc_1(k2_zfmisc_1(C_506, B_508))) | ~v1_funct_2(E_509, C_506, B_508) | ~v1_funct_1(E_509) | ~m1_subset_1(D_510, k1_zfmisc_1(A_505)) | v1_xboole_0(D_510) | ~m1_subset_1(C_506, k1_zfmisc_1(A_505)) | v1_xboole_0(C_506) | v1_xboole_0(B_508) | v1_xboole_0(A_505))), inference(cnfTransformation, [status(thm)], [f_146])).
% 8.12/2.90  tff(c_2669, plain, (![E_673, D_670, B_669, F_674, A_672, C_671]: (k2_partfun1(k4_subset_1(A_672, C_671, D_670), B_669, k1_tmap_1(A_672, B_669, C_671, D_670, E_673, F_674), D_670)=F_674 | ~v1_funct_2(k1_tmap_1(A_672, B_669, C_671, D_670, E_673, F_674), k4_subset_1(A_672, C_671, D_670), B_669) | ~v1_funct_1(k1_tmap_1(A_672, B_669, C_671, D_670, E_673, F_674)) | k2_partfun1(D_670, B_669, F_674, k9_subset_1(A_672, C_671, D_670))!=k2_partfun1(C_671, B_669, E_673, k9_subset_1(A_672, C_671, D_670)) | ~m1_subset_1(F_674, k1_zfmisc_1(k2_zfmisc_1(D_670, B_669))) | ~v1_funct_2(F_674, D_670, B_669) | ~v1_funct_1(F_674) | ~m1_subset_1(E_673, k1_zfmisc_1(k2_zfmisc_1(C_671, B_669))) | ~v1_funct_2(E_673, C_671, B_669) | ~v1_funct_1(E_673) | ~m1_subset_1(D_670, k1_zfmisc_1(A_672)) | v1_xboole_0(D_670) | ~m1_subset_1(C_671, k1_zfmisc_1(A_672)) | v1_xboole_0(C_671) | v1_xboole_0(B_669) | v1_xboole_0(A_672))), inference(resolution, [status(thm)], [c_44, c_1838])).
% 8.12/2.90  tff(c_3215, plain, (![F_744, C_741, B_739, E_743, D_740, A_742]: (k2_partfun1(k4_subset_1(A_742, C_741, D_740), B_739, k1_tmap_1(A_742, B_739, C_741, D_740, E_743, F_744), D_740)=F_744 | ~v1_funct_1(k1_tmap_1(A_742, B_739, C_741, D_740, E_743, F_744)) | k2_partfun1(D_740, B_739, F_744, k9_subset_1(A_742, C_741, D_740))!=k2_partfun1(C_741, B_739, E_743, k9_subset_1(A_742, C_741, D_740)) | ~m1_subset_1(F_744, k1_zfmisc_1(k2_zfmisc_1(D_740, B_739))) | ~v1_funct_2(F_744, D_740, B_739) | ~v1_funct_1(F_744) | ~m1_subset_1(E_743, k1_zfmisc_1(k2_zfmisc_1(C_741, B_739))) | ~v1_funct_2(E_743, C_741, B_739) | ~v1_funct_1(E_743) | ~m1_subset_1(D_740, k1_zfmisc_1(A_742)) | v1_xboole_0(D_740) | ~m1_subset_1(C_741, k1_zfmisc_1(A_742)) | v1_xboole_0(C_741) | v1_xboole_0(B_739) | v1_xboole_0(A_742))), inference(resolution, [status(thm)], [c_46, c_2669])).
% 8.12/2.90  tff(c_3219, plain, (![A_742, C_741, E_743]: (k2_partfun1(k4_subset_1(A_742, C_741, '#skF_6'), '#skF_4', k1_tmap_1(A_742, '#skF_4', C_741, '#skF_6', E_743, '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_742, '#skF_4', C_741, '#skF_6', E_743, '#skF_8')) | k2_partfun1(C_741, '#skF_4', E_743, k9_subset_1(A_742, C_741, '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1(A_742, C_741, '#skF_6')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_743, k1_zfmisc_1(k2_zfmisc_1(C_741, '#skF_4'))) | ~v1_funct_2(E_743, C_741, '#skF_4') | ~v1_funct_1(E_743) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_742)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_741, k1_zfmisc_1(A_742)) | v1_xboole_0(C_741) | v1_xboole_0('#skF_4') | v1_xboole_0(A_742))), inference(resolution, [status(thm)], [c_52, c_3215])).
% 8.12/2.90  tff(c_3225, plain, (![A_742, C_741, E_743]: (k2_partfun1(k4_subset_1(A_742, C_741, '#skF_6'), '#skF_4', k1_tmap_1(A_742, '#skF_4', C_741, '#skF_6', E_743, '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_742, '#skF_4', C_741, '#skF_6', E_743, '#skF_8')) | k2_partfun1(C_741, '#skF_4', E_743, k9_subset_1(A_742, C_741, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_742, C_741, '#skF_6')) | ~m1_subset_1(E_743, k1_zfmisc_1(k2_zfmisc_1(C_741, '#skF_4'))) | ~v1_funct_2(E_743, C_741, '#skF_4') | ~v1_funct_1(E_743) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_742)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_741, k1_zfmisc_1(A_742)) | v1_xboole_0(C_741) | v1_xboole_0('#skF_4') | v1_xboole_0(A_742))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_1297, c_3219])).
% 8.12/2.90  tff(c_3433, plain, (![A_777, C_778, E_779]: (k2_partfun1(k4_subset_1(A_777, C_778, '#skF_6'), '#skF_4', k1_tmap_1(A_777, '#skF_4', C_778, '#skF_6', E_779, '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_777, '#skF_4', C_778, '#skF_6', E_779, '#skF_8')) | k2_partfun1(C_778, '#skF_4', E_779, k9_subset_1(A_777, C_778, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_777, C_778, '#skF_6')) | ~m1_subset_1(E_779, k1_zfmisc_1(k2_zfmisc_1(C_778, '#skF_4'))) | ~v1_funct_2(E_779, C_778, '#skF_4') | ~v1_funct_1(E_779) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_777)) | ~m1_subset_1(C_778, k1_zfmisc_1(A_777)) | v1_xboole_0(C_778) | v1_xboole_0(A_777))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_3225])).
% 8.12/2.90  tff(c_3440, plain, (![A_777]: (k2_partfun1(k4_subset_1(A_777, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_777, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_777, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1(A_777, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_777, '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_777)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_777)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_777))), inference(resolution, [status(thm)], [c_58, c_3433])).
% 8.12/2.90  tff(c_3450, plain, (![A_777]: (k2_partfun1(k4_subset_1(A_777, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_777, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_777, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_777, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_777, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_777)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_777)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_777))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1300, c_3440])).
% 8.12/2.90  tff(c_3568, plain, (![A_796]: (k2_partfun1(k4_subset_1(A_796, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_796, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_796, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_796, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_796, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_796)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_796)) | v1_xboole_0(A_796))), inference(negUnitSimplification, [status(thm)], [c_72, c_3450])).
% 8.12/2.90  tff(c_99, plain, (![A_233, B_234]: (r2_hidden('#skF_2'(A_233, B_234), B_234) | r1_xboole_0(A_233, B_234))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.12/2.90  tff(c_103, plain, (![B_234, A_233]: (~v1_xboole_0(B_234) | r1_xboole_0(A_233, B_234))), inference(resolution, [status(thm)], [c_99, c_2])).
% 8.12/2.90  tff(c_125, plain, (![C_242, A_243, B_244]: (v1_relat_1(C_242) | ~m1_subset_1(C_242, k1_zfmisc_1(k2_zfmisc_1(A_243, B_244))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.12/2.90  tff(c_132, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_52, c_125])).
% 8.12/2.90  tff(c_158, plain, (![C_250, A_251, B_252]: (v4_relat_1(C_250, A_251) | ~m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(A_251, B_252))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.12/2.90  tff(c_165, plain, (v4_relat_1('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_52, c_158])).
% 8.12/2.90  tff(c_167, plain, (![B_253, A_254]: (k7_relat_1(B_253, A_254)=B_253 | ~v4_relat_1(B_253, A_254) | ~v1_relat_1(B_253))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.12/2.90  tff(c_173, plain, (k7_relat_1('#skF_8', '#skF_6')='#skF_8' | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_165, c_167])).
% 8.12/2.90  tff(c_179, plain, (k7_relat_1('#skF_8', '#skF_6')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_132, c_173])).
% 8.12/2.90  tff(c_308, plain, (![C_278, A_279, B_280]: (k7_relat_1(k7_relat_1(C_278, A_279), B_280)=k1_xboole_0 | ~r1_xboole_0(A_279, B_280) | ~v1_relat_1(C_278))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.12/2.90  tff(c_323, plain, (![B_280]: (k7_relat_1('#skF_8', B_280)=k1_xboole_0 | ~r1_xboole_0('#skF_6', B_280) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_179, c_308])).
% 8.12/2.90  tff(c_333, plain, (![B_281]: (k7_relat_1('#skF_8', B_281)=k1_xboole_0 | ~r1_xboole_0('#skF_6', B_281))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_323])).
% 8.12/2.90  tff(c_356, plain, (![B_282]: (k7_relat_1('#skF_8', B_282)=k1_xboole_0 | ~v1_xboole_0(B_282))), inference(resolution, [status(thm)], [c_103, c_333])).
% 8.12/2.90  tff(c_360, plain, (k7_relat_1('#skF_8', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_356])).
% 8.12/2.90  tff(c_220, plain, (![A_263, B_264]: (r1_xboole_0(A_263, B_264) | ~r1_subset_1(A_263, B_264) | v1_xboole_0(B_264) | v1_xboole_0(A_263))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.12/2.90  tff(c_608, plain, (![A_314, B_315]: (k3_xboole_0(A_314, B_315)=k1_xboole_0 | ~r1_subset_1(A_314, B_315) | v1_xboole_0(B_315) | v1_xboole_0(A_314))), inference(resolution, [status(thm)], [c_220, c_6])).
% 8.12/2.90  tff(c_614, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0 | v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_64, c_608])).
% 8.12/2.90  tff(c_618, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_72, c_68, c_614])).
% 8.12/2.90  tff(c_133, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_58, c_125])).
% 8.12/2.90  tff(c_166, plain, (v4_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_58, c_158])).
% 8.12/2.90  tff(c_170, plain, (k7_relat_1('#skF_7', '#skF_5')='#skF_7' | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_166, c_167])).
% 8.12/2.90  tff(c_176, plain, (k7_relat_1('#skF_7', '#skF_5')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_133, c_170])).
% 8.12/2.90  tff(c_326, plain, (![B_280]: (k7_relat_1('#skF_7', B_280)=k1_xboole_0 | ~r1_xboole_0('#skF_5', B_280) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_176, c_308])).
% 8.12/2.90  tff(c_381, plain, (![B_287]: (k7_relat_1('#skF_7', B_287)=k1_xboole_0 | ~r1_xboole_0('#skF_5', B_287))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_326])).
% 8.12/2.90  tff(c_404, plain, (![B_288]: (k7_relat_1('#skF_7', B_288)=k1_xboole_0 | ~v1_xboole_0(B_288))), inference(resolution, [status(thm)], [c_103, c_381])).
% 8.12/2.90  tff(c_408, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_404])).
% 8.12/2.90  tff(c_361, plain, (![A_283, B_284, C_285, D_286]: (k2_partfun1(A_283, B_284, C_285, D_286)=k7_relat_1(C_285, D_286) | ~m1_subset_1(C_285, k1_zfmisc_1(k2_zfmisc_1(A_283, B_284))) | ~v1_funct_1(C_285))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.12/2.90  tff(c_363, plain, (![D_286]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_286)=k7_relat_1('#skF_8', D_286) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_52, c_361])).
% 8.12/2.90  tff(c_368, plain, (![D_286]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_286)=k7_relat_1('#skF_8', D_286))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_363])).
% 8.12/2.90  tff(c_365, plain, (![D_286]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_286)=k7_relat_1('#skF_7', D_286) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_58, c_361])).
% 8.12/2.90  tff(c_371, plain, (![D_286]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_286)=k7_relat_1('#skF_7', D_286))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_365])).
% 8.12/2.90  tff(c_242, plain, (![A_268, B_269, C_270]: (k9_subset_1(A_268, B_269, C_270)=k3_xboole_0(B_269, C_270) | ~m1_subset_1(C_270, k1_zfmisc_1(A_268)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.12/2.90  tff(c_253, plain, (![B_269]: (k9_subset_1('#skF_3', B_269, '#skF_6')=k3_xboole_0(B_269, '#skF_6'))), inference(resolution, [status(thm)], [c_66, c_242])).
% 8.12/2.90  tff(c_50, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')!='#skF_8' | k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')!='#skF_7' | k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_222])).
% 8.12/2.90  tff(c_98, plain, (k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_50])).
% 8.12/2.90  tff(c_255, plain, (k2_partfun1('#skF_5', '#skF_4', '#skF_7', k3_xboole_0('#skF_5', '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k3_xboole_0('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_253, c_253, c_98])).
% 8.12/2.90  tff(c_1025, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_360, c_618, c_408, c_618, c_368, c_371, c_255])).
% 8.12/2.90  tff(c_1026, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')!='#skF_7' | k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')!='#skF_8'), inference(splitRight, [status(thm)], [c_50])).
% 8.12/2.90  tff(c_1072, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')!='#skF_8'), inference(splitLeft, [status(thm)], [c_1026])).
% 8.12/2.90  tff(c_3579, plain, (~v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3568, c_1072])).
% 8.12/2.90  tff(c_3593, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_1305, c_1552, c_1343, c_1552, c_1177, c_1177, c_2083, c_3579])).
% 8.12/2.90  tff(c_3595, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_3593])).
% 8.12/2.90  tff(c_3596, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_1026])).
% 8.12/2.90  tff(c_6449, plain, (~v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6440, c_3596])).
% 8.12/2.90  tff(c_6460, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_3743, c_4053, c_3781, c_4053, c_3840, c_3840, c_4728, c_6449])).
% 8.12/2.90  tff(c_6462, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_6460])).
% 8.12/2.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.12/2.90  
% 8.12/2.90  Inference rules
% 8.12/2.90  ----------------------
% 8.12/2.90  #Ref     : 0
% 8.12/2.90  #Sup     : 1299
% 8.12/2.90  #Fact    : 0
% 8.12/2.90  #Define  : 0
% 8.12/2.90  #Split   : 33
% 8.12/2.90  #Chain   : 0
% 8.12/2.90  #Close   : 0
% 8.12/2.90  
% 8.12/2.90  Ordering : KBO
% 8.12/2.90  
% 8.12/2.90  Simplification rules
% 8.12/2.90  ----------------------
% 8.12/2.90  #Subsume      : 205
% 8.12/2.90  #Demod        : 761
% 8.12/2.90  #Tautology    : 566
% 8.12/2.90  #SimpNegUnit  : 288
% 8.12/2.90  #BackRed      : 4
% 8.12/2.90  
% 8.12/2.90  #Partial instantiations: 0
% 8.12/2.90  #Strategies tried      : 1
% 8.12/2.90  
% 8.12/2.90  Timing (in seconds)
% 8.12/2.90  ----------------------
% 8.12/2.91  Preprocessing        : 0.42
% 8.12/2.91  Parsing              : 0.21
% 8.12/2.91  CNF conversion       : 0.06
% 8.12/2.91  Main loop            : 1.69
% 8.12/2.91  Inferencing          : 0.61
% 8.12/2.91  Reduction            : 0.55
% 8.12/2.91  Demodulation         : 0.39
% 8.12/2.91  BG Simplification    : 0.06
% 8.12/2.91  Subsumption          : 0.36
% 8.12/2.91  Abstraction          : 0.07
% 8.12/2.91  MUC search           : 0.00
% 8.12/2.91  Cooper               : 0.00
% 8.12/2.91  Total                : 2.18
% 8.12/2.91  Index Insertion      : 0.00
% 8.12/2.91  Index Deletion       : 0.00
% 8.12/2.91  Index Matching       : 0.00
% 8.12/2.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
