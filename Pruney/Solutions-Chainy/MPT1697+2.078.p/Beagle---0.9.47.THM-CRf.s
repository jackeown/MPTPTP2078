%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:21 EST 2020

% Result     : Theorem 7.45s
% Output     : CNFRefutation 7.77s
% Verified   : 
% Statistics : Number of formulae       :  221 ( 581 expanded)
%              Number of leaves         :   47 ( 229 expanded)
%              Depth                    :   12
%              Number of atoms          :  698 (2942 expanded)
%              Number of equality atoms :  131 ( 510 expanded)
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

tff(f_234,negated_conjecture,(
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

tff(f_76,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_98,axiom,(
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

tff(f_192,axiom,(
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

tff(f_110,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_158,axiom,(
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

tff(c_80,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_74,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_70,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_10,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3650,plain,(
    ! [A_784,B_785] :
      ( r2_hidden('#skF_2'(A_784,B_785),B_785)
      | r1_xboole_0(A_784,B_785) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3654,plain,(
    ! [B_785,A_784] :
      ( ~ v1_xboole_0(B_785)
      | r1_xboole_0(A_784,B_785) ) ),
    inference(resolution,[status(thm)],[c_3650,c_2])).

tff(c_26,plain,(
    ! [A_23,B_24] : v1_relat_1(k2_zfmisc_1(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_56,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_3628,plain,(
    ! [B_782,A_783] :
      ( v1_relat_1(B_782)
      | ~ m1_subset_1(B_782,k1_zfmisc_1(A_783))
      | ~ v1_relat_1(A_783) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_3631,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_4')) ),
    inference(resolution,[status(thm)],[c_56,c_3628])).

tff(c_3643,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_3631])).

tff(c_3703,plain,(
    ! [C_799,A_800,B_801] :
      ( v4_relat_1(C_799,A_800)
      | ~ m1_subset_1(C_799,k1_zfmisc_1(k2_zfmisc_1(A_800,B_801))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_3710,plain,(
    v4_relat_1('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_3703])).

tff(c_30,plain,(
    ! [B_29,A_28] :
      ( k7_relat_1(B_29,A_28) = B_29
      | ~ v4_relat_1(B_29,A_28)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_3714,plain,
    ( k7_relat_1('#skF_8','#skF_6') = '#skF_8'
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_3710,c_30])).

tff(c_3717,plain,(
    k7_relat_1('#skF_8','#skF_6') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3643,c_3714])).

tff(c_3767,plain,(
    ! [C_809,A_810,B_811] :
      ( k7_relat_1(k7_relat_1(C_809,A_810),B_811) = k1_xboole_0
      | ~ r1_xboole_0(A_810,B_811)
      | ~ v1_relat_1(C_809) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_3785,plain,(
    ! [B_811] :
      ( k7_relat_1('#skF_8',B_811) = k1_xboole_0
      | ~ r1_xboole_0('#skF_6',B_811)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3717,c_3767])).

tff(c_3845,plain,(
    ! [B_815] :
      ( k7_relat_1('#skF_8',B_815) = k1_xboole_0
      | ~ r1_xboole_0('#skF_6',B_815) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3643,c_3785])).

tff(c_3868,plain,(
    ! [B_816] :
      ( k7_relat_1('#skF_8',B_816) = k1_xboole_0
      | ~ v1_xboole_0(B_816) ) ),
    inference(resolution,[status(thm)],[c_3654,c_3845])).

tff(c_3872,plain,(
    k7_relat_1('#skF_8',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_3868])).

tff(c_76,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_72,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_68,plain,(
    r1_subset_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_3732,plain,(
    ! [A_802,B_803] :
      ( r1_xboole_0(A_802,B_803)
      | ~ r1_subset_1(A_802,B_803)
      | v1_xboole_0(B_803)
      | v1_xboole_0(A_802) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4110,plain,(
    ! [A_838,B_839] :
      ( k3_xboole_0(A_838,B_839) = k1_xboole_0
      | ~ r1_subset_1(A_838,B_839)
      | v1_xboole_0(B_839)
      | v1_xboole_0(A_838) ) ),
    inference(resolution,[status(thm)],[c_3732,c_6])).

tff(c_4113,plain,
    ( k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0
    | v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_4110])).

tff(c_4116,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_72,c_4113])).

tff(c_62,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_3634,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_62,c_3628])).

tff(c_3646,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_3634])).

tff(c_3711,plain,(
    v4_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_3703])).

tff(c_3720,plain,
    ( k7_relat_1('#skF_7','#skF_5') = '#skF_7'
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_3711,c_30])).

tff(c_3723,plain,(
    k7_relat_1('#skF_7','#skF_5') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3646,c_3720])).

tff(c_3782,plain,(
    ! [B_811] :
      ( k7_relat_1('#skF_7',B_811) = k1_xboole_0
      | ~ r1_xboole_0('#skF_5',B_811)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3723,c_3767])).

tff(c_3792,plain,(
    ! [B_812] :
      ( k7_relat_1('#skF_7',B_812) = k1_xboole_0
      | ~ r1_xboole_0('#skF_5',B_812) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3646,c_3782])).

tff(c_3815,plain,(
    ! [B_813] :
      ( k7_relat_1('#skF_7',B_813) = k1_xboole_0
      | ~ v1_xboole_0(B_813) ) ),
    inference(resolution,[status(thm)],[c_3654,c_3792])).

tff(c_3819,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_3815])).

tff(c_3908,plain,(
    ! [A_818,B_819,C_820] :
      ( k9_subset_1(A_818,B_819,C_820) = k3_xboole_0(B_819,C_820)
      | ~ m1_subset_1(C_820,k1_zfmisc_1(A_818)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_3919,plain,(
    ! [B_819] : k9_subset_1('#skF_3',B_819,'#skF_6') = k3_xboole_0(B_819,'#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_3908])).

tff(c_66,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_64,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_78,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_60,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_58,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_4149,plain,(
    ! [D_847,A_850,B_845,E_849,F_846,C_848] :
      ( v1_funct_1(k1_tmap_1(A_850,B_845,C_848,D_847,E_849,F_846))
      | ~ m1_subset_1(F_846,k1_zfmisc_1(k2_zfmisc_1(D_847,B_845)))
      | ~ v1_funct_2(F_846,D_847,B_845)
      | ~ v1_funct_1(F_846)
      | ~ m1_subset_1(E_849,k1_zfmisc_1(k2_zfmisc_1(C_848,B_845)))
      | ~ v1_funct_2(E_849,C_848,B_845)
      | ~ v1_funct_1(E_849)
      | ~ m1_subset_1(D_847,k1_zfmisc_1(A_850))
      | v1_xboole_0(D_847)
      | ~ m1_subset_1(C_848,k1_zfmisc_1(A_850))
      | v1_xboole_0(C_848)
      | v1_xboole_0(B_845)
      | v1_xboole_0(A_850) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_4151,plain,(
    ! [A_850,C_848,E_849] :
      ( v1_funct_1(k1_tmap_1(A_850,'#skF_4',C_848,'#skF_6',E_849,'#skF_8'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_849,k1_zfmisc_1(k2_zfmisc_1(C_848,'#skF_4')))
      | ~ v1_funct_2(E_849,C_848,'#skF_4')
      | ~ v1_funct_1(E_849)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_850))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_848,k1_zfmisc_1(A_850))
      | v1_xboole_0(C_848)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_850) ) ),
    inference(resolution,[status(thm)],[c_56,c_4149])).

tff(c_4156,plain,(
    ! [A_850,C_848,E_849] :
      ( v1_funct_1(k1_tmap_1(A_850,'#skF_4',C_848,'#skF_6',E_849,'#skF_8'))
      | ~ m1_subset_1(E_849,k1_zfmisc_1(k2_zfmisc_1(C_848,'#skF_4')))
      | ~ v1_funct_2(E_849,C_848,'#skF_4')
      | ~ v1_funct_1(E_849)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_850))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_848,k1_zfmisc_1(A_850))
      | v1_xboole_0(C_848)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_850) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_4151])).

tff(c_4547,plain,(
    ! [A_914,C_915,E_916] :
      ( v1_funct_1(k1_tmap_1(A_914,'#skF_4',C_915,'#skF_6',E_916,'#skF_8'))
      | ~ m1_subset_1(E_916,k1_zfmisc_1(k2_zfmisc_1(C_915,'#skF_4')))
      | ~ v1_funct_2(E_916,C_915,'#skF_4')
      | ~ v1_funct_1(E_916)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_914))
      | ~ m1_subset_1(C_915,k1_zfmisc_1(A_914))
      | v1_xboole_0(C_915)
      | v1_xboole_0(A_914) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_72,c_4156])).

tff(c_4554,plain,(
    ! [A_914] :
      ( v1_funct_1(k1_tmap_1(A_914,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_914))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_914))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_914) ) ),
    inference(resolution,[status(thm)],[c_62,c_4547])).

tff(c_4564,plain,(
    ! [A_914] :
      ( v1_funct_1(k1_tmap_1(A_914,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_914))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_914))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_914) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_4554])).

tff(c_4794,plain,(
    ! [A_955] :
      ( v1_funct_1(k1_tmap_1(A_955,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_955))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_955))
      | v1_xboole_0(A_955) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_4564])).

tff(c_4797,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_4794])).

tff(c_4800,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_4797])).

tff(c_4801,plain,(
    v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_4800])).

tff(c_4049,plain,(
    ! [A_829,B_830,C_831,D_832] :
      ( k2_partfun1(A_829,B_830,C_831,D_832) = k7_relat_1(C_831,D_832)
      | ~ m1_subset_1(C_831,k1_zfmisc_1(k2_zfmisc_1(A_829,B_830)))
      | ~ v1_funct_1(C_831) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_4053,plain,(
    ! [D_832] :
      ( k2_partfun1('#skF_5','#skF_4','#skF_7',D_832) = k7_relat_1('#skF_7',D_832)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_62,c_4049])).

tff(c_4059,plain,(
    ! [D_832] : k2_partfun1('#skF_5','#skF_4','#skF_7',D_832) = k7_relat_1('#skF_7',D_832) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_4053])).

tff(c_4051,plain,(
    ! [D_832] :
      ( k2_partfun1('#skF_6','#skF_4','#skF_8',D_832) = k7_relat_1('#skF_8',D_832)
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_56,c_4049])).

tff(c_4056,plain,(
    ! [D_832] : k2_partfun1('#skF_6','#skF_4','#skF_8',D_832) = k7_relat_1('#skF_8',D_832) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_4051])).

tff(c_50,plain,(
    ! [D_169,E_170,A_166,B_167,C_168,F_171] :
      ( v1_funct_2(k1_tmap_1(A_166,B_167,C_168,D_169,E_170,F_171),k4_subset_1(A_166,C_168,D_169),B_167)
      | ~ m1_subset_1(F_171,k1_zfmisc_1(k2_zfmisc_1(D_169,B_167)))
      | ~ v1_funct_2(F_171,D_169,B_167)
      | ~ v1_funct_1(F_171)
      | ~ m1_subset_1(E_170,k1_zfmisc_1(k2_zfmisc_1(C_168,B_167)))
      | ~ v1_funct_2(E_170,C_168,B_167)
      | ~ v1_funct_1(E_170)
      | ~ m1_subset_1(D_169,k1_zfmisc_1(A_166))
      | v1_xboole_0(D_169)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(A_166))
      | v1_xboole_0(C_168)
      | v1_xboole_0(B_167)
      | v1_xboole_0(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_48,plain,(
    ! [D_169,E_170,A_166,B_167,C_168,F_171] :
      ( m1_subset_1(k1_tmap_1(A_166,B_167,C_168,D_169,E_170,F_171),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_166,C_168,D_169),B_167)))
      | ~ m1_subset_1(F_171,k1_zfmisc_1(k2_zfmisc_1(D_169,B_167)))
      | ~ v1_funct_2(F_171,D_169,B_167)
      | ~ v1_funct_1(F_171)
      | ~ m1_subset_1(E_170,k1_zfmisc_1(k2_zfmisc_1(C_168,B_167)))
      | ~ v1_funct_2(E_170,C_168,B_167)
      | ~ v1_funct_1(E_170)
      | ~ m1_subset_1(D_169,k1_zfmisc_1(A_166))
      | v1_xboole_0(D_169)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(A_166))
      | v1_xboole_0(C_168)
      | v1_xboole_0(B_167)
      | v1_xboole_0(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_4519,plain,(
    ! [F_903,D_901,B_905,A_900,E_902,C_904] :
      ( k2_partfun1(k4_subset_1(A_900,C_904,D_901),B_905,k1_tmap_1(A_900,B_905,C_904,D_901,E_902,F_903),C_904) = E_902
      | ~ m1_subset_1(k1_tmap_1(A_900,B_905,C_904,D_901,E_902,F_903),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_900,C_904,D_901),B_905)))
      | ~ v1_funct_2(k1_tmap_1(A_900,B_905,C_904,D_901,E_902,F_903),k4_subset_1(A_900,C_904,D_901),B_905)
      | ~ v1_funct_1(k1_tmap_1(A_900,B_905,C_904,D_901,E_902,F_903))
      | k2_partfun1(D_901,B_905,F_903,k9_subset_1(A_900,C_904,D_901)) != k2_partfun1(C_904,B_905,E_902,k9_subset_1(A_900,C_904,D_901))
      | ~ m1_subset_1(F_903,k1_zfmisc_1(k2_zfmisc_1(D_901,B_905)))
      | ~ v1_funct_2(F_903,D_901,B_905)
      | ~ v1_funct_1(F_903)
      | ~ m1_subset_1(E_902,k1_zfmisc_1(k2_zfmisc_1(C_904,B_905)))
      | ~ v1_funct_2(E_902,C_904,B_905)
      | ~ v1_funct_1(E_902)
      | ~ m1_subset_1(D_901,k1_zfmisc_1(A_900))
      | v1_xboole_0(D_901)
      | ~ m1_subset_1(C_904,k1_zfmisc_1(A_900))
      | v1_xboole_0(C_904)
      | v1_xboole_0(B_905)
      | v1_xboole_0(A_900) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_5247,plain,(
    ! [A_1052,D_1049,C_1050,E_1051,F_1048,B_1047] :
      ( k2_partfun1(k4_subset_1(A_1052,C_1050,D_1049),B_1047,k1_tmap_1(A_1052,B_1047,C_1050,D_1049,E_1051,F_1048),C_1050) = E_1051
      | ~ v1_funct_2(k1_tmap_1(A_1052,B_1047,C_1050,D_1049,E_1051,F_1048),k4_subset_1(A_1052,C_1050,D_1049),B_1047)
      | ~ v1_funct_1(k1_tmap_1(A_1052,B_1047,C_1050,D_1049,E_1051,F_1048))
      | k2_partfun1(D_1049,B_1047,F_1048,k9_subset_1(A_1052,C_1050,D_1049)) != k2_partfun1(C_1050,B_1047,E_1051,k9_subset_1(A_1052,C_1050,D_1049))
      | ~ m1_subset_1(F_1048,k1_zfmisc_1(k2_zfmisc_1(D_1049,B_1047)))
      | ~ v1_funct_2(F_1048,D_1049,B_1047)
      | ~ v1_funct_1(F_1048)
      | ~ m1_subset_1(E_1051,k1_zfmisc_1(k2_zfmisc_1(C_1050,B_1047)))
      | ~ v1_funct_2(E_1051,C_1050,B_1047)
      | ~ v1_funct_1(E_1051)
      | ~ m1_subset_1(D_1049,k1_zfmisc_1(A_1052))
      | v1_xboole_0(D_1049)
      | ~ m1_subset_1(C_1050,k1_zfmisc_1(A_1052))
      | v1_xboole_0(C_1050)
      | v1_xboole_0(B_1047)
      | v1_xboole_0(A_1052) ) ),
    inference(resolution,[status(thm)],[c_48,c_4519])).

tff(c_5646,plain,(
    ! [E_1101,B_1097,A_1102,C_1100,F_1098,D_1099] :
      ( k2_partfun1(k4_subset_1(A_1102,C_1100,D_1099),B_1097,k1_tmap_1(A_1102,B_1097,C_1100,D_1099,E_1101,F_1098),C_1100) = E_1101
      | ~ v1_funct_1(k1_tmap_1(A_1102,B_1097,C_1100,D_1099,E_1101,F_1098))
      | k2_partfun1(D_1099,B_1097,F_1098,k9_subset_1(A_1102,C_1100,D_1099)) != k2_partfun1(C_1100,B_1097,E_1101,k9_subset_1(A_1102,C_1100,D_1099))
      | ~ m1_subset_1(F_1098,k1_zfmisc_1(k2_zfmisc_1(D_1099,B_1097)))
      | ~ v1_funct_2(F_1098,D_1099,B_1097)
      | ~ v1_funct_1(F_1098)
      | ~ m1_subset_1(E_1101,k1_zfmisc_1(k2_zfmisc_1(C_1100,B_1097)))
      | ~ v1_funct_2(E_1101,C_1100,B_1097)
      | ~ v1_funct_1(E_1101)
      | ~ m1_subset_1(D_1099,k1_zfmisc_1(A_1102))
      | v1_xboole_0(D_1099)
      | ~ m1_subset_1(C_1100,k1_zfmisc_1(A_1102))
      | v1_xboole_0(C_1100)
      | v1_xboole_0(B_1097)
      | v1_xboole_0(A_1102) ) ),
    inference(resolution,[status(thm)],[c_50,c_5247])).

tff(c_5650,plain,(
    ! [A_1102,C_1100,E_1101] :
      ( k2_partfun1(k4_subset_1(A_1102,C_1100,'#skF_6'),'#skF_4',k1_tmap_1(A_1102,'#skF_4',C_1100,'#skF_6',E_1101,'#skF_8'),C_1100) = E_1101
      | ~ v1_funct_1(k1_tmap_1(A_1102,'#skF_4',C_1100,'#skF_6',E_1101,'#skF_8'))
      | k2_partfun1(C_1100,'#skF_4',E_1101,k9_subset_1(A_1102,C_1100,'#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1(A_1102,C_1100,'#skF_6'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_1101,k1_zfmisc_1(k2_zfmisc_1(C_1100,'#skF_4')))
      | ~ v1_funct_2(E_1101,C_1100,'#skF_4')
      | ~ v1_funct_1(E_1101)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1102))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_1100,k1_zfmisc_1(A_1102))
      | v1_xboole_0(C_1100)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1102) ) ),
    inference(resolution,[status(thm)],[c_56,c_5646])).

tff(c_5656,plain,(
    ! [A_1102,C_1100,E_1101] :
      ( k2_partfun1(k4_subset_1(A_1102,C_1100,'#skF_6'),'#skF_4',k1_tmap_1(A_1102,'#skF_4',C_1100,'#skF_6',E_1101,'#skF_8'),C_1100) = E_1101
      | ~ v1_funct_1(k1_tmap_1(A_1102,'#skF_4',C_1100,'#skF_6',E_1101,'#skF_8'))
      | k2_partfun1(C_1100,'#skF_4',E_1101,k9_subset_1(A_1102,C_1100,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_1102,C_1100,'#skF_6'))
      | ~ m1_subset_1(E_1101,k1_zfmisc_1(k2_zfmisc_1(C_1100,'#skF_4')))
      | ~ v1_funct_2(E_1101,C_1100,'#skF_4')
      | ~ v1_funct_1(E_1101)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1102))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_1100,k1_zfmisc_1(A_1102))
      | v1_xboole_0(C_1100)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_4056,c_5650])).

tff(c_6567,plain,(
    ! [A_1208,C_1209,E_1210] :
      ( k2_partfun1(k4_subset_1(A_1208,C_1209,'#skF_6'),'#skF_4',k1_tmap_1(A_1208,'#skF_4',C_1209,'#skF_6',E_1210,'#skF_8'),C_1209) = E_1210
      | ~ v1_funct_1(k1_tmap_1(A_1208,'#skF_4',C_1209,'#skF_6',E_1210,'#skF_8'))
      | k2_partfun1(C_1209,'#skF_4',E_1210,k9_subset_1(A_1208,C_1209,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_1208,C_1209,'#skF_6'))
      | ~ m1_subset_1(E_1210,k1_zfmisc_1(k2_zfmisc_1(C_1209,'#skF_4')))
      | ~ v1_funct_2(E_1210,C_1209,'#skF_4')
      | ~ v1_funct_1(E_1210)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1208))
      | ~ m1_subset_1(C_1209,k1_zfmisc_1(A_1208))
      | v1_xboole_0(C_1209)
      | v1_xboole_0(A_1208) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_72,c_5656])).

tff(c_6574,plain,(
    ! [A_1208] :
      ( k2_partfun1(k4_subset_1(A_1208,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_1208,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1208,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1(A_1208,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_1208,'#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1208))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1208))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_1208) ) ),
    inference(resolution,[status(thm)],[c_62,c_6567])).

tff(c_6584,plain,(
    ! [A_1208] :
      ( k2_partfun1(k4_subset_1(A_1208,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_1208,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1208,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_1208,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_1208,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1208))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1208))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_1208) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_4059,c_6574])).

tff(c_6587,plain,(
    ! [A_1211] :
      ( k2_partfun1(k4_subset_1(A_1211,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_1211,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1211,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_1211,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_1211,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1211))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1211))
      | v1_xboole_0(A_1211) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_6584])).

tff(c_1152,plain,(
    ! [A_409,B_410] :
      ( r2_hidden('#skF_2'(A_409,B_410),B_410)
      | r1_xboole_0(A_409,B_410) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1156,plain,(
    ! [B_410,A_409] :
      ( ~ v1_xboole_0(B_410)
      | r1_xboole_0(A_409,B_410) ) ),
    inference(resolution,[status(thm)],[c_1152,c_2])).

tff(c_1130,plain,(
    ! [B_407,A_408] :
      ( v1_relat_1(B_407)
      | ~ m1_subset_1(B_407,k1_zfmisc_1(A_408))
      | ~ v1_relat_1(A_408) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1133,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_4')) ),
    inference(resolution,[status(thm)],[c_56,c_1130])).

tff(c_1145,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1133])).

tff(c_1190,plain,(
    ! [C_419,A_420,B_421] :
      ( v4_relat_1(C_419,A_420)
      | ~ m1_subset_1(C_419,k1_zfmisc_1(k2_zfmisc_1(A_420,B_421))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1197,plain,(
    v4_relat_1('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_1190])).

tff(c_1209,plain,(
    ! [B_425,A_426] :
      ( k7_relat_1(B_425,A_426) = B_425
      | ~ v4_relat_1(B_425,A_426)
      | ~ v1_relat_1(B_425) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1215,plain,
    ( k7_relat_1('#skF_8','#skF_6') = '#skF_8'
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_1197,c_1209])).

tff(c_1221,plain,(
    k7_relat_1('#skF_8','#skF_6') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1145,c_1215])).

tff(c_1265,plain,(
    ! [C_434,A_435,B_436] :
      ( k7_relat_1(k7_relat_1(C_434,A_435),B_436) = k1_xboole_0
      | ~ r1_xboole_0(A_435,B_436)
      | ~ v1_relat_1(C_434) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1280,plain,(
    ! [B_436] :
      ( k7_relat_1('#skF_8',B_436) = k1_xboole_0
      | ~ r1_xboole_0('#skF_6',B_436)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1221,c_1265])).

tff(c_1290,plain,(
    ! [B_437] :
      ( k7_relat_1('#skF_8',B_437) = k1_xboole_0
      | ~ r1_xboole_0('#skF_6',B_437) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1145,c_1280])).

tff(c_1313,plain,(
    ! [B_438] :
      ( k7_relat_1('#skF_8',B_438) = k1_xboole_0
      | ~ v1_xboole_0(B_438) ) ),
    inference(resolution,[status(thm)],[c_1156,c_1290])).

tff(c_1317,plain,(
    k7_relat_1('#skF_8',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_1313])).

tff(c_1243,plain,(
    ! [A_429,B_430] :
      ( r1_xboole_0(A_429,B_430)
      | ~ r1_subset_1(A_429,B_430)
      | v1_xboole_0(B_430)
      | v1_xboole_0(A_429) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1630,plain,(
    ! [A_474,B_475] :
      ( k3_xboole_0(A_474,B_475) = k1_xboole_0
      | ~ r1_subset_1(A_474,B_475)
      | v1_xboole_0(B_475)
      | v1_xboole_0(A_474) ) ),
    inference(resolution,[status(thm)],[c_1243,c_6])).

tff(c_1636,plain,
    ( k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0
    | v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_1630])).

tff(c_1640,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_72,c_1636])).

tff(c_1136,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_62,c_1130])).

tff(c_1148,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1136])).

tff(c_1198,plain,(
    v4_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_1190])).

tff(c_1212,plain,
    ( k7_relat_1('#skF_7','#skF_5') = '#skF_7'
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_1198,c_1209])).

tff(c_1218,plain,(
    k7_relat_1('#skF_7','#skF_5') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1148,c_1212])).

tff(c_1283,plain,(
    ! [B_436] :
      ( k7_relat_1('#skF_7',B_436) = k1_xboole_0
      | ~ r1_xboole_0('#skF_5',B_436)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1218,c_1265])).

tff(c_1328,plain,(
    ! [B_440] :
      ( k7_relat_1('#skF_7',B_440) = k1_xboole_0
      | ~ r1_xboole_0('#skF_5',B_440) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1148,c_1283])).

tff(c_1351,plain,(
    ! [B_441] :
      ( k7_relat_1('#skF_7',B_441) = k1_xboole_0
      | ~ v1_xboole_0(B_441) ) ),
    inference(resolution,[status(thm)],[c_1156,c_1328])).

tff(c_1355,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_1351])).

tff(c_1403,plain,(
    ! [A_444,B_445,C_446] :
      ( k9_subset_1(A_444,B_445,C_446) = k3_xboole_0(B_445,C_446)
      | ~ m1_subset_1(C_446,k1_zfmisc_1(A_444)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1414,plain,(
    ! [B_445] : k9_subset_1('#skF_3',B_445,'#skF_6') = k3_xboole_0(B_445,'#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_1403])).

tff(c_1558,plain,(
    ! [A_465,E_464,C_463,F_461,B_460,D_462] :
      ( v1_funct_1(k1_tmap_1(A_465,B_460,C_463,D_462,E_464,F_461))
      | ~ m1_subset_1(F_461,k1_zfmisc_1(k2_zfmisc_1(D_462,B_460)))
      | ~ v1_funct_2(F_461,D_462,B_460)
      | ~ v1_funct_1(F_461)
      | ~ m1_subset_1(E_464,k1_zfmisc_1(k2_zfmisc_1(C_463,B_460)))
      | ~ v1_funct_2(E_464,C_463,B_460)
      | ~ v1_funct_1(E_464)
      | ~ m1_subset_1(D_462,k1_zfmisc_1(A_465))
      | v1_xboole_0(D_462)
      | ~ m1_subset_1(C_463,k1_zfmisc_1(A_465))
      | v1_xboole_0(C_463)
      | v1_xboole_0(B_460)
      | v1_xboole_0(A_465) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_1560,plain,(
    ! [A_465,C_463,E_464] :
      ( v1_funct_1(k1_tmap_1(A_465,'#skF_4',C_463,'#skF_6',E_464,'#skF_8'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_464,k1_zfmisc_1(k2_zfmisc_1(C_463,'#skF_4')))
      | ~ v1_funct_2(E_464,C_463,'#skF_4')
      | ~ v1_funct_1(E_464)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_465))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_463,k1_zfmisc_1(A_465))
      | v1_xboole_0(C_463)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_465) ) ),
    inference(resolution,[status(thm)],[c_56,c_1558])).

tff(c_1565,plain,(
    ! [A_465,C_463,E_464] :
      ( v1_funct_1(k1_tmap_1(A_465,'#skF_4',C_463,'#skF_6',E_464,'#skF_8'))
      | ~ m1_subset_1(E_464,k1_zfmisc_1(k2_zfmisc_1(C_463,'#skF_4')))
      | ~ v1_funct_2(E_464,C_463,'#skF_4')
      | ~ v1_funct_1(E_464)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_465))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_463,k1_zfmisc_1(A_465))
      | v1_xboole_0(C_463)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_465) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1560])).

tff(c_1604,plain,(
    ! [A_469,C_470,E_471] :
      ( v1_funct_1(k1_tmap_1(A_469,'#skF_4',C_470,'#skF_6',E_471,'#skF_8'))
      | ~ m1_subset_1(E_471,k1_zfmisc_1(k2_zfmisc_1(C_470,'#skF_4')))
      | ~ v1_funct_2(E_471,C_470,'#skF_4')
      | ~ v1_funct_1(E_471)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_469))
      | ~ m1_subset_1(C_470,k1_zfmisc_1(A_469))
      | v1_xboole_0(C_470)
      | v1_xboole_0(A_469) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_72,c_1565])).

tff(c_1608,plain,(
    ! [A_469] :
      ( v1_funct_1(k1_tmap_1(A_469,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_469))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_469))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_469) ) ),
    inference(resolution,[status(thm)],[c_62,c_1604])).

tff(c_1615,plain,(
    ! [A_469] :
      ( v1_funct_1(k1_tmap_1(A_469,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_469))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_469))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_469) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1608])).

tff(c_1883,plain,(
    ! [A_506] :
      ( v1_funct_1(k1_tmap_1(A_506,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_506))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_506))
      | v1_xboole_0(A_506) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1615])).

tff(c_1886,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_1883])).

tff(c_1889,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1886])).

tff(c_1890,plain,(
    v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1889])).

tff(c_1471,plain,(
    ! [A_450,B_451,C_452,D_453] :
      ( k2_partfun1(A_450,B_451,C_452,D_453) = k7_relat_1(C_452,D_453)
      | ~ m1_subset_1(C_452,k1_zfmisc_1(k2_zfmisc_1(A_450,B_451)))
      | ~ v1_funct_1(C_452) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1475,plain,(
    ! [D_453] :
      ( k2_partfun1('#skF_5','#skF_4','#skF_7',D_453) = k7_relat_1('#skF_7',D_453)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_62,c_1471])).

tff(c_1481,plain,(
    ! [D_453] : k2_partfun1('#skF_5','#skF_4','#skF_7',D_453) = k7_relat_1('#skF_7',D_453) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1475])).

tff(c_1473,plain,(
    ! [D_453] :
      ( k2_partfun1('#skF_6','#skF_4','#skF_8',D_453) = k7_relat_1('#skF_8',D_453)
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_56,c_1471])).

tff(c_1478,plain,(
    ! [D_453] : k2_partfun1('#skF_6','#skF_4','#skF_8',D_453) = k7_relat_1('#skF_8',D_453) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1473])).

tff(c_2041,plain,(
    ! [C_546,D_543,B_547,E_544,F_545,A_542] :
      ( k2_partfun1(k4_subset_1(A_542,C_546,D_543),B_547,k1_tmap_1(A_542,B_547,C_546,D_543,E_544,F_545),D_543) = F_545
      | ~ m1_subset_1(k1_tmap_1(A_542,B_547,C_546,D_543,E_544,F_545),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_542,C_546,D_543),B_547)))
      | ~ v1_funct_2(k1_tmap_1(A_542,B_547,C_546,D_543,E_544,F_545),k4_subset_1(A_542,C_546,D_543),B_547)
      | ~ v1_funct_1(k1_tmap_1(A_542,B_547,C_546,D_543,E_544,F_545))
      | k2_partfun1(D_543,B_547,F_545,k9_subset_1(A_542,C_546,D_543)) != k2_partfun1(C_546,B_547,E_544,k9_subset_1(A_542,C_546,D_543))
      | ~ m1_subset_1(F_545,k1_zfmisc_1(k2_zfmisc_1(D_543,B_547)))
      | ~ v1_funct_2(F_545,D_543,B_547)
      | ~ v1_funct_1(F_545)
      | ~ m1_subset_1(E_544,k1_zfmisc_1(k2_zfmisc_1(C_546,B_547)))
      | ~ v1_funct_2(E_544,C_546,B_547)
      | ~ v1_funct_1(E_544)
      | ~ m1_subset_1(D_543,k1_zfmisc_1(A_542))
      | v1_xboole_0(D_543)
      | ~ m1_subset_1(C_546,k1_zfmisc_1(A_542))
      | v1_xboole_0(C_546)
      | v1_xboole_0(B_547)
      | v1_xboole_0(A_542) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_2621,plain,(
    ! [C_669,E_670,B_666,A_671,F_667,D_668] :
      ( k2_partfun1(k4_subset_1(A_671,C_669,D_668),B_666,k1_tmap_1(A_671,B_666,C_669,D_668,E_670,F_667),D_668) = F_667
      | ~ v1_funct_2(k1_tmap_1(A_671,B_666,C_669,D_668,E_670,F_667),k4_subset_1(A_671,C_669,D_668),B_666)
      | ~ v1_funct_1(k1_tmap_1(A_671,B_666,C_669,D_668,E_670,F_667))
      | k2_partfun1(D_668,B_666,F_667,k9_subset_1(A_671,C_669,D_668)) != k2_partfun1(C_669,B_666,E_670,k9_subset_1(A_671,C_669,D_668))
      | ~ m1_subset_1(F_667,k1_zfmisc_1(k2_zfmisc_1(D_668,B_666)))
      | ~ v1_funct_2(F_667,D_668,B_666)
      | ~ v1_funct_1(F_667)
      | ~ m1_subset_1(E_670,k1_zfmisc_1(k2_zfmisc_1(C_669,B_666)))
      | ~ v1_funct_2(E_670,C_669,B_666)
      | ~ v1_funct_1(E_670)
      | ~ m1_subset_1(D_668,k1_zfmisc_1(A_671))
      | v1_xboole_0(D_668)
      | ~ m1_subset_1(C_669,k1_zfmisc_1(A_671))
      | v1_xboole_0(C_669)
      | v1_xboole_0(B_666)
      | v1_xboole_0(A_671) ) ),
    inference(resolution,[status(thm)],[c_48,c_2041])).

tff(c_3255,plain,(
    ! [C_741,F_739,B_738,A_743,D_740,E_742] :
      ( k2_partfun1(k4_subset_1(A_743,C_741,D_740),B_738,k1_tmap_1(A_743,B_738,C_741,D_740,E_742,F_739),D_740) = F_739
      | ~ v1_funct_1(k1_tmap_1(A_743,B_738,C_741,D_740,E_742,F_739))
      | k2_partfun1(D_740,B_738,F_739,k9_subset_1(A_743,C_741,D_740)) != k2_partfun1(C_741,B_738,E_742,k9_subset_1(A_743,C_741,D_740))
      | ~ m1_subset_1(F_739,k1_zfmisc_1(k2_zfmisc_1(D_740,B_738)))
      | ~ v1_funct_2(F_739,D_740,B_738)
      | ~ v1_funct_1(F_739)
      | ~ m1_subset_1(E_742,k1_zfmisc_1(k2_zfmisc_1(C_741,B_738)))
      | ~ v1_funct_2(E_742,C_741,B_738)
      | ~ v1_funct_1(E_742)
      | ~ m1_subset_1(D_740,k1_zfmisc_1(A_743))
      | v1_xboole_0(D_740)
      | ~ m1_subset_1(C_741,k1_zfmisc_1(A_743))
      | v1_xboole_0(C_741)
      | v1_xboole_0(B_738)
      | v1_xboole_0(A_743) ) ),
    inference(resolution,[status(thm)],[c_50,c_2621])).

tff(c_3259,plain,(
    ! [A_743,C_741,E_742] :
      ( k2_partfun1(k4_subset_1(A_743,C_741,'#skF_6'),'#skF_4',k1_tmap_1(A_743,'#skF_4',C_741,'#skF_6',E_742,'#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_743,'#skF_4',C_741,'#skF_6',E_742,'#skF_8'))
      | k2_partfun1(C_741,'#skF_4',E_742,k9_subset_1(A_743,C_741,'#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1(A_743,C_741,'#skF_6'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_742,k1_zfmisc_1(k2_zfmisc_1(C_741,'#skF_4')))
      | ~ v1_funct_2(E_742,C_741,'#skF_4')
      | ~ v1_funct_1(E_742)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_743))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_741,k1_zfmisc_1(A_743))
      | v1_xboole_0(C_741)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_743) ) ),
    inference(resolution,[status(thm)],[c_56,c_3255])).

tff(c_3265,plain,(
    ! [A_743,C_741,E_742] :
      ( k2_partfun1(k4_subset_1(A_743,C_741,'#skF_6'),'#skF_4',k1_tmap_1(A_743,'#skF_4',C_741,'#skF_6',E_742,'#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_743,'#skF_4',C_741,'#skF_6',E_742,'#skF_8'))
      | k2_partfun1(C_741,'#skF_4',E_742,k9_subset_1(A_743,C_741,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_743,C_741,'#skF_6'))
      | ~ m1_subset_1(E_742,k1_zfmisc_1(k2_zfmisc_1(C_741,'#skF_4')))
      | ~ v1_funct_2(E_742,C_741,'#skF_4')
      | ~ v1_funct_1(E_742)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_743))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_741,k1_zfmisc_1(A_743))
      | v1_xboole_0(C_741)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_743) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1478,c_3259])).

tff(c_3484,plain,(
    ! [A_766,C_767,E_768] :
      ( k2_partfun1(k4_subset_1(A_766,C_767,'#skF_6'),'#skF_4',k1_tmap_1(A_766,'#skF_4',C_767,'#skF_6',E_768,'#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_766,'#skF_4',C_767,'#skF_6',E_768,'#skF_8'))
      | k2_partfun1(C_767,'#skF_4',E_768,k9_subset_1(A_766,C_767,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_766,C_767,'#skF_6'))
      | ~ m1_subset_1(E_768,k1_zfmisc_1(k2_zfmisc_1(C_767,'#skF_4')))
      | ~ v1_funct_2(E_768,C_767,'#skF_4')
      | ~ v1_funct_1(E_768)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_766))
      | ~ m1_subset_1(C_767,k1_zfmisc_1(A_766))
      | v1_xboole_0(C_767)
      | v1_xboole_0(A_766) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_72,c_3265])).

tff(c_3491,plain,(
    ! [A_766] :
      ( k2_partfun1(k4_subset_1(A_766,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_766,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_766,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1(A_766,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_766,'#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_766))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_766))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_766) ) ),
    inference(resolution,[status(thm)],[c_62,c_3484])).

tff(c_3501,plain,(
    ! [A_766] :
      ( k2_partfun1(k4_subset_1(A_766,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_766,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_766,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_766,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_766,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_766))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_766))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_766) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1481,c_3491])).

tff(c_3591,plain,(
    ! [A_780] :
      ( k2_partfun1(k4_subset_1(A_780,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_780,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_780,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_780,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_780,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_780))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_780))
      | v1_xboole_0(A_780) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_3501])).

tff(c_126,plain,(
    ! [A_242,B_243] :
      ( r2_hidden('#skF_2'(A_242,B_243),B_243)
      | r1_xboole_0(A_242,B_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_130,plain,(
    ! [B_243,A_242] :
      ( ~ v1_xboole_0(B_243)
      | r1_xboole_0(A_242,B_243) ) ),
    inference(resolution,[status(thm)],[c_126,c_2])).

tff(c_104,plain,(
    ! [B_240,A_241] :
      ( v1_relat_1(B_240)
      | ~ m1_subset_1(B_240,k1_zfmisc_1(A_241))
      | ~ v1_relat_1(A_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_107,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_4')) ),
    inference(resolution,[status(thm)],[c_56,c_104])).

tff(c_119,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_107])).

tff(c_217,plain,(
    ! [C_266,A_267,B_268] :
      ( v4_relat_1(C_266,A_267)
      | ~ m1_subset_1(C_266,k1_zfmisc_1(k2_zfmisc_1(A_267,B_268))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_224,plain,(
    v4_relat_1('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_217])).

tff(c_228,plain,
    ( k7_relat_1('#skF_8','#skF_6') = '#skF_8'
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_224,c_30])).

tff(c_231,plain,(
    k7_relat_1('#skF_8','#skF_6') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_228])).

tff(c_347,plain,(
    ! [C_286,A_287,B_288] :
      ( k7_relat_1(k7_relat_1(C_286,A_287),B_288) = k1_xboole_0
      | ~ r1_xboole_0(A_287,B_288)
      | ~ v1_relat_1(C_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_365,plain,(
    ! [B_288] :
      ( k7_relat_1('#skF_8',B_288) = k1_xboole_0
      | ~ r1_xboole_0('#skF_6',B_288)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_347])).

tff(c_420,plain,(
    ! [B_295] :
      ( k7_relat_1('#skF_8',B_295) = k1_xboole_0
      | ~ r1_xboole_0('#skF_6',B_295) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_365])).

tff(c_443,plain,(
    ! [B_296] :
      ( k7_relat_1('#skF_8',B_296) = k1_xboole_0
      | ~ v1_xboole_0(B_296) ) ),
    inference(resolution,[status(thm)],[c_130,c_420])).

tff(c_447,plain,(
    k7_relat_1('#skF_8',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_443])).

tff(c_259,plain,(
    ! [A_271,B_272] :
      ( r1_xboole_0(A_271,B_272)
      | ~ r1_subset_1(A_271,B_272)
      | v1_xboole_0(B_272)
      | v1_xboole_0(A_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_635,plain,(
    ! [A_320,B_321] :
      ( k3_xboole_0(A_320,B_321) = k1_xboole_0
      | ~ r1_subset_1(A_320,B_321)
      | v1_xboole_0(B_321)
      | v1_xboole_0(A_320) ) ),
    inference(resolution,[status(thm)],[c_259,c_6])).

tff(c_638,plain,
    ( k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0
    | v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_635])).

tff(c_641,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_72,c_638])).

tff(c_110,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_62,c_104])).

tff(c_122,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_110])).

tff(c_225,plain,(
    v4_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_217])).

tff(c_234,plain,
    ( k7_relat_1('#skF_7','#skF_5') = '#skF_7'
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_225,c_30])).

tff(c_237,plain,(
    k7_relat_1('#skF_7','#skF_5') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_234])).

tff(c_362,plain,(
    ! [B_288] :
      ( k7_relat_1('#skF_7',B_288) = k1_xboole_0
      | ~ r1_xboole_0('#skF_5',B_288)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_347])).

tff(c_372,plain,(
    ! [B_289] :
      ( k7_relat_1('#skF_7',B_289) = k1_xboole_0
      | ~ r1_xboole_0('#skF_5',B_289) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_362])).

tff(c_395,plain,(
    ! [B_290] :
      ( k7_relat_1('#skF_7',B_290) = k1_xboole_0
      | ~ v1_xboole_0(B_290) ) ),
    inference(resolution,[status(thm)],[c_130,c_372])).

tff(c_399,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_395])).

tff(c_409,plain,(
    ! [A_291,B_292,C_293,D_294] :
      ( k2_partfun1(A_291,B_292,C_293,D_294) = k7_relat_1(C_293,D_294)
      | ~ m1_subset_1(C_293,k1_zfmisc_1(k2_zfmisc_1(A_291,B_292)))
      | ~ v1_funct_1(C_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_413,plain,(
    ! [D_294] :
      ( k2_partfun1('#skF_5','#skF_4','#skF_7',D_294) = k7_relat_1('#skF_7',D_294)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_62,c_409])).

tff(c_419,plain,(
    ! [D_294] : k2_partfun1('#skF_5','#skF_4','#skF_7',D_294) = k7_relat_1('#skF_7',D_294) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_413])).

tff(c_411,plain,(
    ! [D_294] :
      ( k2_partfun1('#skF_6','#skF_4','#skF_8',D_294) = k7_relat_1('#skF_8',D_294)
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_56,c_409])).

tff(c_416,plain,(
    ! [D_294] : k2_partfun1('#skF_6','#skF_4','#skF_8',D_294) = k7_relat_1('#skF_8',D_294) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_411])).

tff(c_286,plain,(
    ! [A_278,B_279,C_280] :
      ( k9_subset_1(A_278,B_279,C_280) = k3_xboole_0(B_279,C_280)
      | ~ m1_subset_1(C_280,k1_zfmisc_1(A_278)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_297,plain,(
    ! [B_279] : k9_subset_1('#skF_3',B_279,'#skF_6') = k3_xboole_0(B_279,'#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_286])).

tff(c_54,plain,
    ( k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') != '#skF_8'
    | k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') != '#skF_7'
    | k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_94,plain,(
    k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_310,plain,(
    k2_partfun1('#skF_5','#skF_4','#skF_7',k3_xboole_0('#skF_5','#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_297,c_94])).

tff(c_1071,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_447,c_641,c_399,c_641,c_419,c_416,c_310])).

tff(c_1072,plain,
    ( k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') != '#skF_7'
    | k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1122,plain,(
    k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1072])).

tff(c_3602,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3591,c_1122])).

tff(c_3616,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_1317,c_1640,c_1355,c_1640,c_1414,c_1414,c_1890,c_3602])).

tff(c_3618,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_3616])).

tff(c_3619,plain,(
    k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1072])).

tff(c_6596,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6587,c_3619])).

tff(c_6607,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_3872,c_4116,c_3819,c_4116,c_3919,c_3919,c_4801,c_6596])).

tff(c_6609,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_6607])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:20:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.45/2.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.45/2.88  
% 7.45/2.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.45/2.89  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2
% 7.45/2.89  
% 7.45/2.89  %Foreground sorts:
% 7.45/2.89  
% 7.45/2.89  
% 7.45/2.89  %Background operators:
% 7.45/2.89  
% 7.45/2.89  
% 7.45/2.89  %Foreground operators:
% 7.45/2.89  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 7.45/2.89  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.45/2.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.45/2.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.45/2.89  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.45/2.89  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.45/2.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.45/2.89  tff('#skF_7', type, '#skF_7': $i).
% 7.45/2.89  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.45/2.89  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 7.45/2.89  tff('#skF_5', type, '#skF_5': $i).
% 7.45/2.89  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.45/2.89  tff('#skF_6', type, '#skF_6': $i).
% 7.45/2.89  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.45/2.89  tff('#skF_3', type, '#skF_3': $i).
% 7.45/2.89  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.45/2.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.45/2.89  tff('#skF_8', type, '#skF_8': $i).
% 7.45/2.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.45/2.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.45/2.89  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.45/2.89  tff('#skF_4', type, '#skF_4': $i).
% 7.45/2.89  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.45/2.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.45/2.89  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.45/2.89  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 7.45/2.89  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.45/2.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.45/2.89  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.45/2.89  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.45/2.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.45/2.89  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.45/2.89  
% 7.77/2.92  tff(f_234, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 7.77/2.92  tff(f_36, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.77/2.92  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 7.77/2.92  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.77/2.92  tff(f_76, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.77/2.92  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.77/2.92  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.77/2.92  tff(f_88, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 7.77/2.92  tff(f_82, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 7.77/2.92  tff(f_98, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 7.77/2.92  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 7.77/2.92  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 7.77/2.92  tff(f_192, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 7.77/2.92  tff(f_110, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 7.77/2.92  tff(f_158, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 7.77/2.92  tff(c_80, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_234])).
% 7.77/2.92  tff(c_74, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_234])).
% 7.77/2.92  tff(c_70, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_234])).
% 7.77/2.92  tff(c_10, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.77/2.92  tff(c_3650, plain, (![A_784, B_785]: (r2_hidden('#skF_2'(A_784, B_785), B_785) | r1_xboole_0(A_784, B_785))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.77/2.92  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.77/2.92  tff(c_3654, plain, (![B_785, A_784]: (~v1_xboole_0(B_785) | r1_xboole_0(A_784, B_785))), inference(resolution, [status(thm)], [c_3650, c_2])).
% 7.77/2.92  tff(c_26, plain, (![A_23, B_24]: (v1_relat_1(k2_zfmisc_1(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.77/2.92  tff(c_56, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_234])).
% 7.77/2.92  tff(c_3628, plain, (![B_782, A_783]: (v1_relat_1(B_782) | ~m1_subset_1(B_782, k1_zfmisc_1(A_783)) | ~v1_relat_1(A_783))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.77/2.92  tff(c_3631, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_4'))), inference(resolution, [status(thm)], [c_56, c_3628])).
% 7.77/2.92  tff(c_3643, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_3631])).
% 7.77/2.92  tff(c_3703, plain, (![C_799, A_800, B_801]: (v4_relat_1(C_799, A_800) | ~m1_subset_1(C_799, k1_zfmisc_1(k2_zfmisc_1(A_800, B_801))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.77/2.92  tff(c_3710, plain, (v4_relat_1('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_56, c_3703])).
% 7.77/2.92  tff(c_30, plain, (![B_29, A_28]: (k7_relat_1(B_29, A_28)=B_29 | ~v4_relat_1(B_29, A_28) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.77/2.92  tff(c_3714, plain, (k7_relat_1('#skF_8', '#skF_6')='#skF_8' | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_3710, c_30])).
% 7.77/2.92  tff(c_3717, plain, (k7_relat_1('#skF_8', '#skF_6')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_3643, c_3714])).
% 7.77/2.92  tff(c_3767, plain, (![C_809, A_810, B_811]: (k7_relat_1(k7_relat_1(C_809, A_810), B_811)=k1_xboole_0 | ~r1_xboole_0(A_810, B_811) | ~v1_relat_1(C_809))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.77/2.92  tff(c_3785, plain, (![B_811]: (k7_relat_1('#skF_8', B_811)=k1_xboole_0 | ~r1_xboole_0('#skF_6', B_811) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_3717, c_3767])).
% 7.77/2.92  tff(c_3845, plain, (![B_815]: (k7_relat_1('#skF_8', B_815)=k1_xboole_0 | ~r1_xboole_0('#skF_6', B_815))), inference(demodulation, [status(thm), theory('equality')], [c_3643, c_3785])).
% 7.77/2.92  tff(c_3868, plain, (![B_816]: (k7_relat_1('#skF_8', B_816)=k1_xboole_0 | ~v1_xboole_0(B_816))), inference(resolution, [status(thm)], [c_3654, c_3845])).
% 7.77/2.92  tff(c_3872, plain, (k7_relat_1('#skF_8', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_3868])).
% 7.77/2.92  tff(c_76, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_234])).
% 7.77/2.92  tff(c_72, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_234])).
% 7.77/2.92  tff(c_68, plain, (r1_subset_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_234])).
% 7.77/2.92  tff(c_3732, plain, (![A_802, B_803]: (r1_xboole_0(A_802, B_803) | ~r1_subset_1(A_802, B_803) | v1_xboole_0(B_803) | v1_xboole_0(A_802))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.77/2.92  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.77/2.92  tff(c_4110, plain, (![A_838, B_839]: (k3_xboole_0(A_838, B_839)=k1_xboole_0 | ~r1_subset_1(A_838, B_839) | v1_xboole_0(B_839) | v1_xboole_0(A_838))), inference(resolution, [status(thm)], [c_3732, c_6])).
% 7.77/2.92  tff(c_4113, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0 | v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_68, c_4110])).
% 7.77/2.92  tff(c_4116, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_76, c_72, c_4113])).
% 7.77/2.92  tff(c_62, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_234])).
% 7.77/2.92  tff(c_3634, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_3628])).
% 7.77/2.92  tff(c_3646, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_3634])).
% 7.77/2.92  tff(c_3711, plain, (v4_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_62, c_3703])).
% 7.77/2.92  tff(c_3720, plain, (k7_relat_1('#skF_7', '#skF_5')='#skF_7' | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_3711, c_30])).
% 7.77/2.92  tff(c_3723, plain, (k7_relat_1('#skF_7', '#skF_5')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_3646, c_3720])).
% 7.77/2.92  tff(c_3782, plain, (![B_811]: (k7_relat_1('#skF_7', B_811)=k1_xboole_0 | ~r1_xboole_0('#skF_5', B_811) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_3723, c_3767])).
% 7.77/2.92  tff(c_3792, plain, (![B_812]: (k7_relat_1('#skF_7', B_812)=k1_xboole_0 | ~r1_xboole_0('#skF_5', B_812))), inference(demodulation, [status(thm), theory('equality')], [c_3646, c_3782])).
% 7.77/2.92  tff(c_3815, plain, (![B_813]: (k7_relat_1('#skF_7', B_813)=k1_xboole_0 | ~v1_xboole_0(B_813))), inference(resolution, [status(thm)], [c_3654, c_3792])).
% 7.77/2.92  tff(c_3819, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_3815])).
% 7.77/2.92  tff(c_3908, plain, (![A_818, B_819, C_820]: (k9_subset_1(A_818, B_819, C_820)=k3_xboole_0(B_819, C_820) | ~m1_subset_1(C_820, k1_zfmisc_1(A_818)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.77/2.92  tff(c_3919, plain, (![B_819]: (k9_subset_1('#skF_3', B_819, '#skF_6')=k3_xboole_0(B_819, '#skF_6'))), inference(resolution, [status(thm)], [c_70, c_3908])).
% 7.77/2.92  tff(c_66, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_234])).
% 7.77/2.92  tff(c_64, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_234])).
% 7.77/2.92  tff(c_78, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_234])).
% 7.77/2.92  tff(c_60, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_234])).
% 7.77/2.92  tff(c_58, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_234])).
% 7.77/2.92  tff(c_4149, plain, (![D_847, A_850, B_845, E_849, F_846, C_848]: (v1_funct_1(k1_tmap_1(A_850, B_845, C_848, D_847, E_849, F_846)) | ~m1_subset_1(F_846, k1_zfmisc_1(k2_zfmisc_1(D_847, B_845))) | ~v1_funct_2(F_846, D_847, B_845) | ~v1_funct_1(F_846) | ~m1_subset_1(E_849, k1_zfmisc_1(k2_zfmisc_1(C_848, B_845))) | ~v1_funct_2(E_849, C_848, B_845) | ~v1_funct_1(E_849) | ~m1_subset_1(D_847, k1_zfmisc_1(A_850)) | v1_xboole_0(D_847) | ~m1_subset_1(C_848, k1_zfmisc_1(A_850)) | v1_xboole_0(C_848) | v1_xboole_0(B_845) | v1_xboole_0(A_850))), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.77/2.92  tff(c_4151, plain, (![A_850, C_848, E_849]: (v1_funct_1(k1_tmap_1(A_850, '#skF_4', C_848, '#skF_6', E_849, '#skF_8')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_849, k1_zfmisc_1(k2_zfmisc_1(C_848, '#skF_4'))) | ~v1_funct_2(E_849, C_848, '#skF_4') | ~v1_funct_1(E_849) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_850)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_848, k1_zfmisc_1(A_850)) | v1_xboole_0(C_848) | v1_xboole_0('#skF_4') | v1_xboole_0(A_850))), inference(resolution, [status(thm)], [c_56, c_4149])).
% 7.77/2.92  tff(c_4156, plain, (![A_850, C_848, E_849]: (v1_funct_1(k1_tmap_1(A_850, '#skF_4', C_848, '#skF_6', E_849, '#skF_8')) | ~m1_subset_1(E_849, k1_zfmisc_1(k2_zfmisc_1(C_848, '#skF_4'))) | ~v1_funct_2(E_849, C_848, '#skF_4') | ~v1_funct_1(E_849) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_850)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_848, k1_zfmisc_1(A_850)) | v1_xboole_0(C_848) | v1_xboole_0('#skF_4') | v1_xboole_0(A_850))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_4151])).
% 7.77/2.92  tff(c_4547, plain, (![A_914, C_915, E_916]: (v1_funct_1(k1_tmap_1(A_914, '#skF_4', C_915, '#skF_6', E_916, '#skF_8')) | ~m1_subset_1(E_916, k1_zfmisc_1(k2_zfmisc_1(C_915, '#skF_4'))) | ~v1_funct_2(E_916, C_915, '#skF_4') | ~v1_funct_1(E_916) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_914)) | ~m1_subset_1(C_915, k1_zfmisc_1(A_914)) | v1_xboole_0(C_915) | v1_xboole_0(A_914))), inference(negUnitSimplification, [status(thm)], [c_78, c_72, c_4156])).
% 7.77/2.92  tff(c_4554, plain, (![A_914]: (v1_funct_1(k1_tmap_1(A_914, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_914)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_914)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_914))), inference(resolution, [status(thm)], [c_62, c_4547])).
% 7.77/2.92  tff(c_4564, plain, (![A_914]: (v1_funct_1(k1_tmap_1(A_914, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_914)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_914)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_914))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_4554])).
% 7.77/2.92  tff(c_4794, plain, (![A_955]: (v1_funct_1(k1_tmap_1(A_955, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_955)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_955)) | v1_xboole_0(A_955))), inference(negUnitSimplification, [status(thm)], [c_76, c_4564])).
% 7.77/2.92  tff(c_4797, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_74, c_4794])).
% 7.77/2.92  tff(c_4800, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_4797])).
% 7.77/2.92  tff(c_4801, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_80, c_4800])).
% 7.77/2.92  tff(c_4049, plain, (![A_829, B_830, C_831, D_832]: (k2_partfun1(A_829, B_830, C_831, D_832)=k7_relat_1(C_831, D_832) | ~m1_subset_1(C_831, k1_zfmisc_1(k2_zfmisc_1(A_829, B_830))) | ~v1_funct_1(C_831))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.77/2.92  tff(c_4053, plain, (![D_832]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_832)=k7_relat_1('#skF_7', D_832) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_62, c_4049])).
% 7.77/2.92  tff(c_4059, plain, (![D_832]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_832)=k7_relat_1('#skF_7', D_832))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_4053])).
% 7.77/2.92  tff(c_4051, plain, (![D_832]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_832)=k7_relat_1('#skF_8', D_832) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_56, c_4049])).
% 7.77/2.92  tff(c_4056, plain, (![D_832]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_832)=k7_relat_1('#skF_8', D_832))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_4051])).
% 7.77/2.92  tff(c_50, plain, (![D_169, E_170, A_166, B_167, C_168, F_171]: (v1_funct_2(k1_tmap_1(A_166, B_167, C_168, D_169, E_170, F_171), k4_subset_1(A_166, C_168, D_169), B_167) | ~m1_subset_1(F_171, k1_zfmisc_1(k2_zfmisc_1(D_169, B_167))) | ~v1_funct_2(F_171, D_169, B_167) | ~v1_funct_1(F_171) | ~m1_subset_1(E_170, k1_zfmisc_1(k2_zfmisc_1(C_168, B_167))) | ~v1_funct_2(E_170, C_168, B_167) | ~v1_funct_1(E_170) | ~m1_subset_1(D_169, k1_zfmisc_1(A_166)) | v1_xboole_0(D_169) | ~m1_subset_1(C_168, k1_zfmisc_1(A_166)) | v1_xboole_0(C_168) | v1_xboole_0(B_167) | v1_xboole_0(A_166))), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.77/2.92  tff(c_48, plain, (![D_169, E_170, A_166, B_167, C_168, F_171]: (m1_subset_1(k1_tmap_1(A_166, B_167, C_168, D_169, E_170, F_171), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_166, C_168, D_169), B_167))) | ~m1_subset_1(F_171, k1_zfmisc_1(k2_zfmisc_1(D_169, B_167))) | ~v1_funct_2(F_171, D_169, B_167) | ~v1_funct_1(F_171) | ~m1_subset_1(E_170, k1_zfmisc_1(k2_zfmisc_1(C_168, B_167))) | ~v1_funct_2(E_170, C_168, B_167) | ~v1_funct_1(E_170) | ~m1_subset_1(D_169, k1_zfmisc_1(A_166)) | v1_xboole_0(D_169) | ~m1_subset_1(C_168, k1_zfmisc_1(A_166)) | v1_xboole_0(C_168) | v1_xboole_0(B_167) | v1_xboole_0(A_166))), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.77/2.92  tff(c_4519, plain, (![F_903, D_901, B_905, A_900, E_902, C_904]: (k2_partfun1(k4_subset_1(A_900, C_904, D_901), B_905, k1_tmap_1(A_900, B_905, C_904, D_901, E_902, F_903), C_904)=E_902 | ~m1_subset_1(k1_tmap_1(A_900, B_905, C_904, D_901, E_902, F_903), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_900, C_904, D_901), B_905))) | ~v1_funct_2(k1_tmap_1(A_900, B_905, C_904, D_901, E_902, F_903), k4_subset_1(A_900, C_904, D_901), B_905) | ~v1_funct_1(k1_tmap_1(A_900, B_905, C_904, D_901, E_902, F_903)) | k2_partfun1(D_901, B_905, F_903, k9_subset_1(A_900, C_904, D_901))!=k2_partfun1(C_904, B_905, E_902, k9_subset_1(A_900, C_904, D_901)) | ~m1_subset_1(F_903, k1_zfmisc_1(k2_zfmisc_1(D_901, B_905))) | ~v1_funct_2(F_903, D_901, B_905) | ~v1_funct_1(F_903) | ~m1_subset_1(E_902, k1_zfmisc_1(k2_zfmisc_1(C_904, B_905))) | ~v1_funct_2(E_902, C_904, B_905) | ~v1_funct_1(E_902) | ~m1_subset_1(D_901, k1_zfmisc_1(A_900)) | v1_xboole_0(D_901) | ~m1_subset_1(C_904, k1_zfmisc_1(A_900)) | v1_xboole_0(C_904) | v1_xboole_0(B_905) | v1_xboole_0(A_900))), inference(cnfTransformation, [status(thm)], [f_158])).
% 7.77/2.92  tff(c_5247, plain, (![A_1052, D_1049, C_1050, E_1051, F_1048, B_1047]: (k2_partfun1(k4_subset_1(A_1052, C_1050, D_1049), B_1047, k1_tmap_1(A_1052, B_1047, C_1050, D_1049, E_1051, F_1048), C_1050)=E_1051 | ~v1_funct_2(k1_tmap_1(A_1052, B_1047, C_1050, D_1049, E_1051, F_1048), k4_subset_1(A_1052, C_1050, D_1049), B_1047) | ~v1_funct_1(k1_tmap_1(A_1052, B_1047, C_1050, D_1049, E_1051, F_1048)) | k2_partfun1(D_1049, B_1047, F_1048, k9_subset_1(A_1052, C_1050, D_1049))!=k2_partfun1(C_1050, B_1047, E_1051, k9_subset_1(A_1052, C_1050, D_1049)) | ~m1_subset_1(F_1048, k1_zfmisc_1(k2_zfmisc_1(D_1049, B_1047))) | ~v1_funct_2(F_1048, D_1049, B_1047) | ~v1_funct_1(F_1048) | ~m1_subset_1(E_1051, k1_zfmisc_1(k2_zfmisc_1(C_1050, B_1047))) | ~v1_funct_2(E_1051, C_1050, B_1047) | ~v1_funct_1(E_1051) | ~m1_subset_1(D_1049, k1_zfmisc_1(A_1052)) | v1_xboole_0(D_1049) | ~m1_subset_1(C_1050, k1_zfmisc_1(A_1052)) | v1_xboole_0(C_1050) | v1_xboole_0(B_1047) | v1_xboole_0(A_1052))), inference(resolution, [status(thm)], [c_48, c_4519])).
% 7.77/2.92  tff(c_5646, plain, (![E_1101, B_1097, A_1102, C_1100, F_1098, D_1099]: (k2_partfun1(k4_subset_1(A_1102, C_1100, D_1099), B_1097, k1_tmap_1(A_1102, B_1097, C_1100, D_1099, E_1101, F_1098), C_1100)=E_1101 | ~v1_funct_1(k1_tmap_1(A_1102, B_1097, C_1100, D_1099, E_1101, F_1098)) | k2_partfun1(D_1099, B_1097, F_1098, k9_subset_1(A_1102, C_1100, D_1099))!=k2_partfun1(C_1100, B_1097, E_1101, k9_subset_1(A_1102, C_1100, D_1099)) | ~m1_subset_1(F_1098, k1_zfmisc_1(k2_zfmisc_1(D_1099, B_1097))) | ~v1_funct_2(F_1098, D_1099, B_1097) | ~v1_funct_1(F_1098) | ~m1_subset_1(E_1101, k1_zfmisc_1(k2_zfmisc_1(C_1100, B_1097))) | ~v1_funct_2(E_1101, C_1100, B_1097) | ~v1_funct_1(E_1101) | ~m1_subset_1(D_1099, k1_zfmisc_1(A_1102)) | v1_xboole_0(D_1099) | ~m1_subset_1(C_1100, k1_zfmisc_1(A_1102)) | v1_xboole_0(C_1100) | v1_xboole_0(B_1097) | v1_xboole_0(A_1102))), inference(resolution, [status(thm)], [c_50, c_5247])).
% 7.77/2.92  tff(c_5650, plain, (![A_1102, C_1100, E_1101]: (k2_partfun1(k4_subset_1(A_1102, C_1100, '#skF_6'), '#skF_4', k1_tmap_1(A_1102, '#skF_4', C_1100, '#skF_6', E_1101, '#skF_8'), C_1100)=E_1101 | ~v1_funct_1(k1_tmap_1(A_1102, '#skF_4', C_1100, '#skF_6', E_1101, '#skF_8')) | k2_partfun1(C_1100, '#skF_4', E_1101, k9_subset_1(A_1102, C_1100, '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1(A_1102, C_1100, '#skF_6')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_1101, k1_zfmisc_1(k2_zfmisc_1(C_1100, '#skF_4'))) | ~v1_funct_2(E_1101, C_1100, '#skF_4') | ~v1_funct_1(E_1101) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1102)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_1100, k1_zfmisc_1(A_1102)) | v1_xboole_0(C_1100) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1102))), inference(resolution, [status(thm)], [c_56, c_5646])).
% 7.77/2.92  tff(c_5656, plain, (![A_1102, C_1100, E_1101]: (k2_partfun1(k4_subset_1(A_1102, C_1100, '#skF_6'), '#skF_4', k1_tmap_1(A_1102, '#skF_4', C_1100, '#skF_6', E_1101, '#skF_8'), C_1100)=E_1101 | ~v1_funct_1(k1_tmap_1(A_1102, '#skF_4', C_1100, '#skF_6', E_1101, '#skF_8')) | k2_partfun1(C_1100, '#skF_4', E_1101, k9_subset_1(A_1102, C_1100, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_1102, C_1100, '#skF_6')) | ~m1_subset_1(E_1101, k1_zfmisc_1(k2_zfmisc_1(C_1100, '#skF_4'))) | ~v1_funct_2(E_1101, C_1100, '#skF_4') | ~v1_funct_1(E_1101) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1102)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_1100, k1_zfmisc_1(A_1102)) | v1_xboole_0(C_1100) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1102))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_4056, c_5650])).
% 7.77/2.92  tff(c_6567, plain, (![A_1208, C_1209, E_1210]: (k2_partfun1(k4_subset_1(A_1208, C_1209, '#skF_6'), '#skF_4', k1_tmap_1(A_1208, '#skF_4', C_1209, '#skF_6', E_1210, '#skF_8'), C_1209)=E_1210 | ~v1_funct_1(k1_tmap_1(A_1208, '#skF_4', C_1209, '#skF_6', E_1210, '#skF_8')) | k2_partfun1(C_1209, '#skF_4', E_1210, k9_subset_1(A_1208, C_1209, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_1208, C_1209, '#skF_6')) | ~m1_subset_1(E_1210, k1_zfmisc_1(k2_zfmisc_1(C_1209, '#skF_4'))) | ~v1_funct_2(E_1210, C_1209, '#skF_4') | ~v1_funct_1(E_1210) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1208)) | ~m1_subset_1(C_1209, k1_zfmisc_1(A_1208)) | v1_xboole_0(C_1209) | v1_xboole_0(A_1208))), inference(negUnitSimplification, [status(thm)], [c_78, c_72, c_5656])).
% 7.77/2.92  tff(c_6574, plain, (![A_1208]: (k2_partfun1(k4_subset_1(A_1208, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_1208, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1208, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1(A_1208, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_1208, '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1208)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1208)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_1208))), inference(resolution, [status(thm)], [c_62, c_6567])).
% 7.77/2.92  tff(c_6584, plain, (![A_1208]: (k2_partfun1(k4_subset_1(A_1208, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_1208, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1208, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_1208, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_1208, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1208)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1208)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_1208))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_4059, c_6574])).
% 7.77/2.92  tff(c_6587, plain, (![A_1211]: (k2_partfun1(k4_subset_1(A_1211, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_1211, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1211, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_1211, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_1211, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1211)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1211)) | v1_xboole_0(A_1211))), inference(negUnitSimplification, [status(thm)], [c_76, c_6584])).
% 7.77/2.92  tff(c_1152, plain, (![A_409, B_410]: (r2_hidden('#skF_2'(A_409, B_410), B_410) | r1_xboole_0(A_409, B_410))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.77/2.92  tff(c_1156, plain, (![B_410, A_409]: (~v1_xboole_0(B_410) | r1_xboole_0(A_409, B_410))), inference(resolution, [status(thm)], [c_1152, c_2])).
% 7.77/2.92  tff(c_1130, plain, (![B_407, A_408]: (v1_relat_1(B_407) | ~m1_subset_1(B_407, k1_zfmisc_1(A_408)) | ~v1_relat_1(A_408))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.77/2.92  tff(c_1133, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_4'))), inference(resolution, [status(thm)], [c_56, c_1130])).
% 7.77/2.92  tff(c_1145, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1133])).
% 7.77/2.92  tff(c_1190, plain, (![C_419, A_420, B_421]: (v4_relat_1(C_419, A_420) | ~m1_subset_1(C_419, k1_zfmisc_1(k2_zfmisc_1(A_420, B_421))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.77/2.92  tff(c_1197, plain, (v4_relat_1('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_56, c_1190])).
% 7.77/2.92  tff(c_1209, plain, (![B_425, A_426]: (k7_relat_1(B_425, A_426)=B_425 | ~v4_relat_1(B_425, A_426) | ~v1_relat_1(B_425))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.77/2.92  tff(c_1215, plain, (k7_relat_1('#skF_8', '#skF_6')='#skF_8' | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_1197, c_1209])).
% 7.77/2.92  tff(c_1221, plain, (k7_relat_1('#skF_8', '#skF_6')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1145, c_1215])).
% 7.77/2.92  tff(c_1265, plain, (![C_434, A_435, B_436]: (k7_relat_1(k7_relat_1(C_434, A_435), B_436)=k1_xboole_0 | ~r1_xboole_0(A_435, B_436) | ~v1_relat_1(C_434))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.77/2.92  tff(c_1280, plain, (![B_436]: (k7_relat_1('#skF_8', B_436)=k1_xboole_0 | ~r1_xboole_0('#skF_6', B_436) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1221, c_1265])).
% 7.77/2.92  tff(c_1290, plain, (![B_437]: (k7_relat_1('#skF_8', B_437)=k1_xboole_0 | ~r1_xboole_0('#skF_6', B_437))), inference(demodulation, [status(thm), theory('equality')], [c_1145, c_1280])).
% 7.77/2.92  tff(c_1313, plain, (![B_438]: (k7_relat_1('#skF_8', B_438)=k1_xboole_0 | ~v1_xboole_0(B_438))), inference(resolution, [status(thm)], [c_1156, c_1290])).
% 7.77/2.92  tff(c_1317, plain, (k7_relat_1('#skF_8', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_1313])).
% 7.77/2.92  tff(c_1243, plain, (![A_429, B_430]: (r1_xboole_0(A_429, B_430) | ~r1_subset_1(A_429, B_430) | v1_xboole_0(B_430) | v1_xboole_0(A_429))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.77/2.92  tff(c_1630, plain, (![A_474, B_475]: (k3_xboole_0(A_474, B_475)=k1_xboole_0 | ~r1_subset_1(A_474, B_475) | v1_xboole_0(B_475) | v1_xboole_0(A_474))), inference(resolution, [status(thm)], [c_1243, c_6])).
% 7.77/2.92  tff(c_1636, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0 | v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_68, c_1630])).
% 7.77/2.92  tff(c_1640, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_76, c_72, c_1636])).
% 7.77/2.92  tff(c_1136, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_1130])).
% 7.77/2.92  tff(c_1148, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1136])).
% 7.77/2.92  tff(c_1198, plain, (v4_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_62, c_1190])).
% 7.77/2.92  tff(c_1212, plain, (k7_relat_1('#skF_7', '#skF_5')='#skF_7' | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_1198, c_1209])).
% 7.77/2.92  tff(c_1218, plain, (k7_relat_1('#skF_7', '#skF_5')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_1148, c_1212])).
% 7.77/2.92  tff(c_1283, plain, (![B_436]: (k7_relat_1('#skF_7', B_436)=k1_xboole_0 | ~r1_xboole_0('#skF_5', B_436) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1218, c_1265])).
% 7.77/2.92  tff(c_1328, plain, (![B_440]: (k7_relat_1('#skF_7', B_440)=k1_xboole_0 | ~r1_xboole_0('#skF_5', B_440))), inference(demodulation, [status(thm), theory('equality')], [c_1148, c_1283])).
% 7.77/2.92  tff(c_1351, plain, (![B_441]: (k7_relat_1('#skF_7', B_441)=k1_xboole_0 | ~v1_xboole_0(B_441))), inference(resolution, [status(thm)], [c_1156, c_1328])).
% 7.77/2.92  tff(c_1355, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_1351])).
% 7.77/2.92  tff(c_1403, plain, (![A_444, B_445, C_446]: (k9_subset_1(A_444, B_445, C_446)=k3_xboole_0(B_445, C_446) | ~m1_subset_1(C_446, k1_zfmisc_1(A_444)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.77/2.92  tff(c_1414, plain, (![B_445]: (k9_subset_1('#skF_3', B_445, '#skF_6')=k3_xboole_0(B_445, '#skF_6'))), inference(resolution, [status(thm)], [c_70, c_1403])).
% 7.77/2.92  tff(c_1558, plain, (![A_465, E_464, C_463, F_461, B_460, D_462]: (v1_funct_1(k1_tmap_1(A_465, B_460, C_463, D_462, E_464, F_461)) | ~m1_subset_1(F_461, k1_zfmisc_1(k2_zfmisc_1(D_462, B_460))) | ~v1_funct_2(F_461, D_462, B_460) | ~v1_funct_1(F_461) | ~m1_subset_1(E_464, k1_zfmisc_1(k2_zfmisc_1(C_463, B_460))) | ~v1_funct_2(E_464, C_463, B_460) | ~v1_funct_1(E_464) | ~m1_subset_1(D_462, k1_zfmisc_1(A_465)) | v1_xboole_0(D_462) | ~m1_subset_1(C_463, k1_zfmisc_1(A_465)) | v1_xboole_0(C_463) | v1_xboole_0(B_460) | v1_xboole_0(A_465))), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.77/2.92  tff(c_1560, plain, (![A_465, C_463, E_464]: (v1_funct_1(k1_tmap_1(A_465, '#skF_4', C_463, '#skF_6', E_464, '#skF_8')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_464, k1_zfmisc_1(k2_zfmisc_1(C_463, '#skF_4'))) | ~v1_funct_2(E_464, C_463, '#skF_4') | ~v1_funct_1(E_464) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_465)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_463, k1_zfmisc_1(A_465)) | v1_xboole_0(C_463) | v1_xboole_0('#skF_4') | v1_xboole_0(A_465))), inference(resolution, [status(thm)], [c_56, c_1558])).
% 7.77/2.92  tff(c_1565, plain, (![A_465, C_463, E_464]: (v1_funct_1(k1_tmap_1(A_465, '#skF_4', C_463, '#skF_6', E_464, '#skF_8')) | ~m1_subset_1(E_464, k1_zfmisc_1(k2_zfmisc_1(C_463, '#skF_4'))) | ~v1_funct_2(E_464, C_463, '#skF_4') | ~v1_funct_1(E_464) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_465)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_463, k1_zfmisc_1(A_465)) | v1_xboole_0(C_463) | v1_xboole_0('#skF_4') | v1_xboole_0(A_465))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1560])).
% 7.77/2.92  tff(c_1604, plain, (![A_469, C_470, E_471]: (v1_funct_1(k1_tmap_1(A_469, '#skF_4', C_470, '#skF_6', E_471, '#skF_8')) | ~m1_subset_1(E_471, k1_zfmisc_1(k2_zfmisc_1(C_470, '#skF_4'))) | ~v1_funct_2(E_471, C_470, '#skF_4') | ~v1_funct_1(E_471) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_469)) | ~m1_subset_1(C_470, k1_zfmisc_1(A_469)) | v1_xboole_0(C_470) | v1_xboole_0(A_469))), inference(negUnitSimplification, [status(thm)], [c_78, c_72, c_1565])).
% 7.77/2.92  tff(c_1608, plain, (![A_469]: (v1_funct_1(k1_tmap_1(A_469, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_469)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_469)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_469))), inference(resolution, [status(thm)], [c_62, c_1604])).
% 7.77/2.92  tff(c_1615, plain, (![A_469]: (v1_funct_1(k1_tmap_1(A_469, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_469)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_469)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_469))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1608])).
% 7.77/2.92  tff(c_1883, plain, (![A_506]: (v1_funct_1(k1_tmap_1(A_506, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_506)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_506)) | v1_xboole_0(A_506))), inference(negUnitSimplification, [status(thm)], [c_76, c_1615])).
% 7.77/2.92  tff(c_1886, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_74, c_1883])).
% 7.77/2.92  tff(c_1889, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1886])).
% 7.77/2.92  tff(c_1890, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_80, c_1889])).
% 7.77/2.92  tff(c_1471, plain, (![A_450, B_451, C_452, D_453]: (k2_partfun1(A_450, B_451, C_452, D_453)=k7_relat_1(C_452, D_453) | ~m1_subset_1(C_452, k1_zfmisc_1(k2_zfmisc_1(A_450, B_451))) | ~v1_funct_1(C_452))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.77/2.92  tff(c_1475, plain, (![D_453]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_453)=k7_relat_1('#skF_7', D_453) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_62, c_1471])).
% 7.77/2.92  tff(c_1481, plain, (![D_453]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_453)=k7_relat_1('#skF_7', D_453))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1475])).
% 7.77/2.92  tff(c_1473, plain, (![D_453]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_453)=k7_relat_1('#skF_8', D_453) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_56, c_1471])).
% 7.77/2.92  tff(c_1478, plain, (![D_453]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_453)=k7_relat_1('#skF_8', D_453))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1473])).
% 7.77/2.92  tff(c_2041, plain, (![C_546, D_543, B_547, E_544, F_545, A_542]: (k2_partfun1(k4_subset_1(A_542, C_546, D_543), B_547, k1_tmap_1(A_542, B_547, C_546, D_543, E_544, F_545), D_543)=F_545 | ~m1_subset_1(k1_tmap_1(A_542, B_547, C_546, D_543, E_544, F_545), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_542, C_546, D_543), B_547))) | ~v1_funct_2(k1_tmap_1(A_542, B_547, C_546, D_543, E_544, F_545), k4_subset_1(A_542, C_546, D_543), B_547) | ~v1_funct_1(k1_tmap_1(A_542, B_547, C_546, D_543, E_544, F_545)) | k2_partfun1(D_543, B_547, F_545, k9_subset_1(A_542, C_546, D_543))!=k2_partfun1(C_546, B_547, E_544, k9_subset_1(A_542, C_546, D_543)) | ~m1_subset_1(F_545, k1_zfmisc_1(k2_zfmisc_1(D_543, B_547))) | ~v1_funct_2(F_545, D_543, B_547) | ~v1_funct_1(F_545) | ~m1_subset_1(E_544, k1_zfmisc_1(k2_zfmisc_1(C_546, B_547))) | ~v1_funct_2(E_544, C_546, B_547) | ~v1_funct_1(E_544) | ~m1_subset_1(D_543, k1_zfmisc_1(A_542)) | v1_xboole_0(D_543) | ~m1_subset_1(C_546, k1_zfmisc_1(A_542)) | v1_xboole_0(C_546) | v1_xboole_0(B_547) | v1_xboole_0(A_542))), inference(cnfTransformation, [status(thm)], [f_158])).
% 7.77/2.92  tff(c_2621, plain, (![C_669, E_670, B_666, A_671, F_667, D_668]: (k2_partfun1(k4_subset_1(A_671, C_669, D_668), B_666, k1_tmap_1(A_671, B_666, C_669, D_668, E_670, F_667), D_668)=F_667 | ~v1_funct_2(k1_tmap_1(A_671, B_666, C_669, D_668, E_670, F_667), k4_subset_1(A_671, C_669, D_668), B_666) | ~v1_funct_1(k1_tmap_1(A_671, B_666, C_669, D_668, E_670, F_667)) | k2_partfun1(D_668, B_666, F_667, k9_subset_1(A_671, C_669, D_668))!=k2_partfun1(C_669, B_666, E_670, k9_subset_1(A_671, C_669, D_668)) | ~m1_subset_1(F_667, k1_zfmisc_1(k2_zfmisc_1(D_668, B_666))) | ~v1_funct_2(F_667, D_668, B_666) | ~v1_funct_1(F_667) | ~m1_subset_1(E_670, k1_zfmisc_1(k2_zfmisc_1(C_669, B_666))) | ~v1_funct_2(E_670, C_669, B_666) | ~v1_funct_1(E_670) | ~m1_subset_1(D_668, k1_zfmisc_1(A_671)) | v1_xboole_0(D_668) | ~m1_subset_1(C_669, k1_zfmisc_1(A_671)) | v1_xboole_0(C_669) | v1_xboole_0(B_666) | v1_xboole_0(A_671))), inference(resolution, [status(thm)], [c_48, c_2041])).
% 7.77/2.92  tff(c_3255, plain, (![C_741, F_739, B_738, A_743, D_740, E_742]: (k2_partfun1(k4_subset_1(A_743, C_741, D_740), B_738, k1_tmap_1(A_743, B_738, C_741, D_740, E_742, F_739), D_740)=F_739 | ~v1_funct_1(k1_tmap_1(A_743, B_738, C_741, D_740, E_742, F_739)) | k2_partfun1(D_740, B_738, F_739, k9_subset_1(A_743, C_741, D_740))!=k2_partfun1(C_741, B_738, E_742, k9_subset_1(A_743, C_741, D_740)) | ~m1_subset_1(F_739, k1_zfmisc_1(k2_zfmisc_1(D_740, B_738))) | ~v1_funct_2(F_739, D_740, B_738) | ~v1_funct_1(F_739) | ~m1_subset_1(E_742, k1_zfmisc_1(k2_zfmisc_1(C_741, B_738))) | ~v1_funct_2(E_742, C_741, B_738) | ~v1_funct_1(E_742) | ~m1_subset_1(D_740, k1_zfmisc_1(A_743)) | v1_xboole_0(D_740) | ~m1_subset_1(C_741, k1_zfmisc_1(A_743)) | v1_xboole_0(C_741) | v1_xboole_0(B_738) | v1_xboole_0(A_743))), inference(resolution, [status(thm)], [c_50, c_2621])).
% 7.77/2.92  tff(c_3259, plain, (![A_743, C_741, E_742]: (k2_partfun1(k4_subset_1(A_743, C_741, '#skF_6'), '#skF_4', k1_tmap_1(A_743, '#skF_4', C_741, '#skF_6', E_742, '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_743, '#skF_4', C_741, '#skF_6', E_742, '#skF_8')) | k2_partfun1(C_741, '#skF_4', E_742, k9_subset_1(A_743, C_741, '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1(A_743, C_741, '#skF_6')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_742, k1_zfmisc_1(k2_zfmisc_1(C_741, '#skF_4'))) | ~v1_funct_2(E_742, C_741, '#skF_4') | ~v1_funct_1(E_742) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_743)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_741, k1_zfmisc_1(A_743)) | v1_xboole_0(C_741) | v1_xboole_0('#skF_4') | v1_xboole_0(A_743))), inference(resolution, [status(thm)], [c_56, c_3255])).
% 7.77/2.92  tff(c_3265, plain, (![A_743, C_741, E_742]: (k2_partfun1(k4_subset_1(A_743, C_741, '#skF_6'), '#skF_4', k1_tmap_1(A_743, '#skF_4', C_741, '#skF_6', E_742, '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_743, '#skF_4', C_741, '#skF_6', E_742, '#skF_8')) | k2_partfun1(C_741, '#skF_4', E_742, k9_subset_1(A_743, C_741, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_743, C_741, '#skF_6')) | ~m1_subset_1(E_742, k1_zfmisc_1(k2_zfmisc_1(C_741, '#skF_4'))) | ~v1_funct_2(E_742, C_741, '#skF_4') | ~v1_funct_1(E_742) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_743)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_741, k1_zfmisc_1(A_743)) | v1_xboole_0(C_741) | v1_xboole_0('#skF_4') | v1_xboole_0(A_743))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1478, c_3259])).
% 7.77/2.92  tff(c_3484, plain, (![A_766, C_767, E_768]: (k2_partfun1(k4_subset_1(A_766, C_767, '#skF_6'), '#skF_4', k1_tmap_1(A_766, '#skF_4', C_767, '#skF_6', E_768, '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_766, '#skF_4', C_767, '#skF_6', E_768, '#skF_8')) | k2_partfun1(C_767, '#skF_4', E_768, k9_subset_1(A_766, C_767, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_766, C_767, '#skF_6')) | ~m1_subset_1(E_768, k1_zfmisc_1(k2_zfmisc_1(C_767, '#skF_4'))) | ~v1_funct_2(E_768, C_767, '#skF_4') | ~v1_funct_1(E_768) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_766)) | ~m1_subset_1(C_767, k1_zfmisc_1(A_766)) | v1_xboole_0(C_767) | v1_xboole_0(A_766))), inference(negUnitSimplification, [status(thm)], [c_78, c_72, c_3265])).
% 7.77/2.92  tff(c_3491, plain, (![A_766]: (k2_partfun1(k4_subset_1(A_766, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_766, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_766, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1(A_766, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_766, '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_766)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_766)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_766))), inference(resolution, [status(thm)], [c_62, c_3484])).
% 7.77/2.92  tff(c_3501, plain, (![A_766]: (k2_partfun1(k4_subset_1(A_766, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_766, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_766, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_766, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_766, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_766)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_766)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_766))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1481, c_3491])).
% 7.77/2.92  tff(c_3591, plain, (![A_780]: (k2_partfun1(k4_subset_1(A_780, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_780, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_780, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_780, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_780, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_780)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_780)) | v1_xboole_0(A_780))), inference(negUnitSimplification, [status(thm)], [c_76, c_3501])).
% 7.77/2.92  tff(c_126, plain, (![A_242, B_243]: (r2_hidden('#skF_2'(A_242, B_243), B_243) | r1_xboole_0(A_242, B_243))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.77/2.92  tff(c_130, plain, (![B_243, A_242]: (~v1_xboole_0(B_243) | r1_xboole_0(A_242, B_243))), inference(resolution, [status(thm)], [c_126, c_2])).
% 7.77/2.92  tff(c_104, plain, (![B_240, A_241]: (v1_relat_1(B_240) | ~m1_subset_1(B_240, k1_zfmisc_1(A_241)) | ~v1_relat_1(A_241))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.77/2.92  tff(c_107, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_4'))), inference(resolution, [status(thm)], [c_56, c_104])).
% 7.77/2.92  tff(c_119, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_107])).
% 7.77/2.92  tff(c_217, plain, (![C_266, A_267, B_268]: (v4_relat_1(C_266, A_267) | ~m1_subset_1(C_266, k1_zfmisc_1(k2_zfmisc_1(A_267, B_268))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.77/2.92  tff(c_224, plain, (v4_relat_1('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_56, c_217])).
% 7.77/2.92  tff(c_228, plain, (k7_relat_1('#skF_8', '#skF_6')='#skF_8' | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_224, c_30])).
% 7.77/2.92  tff(c_231, plain, (k7_relat_1('#skF_8', '#skF_6')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_119, c_228])).
% 7.77/2.92  tff(c_347, plain, (![C_286, A_287, B_288]: (k7_relat_1(k7_relat_1(C_286, A_287), B_288)=k1_xboole_0 | ~r1_xboole_0(A_287, B_288) | ~v1_relat_1(C_286))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.77/2.92  tff(c_365, plain, (![B_288]: (k7_relat_1('#skF_8', B_288)=k1_xboole_0 | ~r1_xboole_0('#skF_6', B_288) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_231, c_347])).
% 7.77/2.92  tff(c_420, plain, (![B_295]: (k7_relat_1('#skF_8', B_295)=k1_xboole_0 | ~r1_xboole_0('#skF_6', B_295))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_365])).
% 7.77/2.92  tff(c_443, plain, (![B_296]: (k7_relat_1('#skF_8', B_296)=k1_xboole_0 | ~v1_xboole_0(B_296))), inference(resolution, [status(thm)], [c_130, c_420])).
% 7.77/2.92  tff(c_447, plain, (k7_relat_1('#skF_8', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_443])).
% 7.77/2.92  tff(c_259, plain, (![A_271, B_272]: (r1_xboole_0(A_271, B_272) | ~r1_subset_1(A_271, B_272) | v1_xboole_0(B_272) | v1_xboole_0(A_271))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.77/2.92  tff(c_635, plain, (![A_320, B_321]: (k3_xboole_0(A_320, B_321)=k1_xboole_0 | ~r1_subset_1(A_320, B_321) | v1_xboole_0(B_321) | v1_xboole_0(A_320))), inference(resolution, [status(thm)], [c_259, c_6])).
% 7.77/2.92  tff(c_638, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0 | v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_68, c_635])).
% 7.77/2.92  tff(c_641, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_76, c_72, c_638])).
% 7.77/2.92  tff(c_110, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_104])).
% 7.77/2.92  tff(c_122, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_110])).
% 7.77/2.92  tff(c_225, plain, (v4_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_62, c_217])).
% 7.77/2.92  tff(c_234, plain, (k7_relat_1('#skF_7', '#skF_5')='#skF_7' | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_225, c_30])).
% 7.77/2.92  tff(c_237, plain, (k7_relat_1('#skF_7', '#skF_5')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_122, c_234])).
% 7.77/2.92  tff(c_362, plain, (![B_288]: (k7_relat_1('#skF_7', B_288)=k1_xboole_0 | ~r1_xboole_0('#skF_5', B_288) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_237, c_347])).
% 7.77/2.92  tff(c_372, plain, (![B_289]: (k7_relat_1('#skF_7', B_289)=k1_xboole_0 | ~r1_xboole_0('#skF_5', B_289))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_362])).
% 7.77/2.92  tff(c_395, plain, (![B_290]: (k7_relat_1('#skF_7', B_290)=k1_xboole_0 | ~v1_xboole_0(B_290))), inference(resolution, [status(thm)], [c_130, c_372])).
% 7.77/2.92  tff(c_399, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_395])).
% 7.77/2.92  tff(c_409, plain, (![A_291, B_292, C_293, D_294]: (k2_partfun1(A_291, B_292, C_293, D_294)=k7_relat_1(C_293, D_294) | ~m1_subset_1(C_293, k1_zfmisc_1(k2_zfmisc_1(A_291, B_292))) | ~v1_funct_1(C_293))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.77/2.92  tff(c_413, plain, (![D_294]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_294)=k7_relat_1('#skF_7', D_294) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_62, c_409])).
% 7.77/2.92  tff(c_419, plain, (![D_294]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_294)=k7_relat_1('#skF_7', D_294))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_413])).
% 7.77/2.92  tff(c_411, plain, (![D_294]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_294)=k7_relat_1('#skF_8', D_294) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_56, c_409])).
% 7.77/2.92  tff(c_416, plain, (![D_294]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_294)=k7_relat_1('#skF_8', D_294))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_411])).
% 7.77/2.92  tff(c_286, plain, (![A_278, B_279, C_280]: (k9_subset_1(A_278, B_279, C_280)=k3_xboole_0(B_279, C_280) | ~m1_subset_1(C_280, k1_zfmisc_1(A_278)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.77/2.92  tff(c_297, plain, (![B_279]: (k9_subset_1('#skF_3', B_279, '#skF_6')=k3_xboole_0(B_279, '#skF_6'))), inference(resolution, [status(thm)], [c_70, c_286])).
% 7.77/2.92  tff(c_54, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')!='#skF_8' | k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')!='#skF_7' | k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_234])).
% 7.77/2.92  tff(c_94, plain, (k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_54])).
% 7.77/2.92  tff(c_310, plain, (k2_partfun1('#skF_5', '#skF_4', '#skF_7', k3_xboole_0('#skF_5', '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k3_xboole_0('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_297, c_297, c_94])).
% 7.77/2.92  tff(c_1071, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_447, c_641, c_399, c_641, c_419, c_416, c_310])).
% 7.77/2.92  tff(c_1072, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')!='#skF_7' | k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')!='#skF_8'), inference(splitRight, [status(thm)], [c_54])).
% 7.77/2.92  tff(c_1122, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')!='#skF_8'), inference(splitLeft, [status(thm)], [c_1072])).
% 7.77/2.92  tff(c_3602, plain, (~v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3591, c_1122])).
% 7.77/2.92  tff(c_3616, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_1317, c_1640, c_1355, c_1640, c_1414, c_1414, c_1890, c_3602])).
% 7.77/2.92  tff(c_3618, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_3616])).
% 7.77/2.92  tff(c_3619, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_1072])).
% 7.77/2.92  tff(c_6596, plain, (~v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6587, c_3619])).
% 7.77/2.92  tff(c_6607, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_3872, c_4116, c_3819, c_4116, c_3919, c_3919, c_4801, c_6596])).
% 7.77/2.92  tff(c_6609, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_6607])).
% 7.77/2.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.77/2.92  
% 7.77/2.92  Inference rules
% 7.77/2.92  ----------------------
% 7.77/2.92  #Ref     : 0
% 7.77/2.92  #Sup     : 1323
% 7.77/2.92  #Fact    : 0
% 7.77/2.92  #Define  : 0
% 7.77/2.92  #Split   : 44
% 7.77/2.92  #Chain   : 0
% 7.77/2.92  #Close   : 0
% 7.77/2.92  
% 7.77/2.92  Ordering : KBO
% 7.77/2.92  
% 7.77/2.92  Simplification rules
% 7.77/2.92  ----------------------
% 7.77/2.92  #Subsume      : 209
% 7.77/2.92  #Demod        : 794
% 7.77/2.92  #Tautology    : 570
% 7.77/2.92  #SimpNegUnit  : 292
% 7.77/2.92  #BackRed      : 4
% 7.77/2.92  
% 7.77/2.92  #Partial instantiations: 0
% 7.77/2.92  #Strategies tried      : 1
% 7.77/2.92  
% 7.77/2.92  Timing (in seconds)
% 7.77/2.92  ----------------------
% 7.77/2.93  Preprocessing        : 0.39
% 7.77/2.93  Parsing              : 0.19
% 7.77/2.93  CNF conversion       : 0.06
% 7.77/2.93  Main loop            : 1.76
% 7.77/2.93  Inferencing          : 0.63
% 7.77/2.93  Reduction            : 0.56
% 7.77/2.93  Demodulation         : 0.40
% 7.77/2.93  BG Simplification    : 0.06
% 7.77/2.93  Subsumption          : 0.41
% 7.77/2.93  Abstraction          : 0.07
% 7.77/2.93  MUC search           : 0.00
% 7.77/2.93  Cooper               : 0.00
% 7.77/2.93  Total                : 2.23
% 7.77/2.93  Index Insertion      : 0.00
% 7.77/2.93  Index Deletion       : 0.00
% 7.77/2.93  Index Matching       : 0.00
% 7.77/2.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
