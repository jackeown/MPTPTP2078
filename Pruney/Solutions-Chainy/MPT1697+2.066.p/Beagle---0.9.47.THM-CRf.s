%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:19 EST 2020

% Result     : Theorem 7.81s
% Output     : CNFRefutation 7.98s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 504 expanded)
%              Number of leaves         :   39 ( 200 expanded)
%              Depth                    :   12
%              Number of atoms          :  597 (2774 expanded)
%              Number of equality atoms :  107 ( 504 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_197,negated_conjecture,(
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

tff(f_31,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_57,axiom,(
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

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_155,axiom,(
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

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_121,axiom,(
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

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_6,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_83,plain,(
    ! [C_220,A_221,B_222] :
      ( v1_relat_1(C_220)
      | ~ m1_subset_1(C_220,k1_zfmisc_1(k2_zfmisc_1(A_221,B_222))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_90,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_83])).

tff(c_595,plain,(
    ! [C_288,A_289,B_290] :
      ( v4_relat_1(C_288,A_289)
      | ~ m1_subset_1(C_288,k1_zfmisc_1(k2_zfmisc_1(A_289,B_290))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_602,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_595])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( k7_relat_1(B_11,A_10) = B_11
      | ~ v4_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_606,plain,
    ( k7_relat_1('#skF_6','#skF_4') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_602,c_12])).

tff(c_609,plain,(
    k7_relat_1('#skF_6','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_606])).

tff(c_669,plain,(
    ! [C_301,A_302,B_303] :
      ( k7_relat_1(k7_relat_1(C_301,A_302),B_303) = k1_xboole_0
      | ~ r1_xboole_0(A_302,B_303)
      | ~ v1_relat_1(C_301) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_687,plain,(
    ! [B_303] :
      ( k7_relat_1('#skF_6',B_303) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_303)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_609,c_669])).

tff(c_749,plain,(
    ! [B_308] :
      ( k7_relat_1('#skF_6',B_308) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_308) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_687])).

tff(c_766,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_749])).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_52,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_637,plain,(
    ! [A_294,B_295] :
      ( r1_xboole_0(A_294,B_295)
      | ~ r1_subset_1(A_294,B_295)
      | v1_xboole_0(B_295)
      | v1_xboole_0(A_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2983,plain,(
    ! [A_709,B_710] :
      ( k3_xboole_0(A_709,B_710) = k1_xboole_0
      | ~ r1_subset_1(A_709,B_710)
      | v1_xboole_0(B_710)
      | v1_xboole_0(A_709) ) ),
    inference(resolution,[status(thm)],[c_637,c_2])).

tff(c_2989,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_2983])).

tff(c_2993,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_56,c_2989])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_91,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_83])).

tff(c_603,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_595])).

tff(c_612,plain,
    ( k7_relat_1('#skF_5','#skF_3') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_603,c_12])).

tff(c_615,plain,(
    k7_relat_1('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_612])).

tff(c_684,plain,(
    ! [B_303] :
      ( k7_relat_1('#skF_5',B_303) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_303)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_615,c_669])).

tff(c_713,plain,(
    ! [B_306] :
      ( k7_relat_1('#skF_5',B_306) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_306) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_684])).

tff(c_730,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_713])).

tff(c_656,plain,(
    ! [A_298,B_299,C_300] :
      ( k9_subset_1(A_298,B_299,C_300) = k3_xboole_0(B_299,C_300)
      | ~ m1_subset_1(C_300,k1_zfmisc_1(A_298)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_668,plain,(
    ! [B_299] : k9_subset_1('#skF_1',B_299,'#skF_4') = k3_xboole_0(B_299,'#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_656])).

tff(c_50,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_48,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_44,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_42,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_3051,plain,(
    ! [C_724,A_722,B_721,E_719,D_723,F_720] :
      ( v1_funct_1(k1_tmap_1(A_722,B_721,C_724,D_723,E_719,F_720))
      | ~ m1_subset_1(F_720,k1_zfmisc_1(k2_zfmisc_1(D_723,B_721)))
      | ~ v1_funct_2(F_720,D_723,B_721)
      | ~ v1_funct_1(F_720)
      | ~ m1_subset_1(E_719,k1_zfmisc_1(k2_zfmisc_1(C_724,B_721)))
      | ~ v1_funct_2(E_719,C_724,B_721)
      | ~ v1_funct_1(E_719)
      | ~ m1_subset_1(D_723,k1_zfmisc_1(A_722))
      | v1_xboole_0(D_723)
      | ~ m1_subset_1(C_724,k1_zfmisc_1(A_722))
      | v1_xboole_0(C_724)
      | v1_xboole_0(B_721)
      | v1_xboole_0(A_722) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_3053,plain,(
    ! [A_722,C_724,E_719] :
      ( v1_funct_1(k1_tmap_1(A_722,'#skF_2',C_724,'#skF_4',E_719,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_719,k1_zfmisc_1(k2_zfmisc_1(C_724,'#skF_2')))
      | ~ v1_funct_2(E_719,C_724,'#skF_2')
      | ~ v1_funct_1(E_719)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_722))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_724,k1_zfmisc_1(A_722))
      | v1_xboole_0(C_724)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_722) ) ),
    inference(resolution,[status(thm)],[c_40,c_3051])).

tff(c_3058,plain,(
    ! [A_722,C_724,E_719] :
      ( v1_funct_1(k1_tmap_1(A_722,'#skF_2',C_724,'#skF_4',E_719,'#skF_6'))
      | ~ m1_subset_1(E_719,k1_zfmisc_1(k2_zfmisc_1(C_724,'#skF_2')))
      | ~ v1_funct_2(E_719,C_724,'#skF_2')
      | ~ v1_funct_1(E_719)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_722))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_724,k1_zfmisc_1(A_722))
      | v1_xboole_0(C_724)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_722) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_3053])).

tff(c_3248,plain,(
    ! [A_762,C_763,E_764] :
      ( v1_funct_1(k1_tmap_1(A_762,'#skF_2',C_763,'#skF_4',E_764,'#skF_6'))
      | ~ m1_subset_1(E_764,k1_zfmisc_1(k2_zfmisc_1(C_763,'#skF_2')))
      | ~ v1_funct_2(E_764,C_763,'#skF_2')
      | ~ v1_funct_1(E_764)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_762))
      | ~ m1_subset_1(C_763,k1_zfmisc_1(A_762))
      | v1_xboole_0(C_763)
      | v1_xboole_0(A_762) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_3058])).

tff(c_3255,plain,(
    ! [A_762] :
      ( v1_funct_1(k1_tmap_1(A_762,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_762))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_762))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_762) ) ),
    inference(resolution,[status(thm)],[c_46,c_3248])).

tff(c_3265,plain,(
    ! [A_762] :
      ( v1_funct_1(k1_tmap_1(A_762,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_762))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_762))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_762) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_3255])).

tff(c_3279,plain,(
    ! [A_766] :
      ( v1_funct_1(k1_tmap_1(A_766,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_766))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_766))
      | v1_xboole_0(A_766) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_3265])).

tff(c_3282,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_3279])).

tff(c_3285,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3282])).

tff(c_3286,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_3285])).

tff(c_800,plain,(
    ! [A_310,B_311,C_312,D_313] :
      ( k2_partfun1(A_310,B_311,C_312,D_313) = k7_relat_1(C_312,D_313)
      | ~ m1_subset_1(C_312,k1_zfmisc_1(k2_zfmisc_1(A_310,B_311)))
      | ~ v1_funct_1(C_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_804,plain,(
    ! [D_313] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_313) = k7_relat_1('#skF_5',D_313)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_46,c_800])).

tff(c_810,plain,(
    ! [D_313] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_313) = k7_relat_1('#skF_5',D_313) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_804])).

tff(c_802,plain,(
    ! [D_313] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_313) = k7_relat_1('#skF_6',D_313)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_40,c_800])).

tff(c_807,plain,(
    ! [D_313] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_313) = k7_relat_1('#skF_6',D_313) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_802])).

tff(c_34,plain,(
    ! [E_155,B_152,F_156,C_153,D_154,A_151] :
      ( v1_funct_2(k1_tmap_1(A_151,B_152,C_153,D_154,E_155,F_156),k4_subset_1(A_151,C_153,D_154),B_152)
      | ~ m1_subset_1(F_156,k1_zfmisc_1(k2_zfmisc_1(D_154,B_152)))
      | ~ v1_funct_2(F_156,D_154,B_152)
      | ~ v1_funct_1(F_156)
      | ~ m1_subset_1(E_155,k1_zfmisc_1(k2_zfmisc_1(C_153,B_152)))
      | ~ v1_funct_2(E_155,C_153,B_152)
      | ~ v1_funct_1(E_155)
      | ~ m1_subset_1(D_154,k1_zfmisc_1(A_151))
      | v1_xboole_0(D_154)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(A_151))
      | v1_xboole_0(C_153)
      | v1_xboole_0(B_152)
      | v1_xboole_0(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_32,plain,(
    ! [E_155,B_152,F_156,C_153,D_154,A_151] :
      ( m1_subset_1(k1_tmap_1(A_151,B_152,C_153,D_154,E_155,F_156),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_151,C_153,D_154),B_152)))
      | ~ m1_subset_1(F_156,k1_zfmisc_1(k2_zfmisc_1(D_154,B_152)))
      | ~ v1_funct_2(F_156,D_154,B_152)
      | ~ v1_funct_1(F_156)
      | ~ m1_subset_1(E_155,k1_zfmisc_1(k2_zfmisc_1(C_153,B_152)))
      | ~ v1_funct_2(E_155,C_153,B_152)
      | ~ v1_funct_1(E_155)
      | ~ m1_subset_1(D_154,k1_zfmisc_1(A_151))
      | v1_xboole_0(D_154)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(A_151))
      | v1_xboole_0(C_153)
      | v1_xboole_0(B_152)
      | v1_xboole_0(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_3287,plain,(
    ! [E_771,C_767,D_772,B_770,F_768,A_769] :
      ( k2_partfun1(k4_subset_1(A_769,C_767,D_772),B_770,k1_tmap_1(A_769,B_770,C_767,D_772,E_771,F_768),C_767) = E_771
      | ~ m1_subset_1(k1_tmap_1(A_769,B_770,C_767,D_772,E_771,F_768),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_769,C_767,D_772),B_770)))
      | ~ v1_funct_2(k1_tmap_1(A_769,B_770,C_767,D_772,E_771,F_768),k4_subset_1(A_769,C_767,D_772),B_770)
      | ~ v1_funct_1(k1_tmap_1(A_769,B_770,C_767,D_772,E_771,F_768))
      | k2_partfun1(D_772,B_770,F_768,k9_subset_1(A_769,C_767,D_772)) != k2_partfun1(C_767,B_770,E_771,k9_subset_1(A_769,C_767,D_772))
      | ~ m1_subset_1(F_768,k1_zfmisc_1(k2_zfmisc_1(D_772,B_770)))
      | ~ v1_funct_2(F_768,D_772,B_770)
      | ~ v1_funct_1(F_768)
      | ~ m1_subset_1(E_771,k1_zfmisc_1(k2_zfmisc_1(C_767,B_770)))
      | ~ v1_funct_2(E_771,C_767,B_770)
      | ~ v1_funct_1(E_771)
      | ~ m1_subset_1(D_772,k1_zfmisc_1(A_769))
      | v1_xboole_0(D_772)
      | ~ m1_subset_1(C_767,k1_zfmisc_1(A_769))
      | v1_xboole_0(C_767)
      | v1_xboole_0(B_770)
      | v1_xboole_0(A_769) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_3751,plain,(
    ! [F_871,A_873,E_870,D_874,B_872,C_875] :
      ( k2_partfun1(k4_subset_1(A_873,C_875,D_874),B_872,k1_tmap_1(A_873,B_872,C_875,D_874,E_870,F_871),C_875) = E_870
      | ~ v1_funct_2(k1_tmap_1(A_873,B_872,C_875,D_874,E_870,F_871),k4_subset_1(A_873,C_875,D_874),B_872)
      | ~ v1_funct_1(k1_tmap_1(A_873,B_872,C_875,D_874,E_870,F_871))
      | k2_partfun1(D_874,B_872,F_871,k9_subset_1(A_873,C_875,D_874)) != k2_partfun1(C_875,B_872,E_870,k9_subset_1(A_873,C_875,D_874))
      | ~ m1_subset_1(F_871,k1_zfmisc_1(k2_zfmisc_1(D_874,B_872)))
      | ~ v1_funct_2(F_871,D_874,B_872)
      | ~ v1_funct_1(F_871)
      | ~ m1_subset_1(E_870,k1_zfmisc_1(k2_zfmisc_1(C_875,B_872)))
      | ~ v1_funct_2(E_870,C_875,B_872)
      | ~ v1_funct_1(E_870)
      | ~ m1_subset_1(D_874,k1_zfmisc_1(A_873))
      | v1_xboole_0(D_874)
      | ~ m1_subset_1(C_875,k1_zfmisc_1(A_873))
      | v1_xboole_0(C_875)
      | v1_xboole_0(B_872)
      | v1_xboole_0(A_873) ) ),
    inference(resolution,[status(thm)],[c_32,c_3287])).

tff(c_4166,plain,(
    ! [B_943,F_942,E_941,C_946,D_945,A_944] :
      ( k2_partfun1(k4_subset_1(A_944,C_946,D_945),B_943,k1_tmap_1(A_944,B_943,C_946,D_945,E_941,F_942),C_946) = E_941
      | ~ v1_funct_1(k1_tmap_1(A_944,B_943,C_946,D_945,E_941,F_942))
      | k2_partfun1(D_945,B_943,F_942,k9_subset_1(A_944,C_946,D_945)) != k2_partfun1(C_946,B_943,E_941,k9_subset_1(A_944,C_946,D_945))
      | ~ m1_subset_1(F_942,k1_zfmisc_1(k2_zfmisc_1(D_945,B_943)))
      | ~ v1_funct_2(F_942,D_945,B_943)
      | ~ v1_funct_1(F_942)
      | ~ m1_subset_1(E_941,k1_zfmisc_1(k2_zfmisc_1(C_946,B_943)))
      | ~ v1_funct_2(E_941,C_946,B_943)
      | ~ v1_funct_1(E_941)
      | ~ m1_subset_1(D_945,k1_zfmisc_1(A_944))
      | v1_xboole_0(D_945)
      | ~ m1_subset_1(C_946,k1_zfmisc_1(A_944))
      | v1_xboole_0(C_946)
      | v1_xboole_0(B_943)
      | v1_xboole_0(A_944) ) ),
    inference(resolution,[status(thm)],[c_34,c_3751])).

tff(c_4170,plain,(
    ! [A_944,C_946,E_941] :
      ( k2_partfun1(k4_subset_1(A_944,C_946,'#skF_4'),'#skF_2',k1_tmap_1(A_944,'#skF_2',C_946,'#skF_4',E_941,'#skF_6'),C_946) = E_941
      | ~ v1_funct_1(k1_tmap_1(A_944,'#skF_2',C_946,'#skF_4',E_941,'#skF_6'))
      | k2_partfun1(C_946,'#skF_2',E_941,k9_subset_1(A_944,C_946,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_944,C_946,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_941,k1_zfmisc_1(k2_zfmisc_1(C_946,'#skF_2')))
      | ~ v1_funct_2(E_941,C_946,'#skF_2')
      | ~ v1_funct_1(E_941)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_944))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_946,k1_zfmisc_1(A_944))
      | v1_xboole_0(C_946)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_944) ) ),
    inference(resolution,[status(thm)],[c_40,c_4166])).

tff(c_4176,plain,(
    ! [A_944,C_946,E_941] :
      ( k2_partfun1(k4_subset_1(A_944,C_946,'#skF_4'),'#skF_2',k1_tmap_1(A_944,'#skF_2',C_946,'#skF_4',E_941,'#skF_6'),C_946) = E_941
      | ~ v1_funct_1(k1_tmap_1(A_944,'#skF_2',C_946,'#skF_4',E_941,'#skF_6'))
      | k2_partfun1(C_946,'#skF_2',E_941,k9_subset_1(A_944,C_946,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_944,C_946,'#skF_4'))
      | ~ m1_subset_1(E_941,k1_zfmisc_1(k2_zfmisc_1(C_946,'#skF_2')))
      | ~ v1_funct_2(E_941,C_946,'#skF_2')
      | ~ v1_funct_1(E_941)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_944))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_946,k1_zfmisc_1(A_944))
      | v1_xboole_0(C_946)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_944) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_807,c_4170])).

tff(c_4665,plain,(
    ! [A_1032,C_1033,E_1034] :
      ( k2_partfun1(k4_subset_1(A_1032,C_1033,'#skF_4'),'#skF_2',k1_tmap_1(A_1032,'#skF_2',C_1033,'#skF_4',E_1034,'#skF_6'),C_1033) = E_1034
      | ~ v1_funct_1(k1_tmap_1(A_1032,'#skF_2',C_1033,'#skF_4',E_1034,'#skF_6'))
      | k2_partfun1(C_1033,'#skF_2',E_1034,k9_subset_1(A_1032,C_1033,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1032,C_1033,'#skF_4'))
      | ~ m1_subset_1(E_1034,k1_zfmisc_1(k2_zfmisc_1(C_1033,'#skF_2')))
      | ~ v1_funct_2(E_1034,C_1033,'#skF_2')
      | ~ v1_funct_1(E_1034)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1032))
      | ~ m1_subset_1(C_1033,k1_zfmisc_1(A_1032))
      | v1_xboole_0(C_1033)
      | v1_xboole_0(A_1032) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_4176])).

tff(c_4672,plain,(
    ! [A_1032] :
      ( k2_partfun1(k4_subset_1(A_1032,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1032,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1032,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1032,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1032,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1032))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1032))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1032) ) ),
    inference(resolution,[status(thm)],[c_46,c_4665])).

tff(c_4682,plain,(
    ! [A_1032] :
      ( k2_partfun1(k4_subset_1(A_1032,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1032,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1032,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1032,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1032,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1032))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1032))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1032) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_810,c_4672])).

tff(c_4702,plain,(
    ! [A_1041] :
      ( k2_partfun1(k4_subset_1(A_1041,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1041,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1041,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1041,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1041,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1041))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1041))
      | v1_xboole_0(A_1041) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_4682])).

tff(c_1025,plain,(
    ! [A_327,B_328] :
      ( k3_xboole_0(A_327,B_328) = k1_xboole_0
      | ~ r1_subset_1(A_327,B_328)
      | v1_xboole_0(B_328)
      | v1_xboole_0(A_327) ) ),
    inference(resolution,[status(thm)],[c_637,c_2])).

tff(c_1031,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_1025])).

tff(c_1035,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_56,c_1031])).

tff(c_1082,plain,(
    ! [C_342,B_339,D_341,E_337,F_338,A_340] :
      ( v1_funct_1(k1_tmap_1(A_340,B_339,C_342,D_341,E_337,F_338))
      | ~ m1_subset_1(F_338,k1_zfmisc_1(k2_zfmisc_1(D_341,B_339)))
      | ~ v1_funct_2(F_338,D_341,B_339)
      | ~ v1_funct_1(F_338)
      | ~ m1_subset_1(E_337,k1_zfmisc_1(k2_zfmisc_1(C_342,B_339)))
      | ~ v1_funct_2(E_337,C_342,B_339)
      | ~ v1_funct_1(E_337)
      | ~ m1_subset_1(D_341,k1_zfmisc_1(A_340))
      | v1_xboole_0(D_341)
      | ~ m1_subset_1(C_342,k1_zfmisc_1(A_340))
      | v1_xboole_0(C_342)
      | v1_xboole_0(B_339)
      | v1_xboole_0(A_340) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_1084,plain,(
    ! [A_340,C_342,E_337] :
      ( v1_funct_1(k1_tmap_1(A_340,'#skF_2',C_342,'#skF_4',E_337,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_337,k1_zfmisc_1(k2_zfmisc_1(C_342,'#skF_2')))
      | ~ v1_funct_2(E_337,C_342,'#skF_2')
      | ~ v1_funct_1(E_337)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_340))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_342,k1_zfmisc_1(A_340))
      | v1_xboole_0(C_342)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_340) ) ),
    inference(resolution,[status(thm)],[c_40,c_1082])).

tff(c_1089,plain,(
    ! [A_340,C_342,E_337] :
      ( v1_funct_1(k1_tmap_1(A_340,'#skF_2',C_342,'#skF_4',E_337,'#skF_6'))
      | ~ m1_subset_1(E_337,k1_zfmisc_1(k2_zfmisc_1(C_342,'#skF_2')))
      | ~ v1_funct_2(E_337,C_342,'#skF_2')
      | ~ v1_funct_1(E_337)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_340))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_342,k1_zfmisc_1(A_340))
      | v1_xboole_0(C_342)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_340) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_1084])).

tff(c_1096,plain,(
    ! [A_343,C_344,E_345] :
      ( v1_funct_1(k1_tmap_1(A_343,'#skF_2',C_344,'#skF_4',E_345,'#skF_6'))
      | ~ m1_subset_1(E_345,k1_zfmisc_1(k2_zfmisc_1(C_344,'#skF_2')))
      | ~ v1_funct_2(E_345,C_344,'#skF_2')
      | ~ v1_funct_1(E_345)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_343))
      | ~ m1_subset_1(C_344,k1_zfmisc_1(A_343))
      | v1_xboole_0(C_344)
      | v1_xboole_0(A_343) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_1089])).

tff(c_1100,plain,(
    ! [A_343] :
      ( v1_funct_1(k1_tmap_1(A_343,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_343))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_343))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_343) ) ),
    inference(resolution,[status(thm)],[c_46,c_1096])).

tff(c_1107,plain,(
    ! [A_343] :
      ( v1_funct_1(k1_tmap_1(A_343,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_343))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_343))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_343) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_1100])).

tff(c_1150,plain,(
    ! [A_361] :
      ( v1_funct_1(k1_tmap_1(A_361,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_361))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_361))
      | v1_xboole_0(A_361) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1107])).

tff(c_1153,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_1150])).

tff(c_1156,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1153])).

tff(c_1157,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1156])).

tff(c_1362,plain,(
    ! [F_391,B_393,A_392,C_390,E_394,D_395] :
      ( k2_partfun1(k4_subset_1(A_392,C_390,D_395),B_393,k1_tmap_1(A_392,B_393,C_390,D_395,E_394,F_391),D_395) = F_391
      | ~ m1_subset_1(k1_tmap_1(A_392,B_393,C_390,D_395,E_394,F_391),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_392,C_390,D_395),B_393)))
      | ~ v1_funct_2(k1_tmap_1(A_392,B_393,C_390,D_395,E_394,F_391),k4_subset_1(A_392,C_390,D_395),B_393)
      | ~ v1_funct_1(k1_tmap_1(A_392,B_393,C_390,D_395,E_394,F_391))
      | k2_partfun1(D_395,B_393,F_391,k9_subset_1(A_392,C_390,D_395)) != k2_partfun1(C_390,B_393,E_394,k9_subset_1(A_392,C_390,D_395))
      | ~ m1_subset_1(F_391,k1_zfmisc_1(k2_zfmisc_1(D_395,B_393)))
      | ~ v1_funct_2(F_391,D_395,B_393)
      | ~ v1_funct_1(F_391)
      | ~ m1_subset_1(E_394,k1_zfmisc_1(k2_zfmisc_1(C_390,B_393)))
      | ~ v1_funct_2(E_394,C_390,B_393)
      | ~ v1_funct_1(E_394)
      | ~ m1_subset_1(D_395,k1_zfmisc_1(A_392))
      | v1_xboole_0(D_395)
      | ~ m1_subset_1(C_390,k1_zfmisc_1(A_392))
      | v1_xboole_0(C_390)
      | v1_xboole_0(B_393)
      | v1_xboole_0(A_392) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1832,plain,(
    ! [C_507,A_505,E_502,B_504,F_503,D_506] :
      ( k2_partfun1(k4_subset_1(A_505,C_507,D_506),B_504,k1_tmap_1(A_505,B_504,C_507,D_506,E_502,F_503),D_506) = F_503
      | ~ v1_funct_2(k1_tmap_1(A_505,B_504,C_507,D_506,E_502,F_503),k4_subset_1(A_505,C_507,D_506),B_504)
      | ~ v1_funct_1(k1_tmap_1(A_505,B_504,C_507,D_506,E_502,F_503))
      | k2_partfun1(D_506,B_504,F_503,k9_subset_1(A_505,C_507,D_506)) != k2_partfun1(C_507,B_504,E_502,k9_subset_1(A_505,C_507,D_506))
      | ~ m1_subset_1(F_503,k1_zfmisc_1(k2_zfmisc_1(D_506,B_504)))
      | ~ v1_funct_2(F_503,D_506,B_504)
      | ~ v1_funct_1(F_503)
      | ~ m1_subset_1(E_502,k1_zfmisc_1(k2_zfmisc_1(C_507,B_504)))
      | ~ v1_funct_2(E_502,C_507,B_504)
      | ~ v1_funct_1(E_502)
      | ~ m1_subset_1(D_506,k1_zfmisc_1(A_505))
      | v1_xboole_0(D_506)
      | ~ m1_subset_1(C_507,k1_zfmisc_1(A_505))
      | v1_xboole_0(C_507)
      | v1_xboole_0(B_504)
      | v1_xboole_0(A_505) ) ),
    inference(resolution,[status(thm)],[c_32,c_1362])).

tff(c_2162,plain,(
    ! [C_562,D_561,F_558,B_559,A_560,E_557] :
      ( k2_partfun1(k4_subset_1(A_560,C_562,D_561),B_559,k1_tmap_1(A_560,B_559,C_562,D_561,E_557,F_558),D_561) = F_558
      | ~ v1_funct_1(k1_tmap_1(A_560,B_559,C_562,D_561,E_557,F_558))
      | k2_partfun1(D_561,B_559,F_558,k9_subset_1(A_560,C_562,D_561)) != k2_partfun1(C_562,B_559,E_557,k9_subset_1(A_560,C_562,D_561))
      | ~ m1_subset_1(F_558,k1_zfmisc_1(k2_zfmisc_1(D_561,B_559)))
      | ~ v1_funct_2(F_558,D_561,B_559)
      | ~ v1_funct_1(F_558)
      | ~ m1_subset_1(E_557,k1_zfmisc_1(k2_zfmisc_1(C_562,B_559)))
      | ~ v1_funct_2(E_557,C_562,B_559)
      | ~ v1_funct_1(E_557)
      | ~ m1_subset_1(D_561,k1_zfmisc_1(A_560))
      | v1_xboole_0(D_561)
      | ~ m1_subset_1(C_562,k1_zfmisc_1(A_560))
      | v1_xboole_0(C_562)
      | v1_xboole_0(B_559)
      | v1_xboole_0(A_560) ) ),
    inference(resolution,[status(thm)],[c_34,c_1832])).

tff(c_2166,plain,(
    ! [A_560,C_562,E_557] :
      ( k2_partfun1(k4_subset_1(A_560,C_562,'#skF_4'),'#skF_2',k1_tmap_1(A_560,'#skF_2',C_562,'#skF_4',E_557,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_560,'#skF_2',C_562,'#skF_4',E_557,'#skF_6'))
      | k2_partfun1(C_562,'#skF_2',E_557,k9_subset_1(A_560,C_562,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_560,C_562,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_557,k1_zfmisc_1(k2_zfmisc_1(C_562,'#skF_2')))
      | ~ v1_funct_2(E_557,C_562,'#skF_2')
      | ~ v1_funct_1(E_557)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_560))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_562,k1_zfmisc_1(A_560))
      | v1_xboole_0(C_562)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_560) ) ),
    inference(resolution,[status(thm)],[c_40,c_2162])).

tff(c_2172,plain,(
    ! [A_560,C_562,E_557] :
      ( k2_partfun1(k4_subset_1(A_560,C_562,'#skF_4'),'#skF_2',k1_tmap_1(A_560,'#skF_2',C_562,'#skF_4',E_557,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_560,'#skF_2',C_562,'#skF_4',E_557,'#skF_6'))
      | k2_partfun1(C_562,'#skF_2',E_557,k9_subset_1(A_560,C_562,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_560,C_562,'#skF_4'))
      | ~ m1_subset_1(E_557,k1_zfmisc_1(k2_zfmisc_1(C_562,'#skF_2')))
      | ~ v1_funct_2(E_557,C_562,'#skF_2')
      | ~ v1_funct_1(E_557)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_560))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_562,k1_zfmisc_1(A_560))
      | v1_xboole_0(C_562)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_560) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_807,c_2166])).

tff(c_2797,plain,(
    ! [A_697,C_698,E_699] :
      ( k2_partfun1(k4_subset_1(A_697,C_698,'#skF_4'),'#skF_2',k1_tmap_1(A_697,'#skF_2',C_698,'#skF_4',E_699,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_697,'#skF_2',C_698,'#skF_4',E_699,'#skF_6'))
      | k2_partfun1(C_698,'#skF_2',E_699,k9_subset_1(A_697,C_698,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_697,C_698,'#skF_4'))
      | ~ m1_subset_1(E_699,k1_zfmisc_1(k2_zfmisc_1(C_698,'#skF_2')))
      | ~ v1_funct_2(E_699,C_698,'#skF_2')
      | ~ v1_funct_1(E_699)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_697))
      | ~ m1_subset_1(C_698,k1_zfmisc_1(A_697))
      | v1_xboole_0(C_698)
      | v1_xboole_0(A_697) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_2172])).

tff(c_2804,plain,(
    ! [A_697] :
      ( k2_partfun1(k4_subset_1(A_697,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_697,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_697,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_697,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_697,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_697))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_697))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_697) ) ),
    inference(resolution,[status(thm)],[c_46,c_2797])).

tff(c_2814,plain,(
    ! [A_697] :
      ( k2_partfun1(k4_subset_1(A_697,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_697,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_697,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_697,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_697,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_697))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_697))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_697) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_810,c_2804])).

tff(c_2816,plain,(
    ! [A_700] :
      ( k2_partfun1(k4_subset_1(A_700,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_700,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_700,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_700,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_700,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_700))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_700))
      | v1_xboole_0(A_700) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2814])).

tff(c_93,plain,(
    ! [C_223,A_224,B_225] :
      ( v4_relat_1(C_223,A_224)
      | ~ m1_subset_1(C_223,k1_zfmisc_1(k2_zfmisc_1(A_224,B_225))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_100,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_93])).

tff(c_111,plain,(
    ! [B_229,A_230] :
      ( k7_relat_1(B_229,A_230) = B_229
      | ~ v4_relat_1(B_229,A_230)
      | ~ v1_relat_1(B_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_117,plain,
    ( k7_relat_1('#skF_6','#skF_4') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_100,c_111])).

tff(c_123,plain,(
    k7_relat_1('#skF_6','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_117])).

tff(c_151,plain,(
    ! [C_235,A_236,B_237] :
      ( k7_relat_1(k7_relat_1(C_235,A_236),B_237) = k1_xboole_0
      | ~ r1_xboole_0(A_236,B_237)
      | ~ v1_relat_1(C_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_169,plain,(
    ! [B_237] :
      ( k7_relat_1('#skF_6',B_237) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_237)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_151])).

tff(c_203,plain,(
    ! [B_239] :
      ( k7_relat_1('#skF_6',B_239) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_239) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_169])).

tff(c_220,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_203])).

tff(c_132,plain,(
    ! [A_231,B_232] :
      ( r1_xboole_0(A_231,B_232)
      | ~ r1_subset_1(A_231,B_232)
      | v1_xboole_0(B_232)
      | v1_xboole_0(A_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_532,plain,(
    ! [A_270,B_271] :
      ( k3_xboole_0(A_270,B_271) = k1_xboole_0
      | ~ r1_subset_1(A_270,B_271)
      | v1_xboole_0(B_271)
      | v1_xboole_0(A_270) ) ),
    inference(resolution,[status(thm)],[c_132,c_2])).

tff(c_538,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_532])).

tff(c_542,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_56,c_538])).

tff(c_101,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_93])).

tff(c_114,plain,
    ( k7_relat_1('#skF_5','#skF_3') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_101,c_111])).

tff(c_120,plain,(
    k7_relat_1('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_114])).

tff(c_166,plain,(
    ! [B_237] :
      ( k7_relat_1('#skF_5',B_237) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_237)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_151])).

tff(c_176,plain,(
    ! [B_238] :
      ( k7_relat_1('#skF_5',B_238) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_238) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_166])).

tff(c_193,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_176])).

tff(c_353,plain,(
    ! [A_249,B_250,C_251,D_252] :
      ( k2_partfun1(A_249,B_250,C_251,D_252) = k7_relat_1(C_251,D_252)
      | ~ m1_subset_1(C_251,k1_zfmisc_1(k2_zfmisc_1(A_249,B_250)))
      | ~ v1_funct_1(C_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_357,plain,(
    ! [D_252] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_252) = k7_relat_1('#skF_5',D_252)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_46,c_353])).

tff(c_363,plain,(
    ! [D_252] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_252) = k7_relat_1('#skF_5',D_252) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_357])).

tff(c_355,plain,(
    ! [D_252] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_252) = k7_relat_1('#skF_6',D_252)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_40,c_353])).

tff(c_360,plain,(
    ! [D_252] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_252) = k7_relat_1('#skF_6',D_252) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_355])).

tff(c_287,plain,(
    ! [A_243,B_244,C_245] :
      ( k9_subset_1(A_243,B_244,C_245) = k3_xboole_0(B_244,C_245)
      | ~ m1_subset_1(C_245,k1_zfmisc_1(A_243)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_299,plain,(
    ! [B_244] : k9_subset_1('#skF_1',B_244,'#skF_4') = k3_xboole_0(B_244,'#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_287])).

tff(c_38,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_92,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_310,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_299,c_92])).

tff(c_591,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_542,c_193,c_542,c_363,c_360,c_310])).

tff(c_592,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_903,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_592])).

tff(c_2827,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2816,c_903])).

tff(c_2841,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_766,c_1035,c_730,c_1035,c_668,c_668,c_1157,c_2827])).

tff(c_2843,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2841])).

tff(c_2844,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_592])).

tff(c_4711,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4702,c_2844])).

tff(c_4722,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_766,c_2993,c_730,c_2993,c_668,c_668,c_3286,c_4711])).

tff(c_4724,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_4722])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:27:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.81/2.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.98/2.72  
% 7.98/2.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.98/2.73  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.98/2.73  
% 7.98/2.73  %Foreground sorts:
% 7.98/2.73  
% 7.98/2.73  
% 7.98/2.73  %Background operators:
% 7.98/2.73  
% 7.98/2.73  
% 7.98/2.73  %Foreground operators:
% 7.98/2.73  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 7.98/2.73  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.98/2.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.98/2.73  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.98/2.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.98/2.73  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 7.98/2.73  tff('#skF_5', type, '#skF_5': $i).
% 7.98/2.73  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.98/2.73  tff('#skF_6', type, '#skF_6': $i).
% 7.98/2.73  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.98/2.73  tff('#skF_2', type, '#skF_2': $i).
% 7.98/2.73  tff('#skF_3', type, '#skF_3': $i).
% 7.98/2.73  tff('#skF_1', type, '#skF_1': $i).
% 7.98/2.73  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.98/2.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.98/2.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.98/2.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.98/2.73  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.98/2.73  tff('#skF_4', type, '#skF_4': $i).
% 7.98/2.73  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.98/2.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.98/2.73  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 7.98/2.73  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.98/2.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.98/2.73  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.98/2.73  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.98/2.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.98/2.73  
% 7.98/2.76  tff(f_197, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 7.98/2.76  tff(f_31, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 7.98/2.76  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.98/2.76  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.98/2.76  tff(f_47, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 7.98/2.76  tff(f_41, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 7.98/2.76  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 7.98/2.76  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 7.98/2.76  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 7.98/2.76  tff(f_155, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 7.98/2.76  tff(f_73, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 7.98/2.76  tff(f_121, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 7.98/2.76  tff(c_64, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.98/2.76  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.98/2.76  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.98/2.76  tff(c_6, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.98/2.76  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.98/2.76  tff(c_83, plain, (![C_220, A_221, B_222]: (v1_relat_1(C_220) | ~m1_subset_1(C_220, k1_zfmisc_1(k2_zfmisc_1(A_221, B_222))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.98/2.76  tff(c_90, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_40, c_83])).
% 7.98/2.76  tff(c_595, plain, (![C_288, A_289, B_290]: (v4_relat_1(C_288, A_289) | ~m1_subset_1(C_288, k1_zfmisc_1(k2_zfmisc_1(A_289, B_290))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.98/2.76  tff(c_602, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_595])).
% 7.98/2.76  tff(c_12, plain, (![B_11, A_10]: (k7_relat_1(B_11, A_10)=B_11 | ~v4_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.98/2.76  tff(c_606, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_602, c_12])).
% 7.98/2.76  tff(c_609, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_606])).
% 7.98/2.76  tff(c_669, plain, (![C_301, A_302, B_303]: (k7_relat_1(k7_relat_1(C_301, A_302), B_303)=k1_xboole_0 | ~r1_xboole_0(A_302, B_303) | ~v1_relat_1(C_301))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.98/2.76  tff(c_687, plain, (![B_303]: (k7_relat_1('#skF_6', B_303)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_303) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_609, c_669])).
% 7.98/2.76  tff(c_749, plain, (![B_308]: (k7_relat_1('#skF_6', B_308)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_308))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_687])).
% 7.98/2.76  tff(c_766, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_749])).
% 7.98/2.76  tff(c_60, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.98/2.76  tff(c_56, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.98/2.76  tff(c_52, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.98/2.76  tff(c_637, plain, (![A_294, B_295]: (r1_xboole_0(A_294, B_295) | ~r1_subset_1(A_294, B_295) | v1_xboole_0(B_295) | v1_xboole_0(A_294))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.98/2.76  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.98/2.76  tff(c_2983, plain, (![A_709, B_710]: (k3_xboole_0(A_709, B_710)=k1_xboole_0 | ~r1_subset_1(A_709, B_710) | v1_xboole_0(B_710) | v1_xboole_0(A_709))), inference(resolution, [status(thm)], [c_637, c_2])).
% 7.98/2.76  tff(c_2989, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_2983])).
% 7.98/2.76  tff(c_2993, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_60, c_56, c_2989])).
% 7.98/2.76  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.98/2.76  tff(c_91, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_83])).
% 7.98/2.76  tff(c_603, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_595])).
% 7.98/2.76  tff(c_612, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_603, c_12])).
% 7.98/2.76  tff(c_615, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_91, c_612])).
% 7.98/2.76  tff(c_684, plain, (![B_303]: (k7_relat_1('#skF_5', B_303)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_303) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_615, c_669])).
% 7.98/2.76  tff(c_713, plain, (![B_306]: (k7_relat_1('#skF_5', B_306)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_306))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_684])).
% 7.98/2.76  tff(c_730, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_713])).
% 7.98/2.76  tff(c_656, plain, (![A_298, B_299, C_300]: (k9_subset_1(A_298, B_299, C_300)=k3_xboole_0(B_299, C_300) | ~m1_subset_1(C_300, k1_zfmisc_1(A_298)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.98/2.76  tff(c_668, plain, (![B_299]: (k9_subset_1('#skF_1', B_299, '#skF_4')=k3_xboole_0(B_299, '#skF_4'))), inference(resolution, [status(thm)], [c_54, c_656])).
% 7.98/2.76  tff(c_50, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.98/2.76  tff(c_48, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.98/2.76  tff(c_62, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.98/2.76  tff(c_44, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.98/2.76  tff(c_42, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.98/2.76  tff(c_3051, plain, (![C_724, A_722, B_721, E_719, D_723, F_720]: (v1_funct_1(k1_tmap_1(A_722, B_721, C_724, D_723, E_719, F_720)) | ~m1_subset_1(F_720, k1_zfmisc_1(k2_zfmisc_1(D_723, B_721))) | ~v1_funct_2(F_720, D_723, B_721) | ~v1_funct_1(F_720) | ~m1_subset_1(E_719, k1_zfmisc_1(k2_zfmisc_1(C_724, B_721))) | ~v1_funct_2(E_719, C_724, B_721) | ~v1_funct_1(E_719) | ~m1_subset_1(D_723, k1_zfmisc_1(A_722)) | v1_xboole_0(D_723) | ~m1_subset_1(C_724, k1_zfmisc_1(A_722)) | v1_xboole_0(C_724) | v1_xboole_0(B_721) | v1_xboole_0(A_722))), inference(cnfTransformation, [status(thm)], [f_155])).
% 7.98/2.76  tff(c_3053, plain, (![A_722, C_724, E_719]: (v1_funct_1(k1_tmap_1(A_722, '#skF_2', C_724, '#skF_4', E_719, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_719, k1_zfmisc_1(k2_zfmisc_1(C_724, '#skF_2'))) | ~v1_funct_2(E_719, C_724, '#skF_2') | ~v1_funct_1(E_719) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_722)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_724, k1_zfmisc_1(A_722)) | v1_xboole_0(C_724) | v1_xboole_0('#skF_2') | v1_xboole_0(A_722))), inference(resolution, [status(thm)], [c_40, c_3051])).
% 7.98/2.76  tff(c_3058, plain, (![A_722, C_724, E_719]: (v1_funct_1(k1_tmap_1(A_722, '#skF_2', C_724, '#skF_4', E_719, '#skF_6')) | ~m1_subset_1(E_719, k1_zfmisc_1(k2_zfmisc_1(C_724, '#skF_2'))) | ~v1_funct_2(E_719, C_724, '#skF_2') | ~v1_funct_1(E_719) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_722)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_724, k1_zfmisc_1(A_722)) | v1_xboole_0(C_724) | v1_xboole_0('#skF_2') | v1_xboole_0(A_722))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_3053])).
% 7.98/2.76  tff(c_3248, plain, (![A_762, C_763, E_764]: (v1_funct_1(k1_tmap_1(A_762, '#skF_2', C_763, '#skF_4', E_764, '#skF_6')) | ~m1_subset_1(E_764, k1_zfmisc_1(k2_zfmisc_1(C_763, '#skF_2'))) | ~v1_funct_2(E_764, C_763, '#skF_2') | ~v1_funct_1(E_764) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_762)) | ~m1_subset_1(C_763, k1_zfmisc_1(A_762)) | v1_xboole_0(C_763) | v1_xboole_0(A_762))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_3058])).
% 7.98/2.76  tff(c_3255, plain, (![A_762]: (v1_funct_1(k1_tmap_1(A_762, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_762)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_762)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_762))), inference(resolution, [status(thm)], [c_46, c_3248])).
% 7.98/2.76  tff(c_3265, plain, (![A_762]: (v1_funct_1(k1_tmap_1(A_762, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_762)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_762)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_762))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_3255])).
% 7.98/2.76  tff(c_3279, plain, (![A_766]: (v1_funct_1(k1_tmap_1(A_766, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_766)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_766)) | v1_xboole_0(A_766))), inference(negUnitSimplification, [status(thm)], [c_60, c_3265])).
% 7.98/2.76  tff(c_3282, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_58, c_3279])).
% 7.98/2.76  tff(c_3285, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3282])).
% 7.98/2.76  tff(c_3286, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_64, c_3285])).
% 7.98/2.76  tff(c_800, plain, (![A_310, B_311, C_312, D_313]: (k2_partfun1(A_310, B_311, C_312, D_313)=k7_relat_1(C_312, D_313) | ~m1_subset_1(C_312, k1_zfmisc_1(k2_zfmisc_1(A_310, B_311))) | ~v1_funct_1(C_312))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.98/2.76  tff(c_804, plain, (![D_313]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_313)=k7_relat_1('#skF_5', D_313) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_46, c_800])).
% 7.98/2.76  tff(c_810, plain, (![D_313]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_313)=k7_relat_1('#skF_5', D_313))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_804])).
% 7.98/2.76  tff(c_802, plain, (![D_313]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_313)=k7_relat_1('#skF_6', D_313) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_40, c_800])).
% 7.98/2.76  tff(c_807, plain, (![D_313]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_313)=k7_relat_1('#skF_6', D_313))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_802])).
% 7.98/2.76  tff(c_34, plain, (![E_155, B_152, F_156, C_153, D_154, A_151]: (v1_funct_2(k1_tmap_1(A_151, B_152, C_153, D_154, E_155, F_156), k4_subset_1(A_151, C_153, D_154), B_152) | ~m1_subset_1(F_156, k1_zfmisc_1(k2_zfmisc_1(D_154, B_152))) | ~v1_funct_2(F_156, D_154, B_152) | ~v1_funct_1(F_156) | ~m1_subset_1(E_155, k1_zfmisc_1(k2_zfmisc_1(C_153, B_152))) | ~v1_funct_2(E_155, C_153, B_152) | ~v1_funct_1(E_155) | ~m1_subset_1(D_154, k1_zfmisc_1(A_151)) | v1_xboole_0(D_154) | ~m1_subset_1(C_153, k1_zfmisc_1(A_151)) | v1_xboole_0(C_153) | v1_xboole_0(B_152) | v1_xboole_0(A_151))), inference(cnfTransformation, [status(thm)], [f_155])).
% 7.98/2.76  tff(c_32, plain, (![E_155, B_152, F_156, C_153, D_154, A_151]: (m1_subset_1(k1_tmap_1(A_151, B_152, C_153, D_154, E_155, F_156), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_151, C_153, D_154), B_152))) | ~m1_subset_1(F_156, k1_zfmisc_1(k2_zfmisc_1(D_154, B_152))) | ~v1_funct_2(F_156, D_154, B_152) | ~v1_funct_1(F_156) | ~m1_subset_1(E_155, k1_zfmisc_1(k2_zfmisc_1(C_153, B_152))) | ~v1_funct_2(E_155, C_153, B_152) | ~v1_funct_1(E_155) | ~m1_subset_1(D_154, k1_zfmisc_1(A_151)) | v1_xboole_0(D_154) | ~m1_subset_1(C_153, k1_zfmisc_1(A_151)) | v1_xboole_0(C_153) | v1_xboole_0(B_152) | v1_xboole_0(A_151))), inference(cnfTransformation, [status(thm)], [f_155])).
% 7.98/2.76  tff(c_3287, plain, (![E_771, C_767, D_772, B_770, F_768, A_769]: (k2_partfun1(k4_subset_1(A_769, C_767, D_772), B_770, k1_tmap_1(A_769, B_770, C_767, D_772, E_771, F_768), C_767)=E_771 | ~m1_subset_1(k1_tmap_1(A_769, B_770, C_767, D_772, E_771, F_768), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_769, C_767, D_772), B_770))) | ~v1_funct_2(k1_tmap_1(A_769, B_770, C_767, D_772, E_771, F_768), k4_subset_1(A_769, C_767, D_772), B_770) | ~v1_funct_1(k1_tmap_1(A_769, B_770, C_767, D_772, E_771, F_768)) | k2_partfun1(D_772, B_770, F_768, k9_subset_1(A_769, C_767, D_772))!=k2_partfun1(C_767, B_770, E_771, k9_subset_1(A_769, C_767, D_772)) | ~m1_subset_1(F_768, k1_zfmisc_1(k2_zfmisc_1(D_772, B_770))) | ~v1_funct_2(F_768, D_772, B_770) | ~v1_funct_1(F_768) | ~m1_subset_1(E_771, k1_zfmisc_1(k2_zfmisc_1(C_767, B_770))) | ~v1_funct_2(E_771, C_767, B_770) | ~v1_funct_1(E_771) | ~m1_subset_1(D_772, k1_zfmisc_1(A_769)) | v1_xboole_0(D_772) | ~m1_subset_1(C_767, k1_zfmisc_1(A_769)) | v1_xboole_0(C_767) | v1_xboole_0(B_770) | v1_xboole_0(A_769))), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.98/2.76  tff(c_3751, plain, (![F_871, A_873, E_870, D_874, B_872, C_875]: (k2_partfun1(k4_subset_1(A_873, C_875, D_874), B_872, k1_tmap_1(A_873, B_872, C_875, D_874, E_870, F_871), C_875)=E_870 | ~v1_funct_2(k1_tmap_1(A_873, B_872, C_875, D_874, E_870, F_871), k4_subset_1(A_873, C_875, D_874), B_872) | ~v1_funct_1(k1_tmap_1(A_873, B_872, C_875, D_874, E_870, F_871)) | k2_partfun1(D_874, B_872, F_871, k9_subset_1(A_873, C_875, D_874))!=k2_partfun1(C_875, B_872, E_870, k9_subset_1(A_873, C_875, D_874)) | ~m1_subset_1(F_871, k1_zfmisc_1(k2_zfmisc_1(D_874, B_872))) | ~v1_funct_2(F_871, D_874, B_872) | ~v1_funct_1(F_871) | ~m1_subset_1(E_870, k1_zfmisc_1(k2_zfmisc_1(C_875, B_872))) | ~v1_funct_2(E_870, C_875, B_872) | ~v1_funct_1(E_870) | ~m1_subset_1(D_874, k1_zfmisc_1(A_873)) | v1_xboole_0(D_874) | ~m1_subset_1(C_875, k1_zfmisc_1(A_873)) | v1_xboole_0(C_875) | v1_xboole_0(B_872) | v1_xboole_0(A_873))), inference(resolution, [status(thm)], [c_32, c_3287])).
% 7.98/2.76  tff(c_4166, plain, (![B_943, F_942, E_941, C_946, D_945, A_944]: (k2_partfun1(k4_subset_1(A_944, C_946, D_945), B_943, k1_tmap_1(A_944, B_943, C_946, D_945, E_941, F_942), C_946)=E_941 | ~v1_funct_1(k1_tmap_1(A_944, B_943, C_946, D_945, E_941, F_942)) | k2_partfun1(D_945, B_943, F_942, k9_subset_1(A_944, C_946, D_945))!=k2_partfun1(C_946, B_943, E_941, k9_subset_1(A_944, C_946, D_945)) | ~m1_subset_1(F_942, k1_zfmisc_1(k2_zfmisc_1(D_945, B_943))) | ~v1_funct_2(F_942, D_945, B_943) | ~v1_funct_1(F_942) | ~m1_subset_1(E_941, k1_zfmisc_1(k2_zfmisc_1(C_946, B_943))) | ~v1_funct_2(E_941, C_946, B_943) | ~v1_funct_1(E_941) | ~m1_subset_1(D_945, k1_zfmisc_1(A_944)) | v1_xboole_0(D_945) | ~m1_subset_1(C_946, k1_zfmisc_1(A_944)) | v1_xboole_0(C_946) | v1_xboole_0(B_943) | v1_xboole_0(A_944))), inference(resolution, [status(thm)], [c_34, c_3751])).
% 7.98/2.76  tff(c_4170, plain, (![A_944, C_946, E_941]: (k2_partfun1(k4_subset_1(A_944, C_946, '#skF_4'), '#skF_2', k1_tmap_1(A_944, '#skF_2', C_946, '#skF_4', E_941, '#skF_6'), C_946)=E_941 | ~v1_funct_1(k1_tmap_1(A_944, '#skF_2', C_946, '#skF_4', E_941, '#skF_6')) | k2_partfun1(C_946, '#skF_2', E_941, k9_subset_1(A_944, C_946, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_944, C_946, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_941, k1_zfmisc_1(k2_zfmisc_1(C_946, '#skF_2'))) | ~v1_funct_2(E_941, C_946, '#skF_2') | ~v1_funct_1(E_941) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_944)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_946, k1_zfmisc_1(A_944)) | v1_xboole_0(C_946) | v1_xboole_0('#skF_2') | v1_xboole_0(A_944))), inference(resolution, [status(thm)], [c_40, c_4166])).
% 7.98/2.76  tff(c_4176, plain, (![A_944, C_946, E_941]: (k2_partfun1(k4_subset_1(A_944, C_946, '#skF_4'), '#skF_2', k1_tmap_1(A_944, '#skF_2', C_946, '#skF_4', E_941, '#skF_6'), C_946)=E_941 | ~v1_funct_1(k1_tmap_1(A_944, '#skF_2', C_946, '#skF_4', E_941, '#skF_6')) | k2_partfun1(C_946, '#skF_2', E_941, k9_subset_1(A_944, C_946, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_944, C_946, '#skF_4')) | ~m1_subset_1(E_941, k1_zfmisc_1(k2_zfmisc_1(C_946, '#skF_2'))) | ~v1_funct_2(E_941, C_946, '#skF_2') | ~v1_funct_1(E_941) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_944)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_946, k1_zfmisc_1(A_944)) | v1_xboole_0(C_946) | v1_xboole_0('#skF_2') | v1_xboole_0(A_944))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_807, c_4170])).
% 7.98/2.76  tff(c_4665, plain, (![A_1032, C_1033, E_1034]: (k2_partfun1(k4_subset_1(A_1032, C_1033, '#skF_4'), '#skF_2', k1_tmap_1(A_1032, '#skF_2', C_1033, '#skF_4', E_1034, '#skF_6'), C_1033)=E_1034 | ~v1_funct_1(k1_tmap_1(A_1032, '#skF_2', C_1033, '#skF_4', E_1034, '#skF_6')) | k2_partfun1(C_1033, '#skF_2', E_1034, k9_subset_1(A_1032, C_1033, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1032, C_1033, '#skF_4')) | ~m1_subset_1(E_1034, k1_zfmisc_1(k2_zfmisc_1(C_1033, '#skF_2'))) | ~v1_funct_2(E_1034, C_1033, '#skF_2') | ~v1_funct_1(E_1034) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1032)) | ~m1_subset_1(C_1033, k1_zfmisc_1(A_1032)) | v1_xboole_0(C_1033) | v1_xboole_0(A_1032))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_4176])).
% 7.98/2.76  tff(c_4672, plain, (![A_1032]: (k2_partfun1(k4_subset_1(A_1032, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1032, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1032, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_1032, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1032, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1032)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1032)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1032))), inference(resolution, [status(thm)], [c_46, c_4665])).
% 7.98/2.76  tff(c_4682, plain, (![A_1032]: (k2_partfun1(k4_subset_1(A_1032, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1032, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1032, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1032, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1032, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1032)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1032)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1032))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_810, c_4672])).
% 7.98/2.76  tff(c_4702, plain, (![A_1041]: (k2_partfun1(k4_subset_1(A_1041, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1041, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1041, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1041, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1041, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1041)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1041)) | v1_xboole_0(A_1041))), inference(negUnitSimplification, [status(thm)], [c_60, c_4682])).
% 7.98/2.76  tff(c_1025, plain, (![A_327, B_328]: (k3_xboole_0(A_327, B_328)=k1_xboole_0 | ~r1_subset_1(A_327, B_328) | v1_xboole_0(B_328) | v1_xboole_0(A_327))), inference(resolution, [status(thm)], [c_637, c_2])).
% 7.98/2.76  tff(c_1031, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_1025])).
% 7.98/2.76  tff(c_1035, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_60, c_56, c_1031])).
% 7.98/2.76  tff(c_1082, plain, (![C_342, B_339, D_341, E_337, F_338, A_340]: (v1_funct_1(k1_tmap_1(A_340, B_339, C_342, D_341, E_337, F_338)) | ~m1_subset_1(F_338, k1_zfmisc_1(k2_zfmisc_1(D_341, B_339))) | ~v1_funct_2(F_338, D_341, B_339) | ~v1_funct_1(F_338) | ~m1_subset_1(E_337, k1_zfmisc_1(k2_zfmisc_1(C_342, B_339))) | ~v1_funct_2(E_337, C_342, B_339) | ~v1_funct_1(E_337) | ~m1_subset_1(D_341, k1_zfmisc_1(A_340)) | v1_xboole_0(D_341) | ~m1_subset_1(C_342, k1_zfmisc_1(A_340)) | v1_xboole_0(C_342) | v1_xboole_0(B_339) | v1_xboole_0(A_340))), inference(cnfTransformation, [status(thm)], [f_155])).
% 7.98/2.76  tff(c_1084, plain, (![A_340, C_342, E_337]: (v1_funct_1(k1_tmap_1(A_340, '#skF_2', C_342, '#skF_4', E_337, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_337, k1_zfmisc_1(k2_zfmisc_1(C_342, '#skF_2'))) | ~v1_funct_2(E_337, C_342, '#skF_2') | ~v1_funct_1(E_337) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_340)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_342, k1_zfmisc_1(A_340)) | v1_xboole_0(C_342) | v1_xboole_0('#skF_2') | v1_xboole_0(A_340))), inference(resolution, [status(thm)], [c_40, c_1082])).
% 7.98/2.76  tff(c_1089, plain, (![A_340, C_342, E_337]: (v1_funct_1(k1_tmap_1(A_340, '#skF_2', C_342, '#skF_4', E_337, '#skF_6')) | ~m1_subset_1(E_337, k1_zfmisc_1(k2_zfmisc_1(C_342, '#skF_2'))) | ~v1_funct_2(E_337, C_342, '#skF_2') | ~v1_funct_1(E_337) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_340)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_342, k1_zfmisc_1(A_340)) | v1_xboole_0(C_342) | v1_xboole_0('#skF_2') | v1_xboole_0(A_340))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_1084])).
% 7.98/2.76  tff(c_1096, plain, (![A_343, C_344, E_345]: (v1_funct_1(k1_tmap_1(A_343, '#skF_2', C_344, '#skF_4', E_345, '#skF_6')) | ~m1_subset_1(E_345, k1_zfmisc_1(k2_zfmisc_1(C_344, '#skF_2'))) | ~v1_funct_2(E_345, C_344, '#skF_2') | ~v1_funct_1(E_345) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_343)) | ~m1_subset_1(C_344, k1_zfmisc_1(A_343)) | v1_xboole_0(C_344) | v1_xboole_0(A_343))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_1089])).
% 7.98/2.76  tff(c_1100, plain, (![A_343]: (v1_funct_1(k1_tmap_1(A_343, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_343)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_343)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_343))), inference(resolution, [status(thm)], [c_46, c_1096])).
% 7.98/2.76  tff(c_1107, plain, (![A_343]: (v1_funct_1(k1_tmap_1(A_343, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_343)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_343)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_343))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_1100])).
% 7.98/2.76  tff(c_1150, plain, (![A_361]: (v1_funct_1(k1_tmap_1(A_361, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_361)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_361)) | v1_xboole_0(A_361))), inference(negUnitSimplification, [status(thm)], [c_60, c_1107])).
% 7.98/2.76  tff(c_1153, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_58, c_1150])).
% 7.98/2.76  tff(c_1156, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1153])).
% 7.98/2.76  tff(c_1157, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_64, c_1156])).
% 7.98/2.76  tff(c_1362, plain, (![F_391, B_393, A_392, C_390, E_394, D_395]: (k2_partfun1(k4_subset_1(A_392, C_390, D_395), B_393, k1_tmap_1(A_392, B_393, C_390, D_395, E_394, F_391), D_395)=F_391 | ~m1_subset_1(k1_tmap_1(A_392, B_393, C_390, D_395, E_394, F_391), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_392, C_390, D_395), B_393))) | ~v1_funct_2(k1_tmap_1(A_392, B_393, C_390, D_395, E_394, F_391), k4_subset_1(A_392, C_390, D_395), B_393) | ~v1_funct_1(k1_tmap_1(A_392, B_393, C_390, D_395, E_394, F_391)) | k2_partfun1(D_395, B_393, F_391, k9_subset_1(A_392, C_390, D_395))!=k2_partfun1(C_390, B_393, E_394, k9_subset_1(A_392, C_390, D_395)) | ~m1_subset_1(F_391, k1_zfmisc_1(k2_zfmisc_1(D_395, B_393))) | ~v1_funct_2(F_391, D_395, B_393) | ~v1_funct_1(F_391) | ~m1_subset_1(E_394, k1_zfmisc_1(k2_zfmisc_1(C_390, B_393))) | ~v1_funct_2(E_394, C_390, B_393) | ~v1_funct_1(E_394) | ~m1_subset_1(D_395, k1_zfmisc_1(A_392)) | v1_xboole_0(D_395) | ~m1_subset_1(C_390, k1_zfmisc_1(A_392)) | v1_xboole_0(C_390) | v1_xboole_0(B_393) | v1_xboole_0(A_392))), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.98/2.76  tff(c_1832, plain, (![C_507, A_505, E_502, B_504, F_503, D_506]: (k2_partfun1(k4_subset_1(A_505, C_507, D_506), B_504, k1_tmap_1(A_505, B_504, C_507, D_506, E_502, F_503), D_506)=F_503 | ~v1_funct_2(k1_tmap_1(A_505, B_504, C_507, D_506, E_502, F_503), k4_subset_1(A_505, C_507, D_506), B_504) | ~v1_funct_1(k1_tmap_1(A_505, B_504, C_507, D_506, E_502, F_503)) | k2_partfun1(D_506, B_504, F_503, k9_subset_1(A_505, C_507, D_506))!=k2_partfun1(C_507, B_504, E_502, k9_subset_1(A_505, C_507, D_506)) | ~m1_subset_1(F_503, k1_zfmisc_1(k2_zfmisc_1(D_506, B_504))) | ~v1_funct_2(F_503, D_506, B_504) | ~v1_funct_1(F_503) | ~m1_subset_1(E_502, k1_zfmisc_1(k2_zfmisc_1(C_507, B_504))) | ~v1_funct_2(E_502, C_507, B_504) | ~v1_funct_1(E_502) | ~m1_subset_1(D_506, k1_zfmisc_1(A_505)) | v1_xboole_0(D_506) | ~m1_subset_1(C_507, k1_zfmisc_1(A_505)) | v1_xboole_0(C_507) | v1_xboole_0(B_504) | v1_xboole_0(A_505))), inference(resolution, [status(thm)], [c_32, c_1362])).
% 7.98/2.76  tff(c_2162, plain, (![C_562, D_561, F_558, B_559, A_560, E_557]: (k2_partfun1(k4_subset_1(A_560, C_562, D_561), B_559, k1_tmap_1(A_560, B_559, C_562, D_561, E_557, F_558), D_561)=F_558 | ~v1_funct_1(k1_tmap_1(A_560, B_559, C_562, D_561, E_557, F_558)) | k2_partfun1(D_561, B_559, F_558, k9_subset_1(A_560, C_562, D_561))!=k2_partfun1(C_562, B_559, E_557, k9_subset_1(A_560, C_562, D_561)) | ~m1_subset_1(F_558, k1_zfmisc_1(k2_zfmisc_1(D_561, B_559))) | ~v1_funct_2(F_558, D_561, B_559) | ~v1_funct_1(F_558) | ~m1_subset_1(E_557, k1_zfmisc_1(k2_zfmisc_1(C_562, B_559))) | ~v1_funct_2(E_557, C_562, B_559) | ~v1_funct_1(E_557) | ~m1_subset_1(D_561, k1_zfmisc_1(A_560)) | v1_xboole_0(D_561) | ~m1_subset_1(C_562, k1_zfmisc_1(A_560)) | v1_xboole_0(C_562) | v1_xboole_0(B_559) | v1_xboole_0(A_560))), inference(resolution, [status(thm)], [c_34, c_1832])).
% 7.98/2.76  tff(c_2166, plain, (![A_560, C_562, E_557]: (k2_partfun1(k4_subset_1(A_560, C_562, '#skF_4'), '#skF_2', k1_tmap_1(A_560, '#skF_2', C_562, '#skF_4', E_557, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_560, '#skF_2', C_562, '#skF_4', E_557, '#skF_6')) | k2_partfun1(C_562, '#skF_2', E_557, k9_subset_1(A_560, C_562, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_560, C_562, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_557, k1_zfmisc_1(k2_zfmisc_1(C_562, '#skF_2'))) | ~v1_funct_2(E_557, C_562, '#skF_2') | ~v1_funct_1(E_557) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_560)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_562, k1_zfmisc_1(A_560)) | v1_xboole_0(C_562) | v1_xboole_0('#skF_2') | v1_xboole_0(A_560))), inference(resolution, [status(thm)], [c_40, c_2162])).
% 7.98/2.76  tff(c_2172, plain, (![A_560, C_562, E_557]: (k2_partfun1(k4_subset_1(A_560, C_562, '#skF_4'), '#skF_2', k1_tmap_1(A_560, '#skF_2', C_562, '#skF_4', E_557, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_560, '#skF_2', C_562, '#skF_4', E_557, '#skF_6')) | k2_partfun1(C_562, '#skF_2', E_557, k9_subset_1(A_560, C_562, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_560, C_562, '#skF_4')) | ~m1_subset_1(E_557, k1_zfmisc_1(k2_zfmisc_1(C_562, '#skF_2'))) | ~v1_funct_2(E_557, C_562, '#skF_2') | ~v1_funct_1(E_557) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_560)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_562, k1_zfmisc_1(A_560)) | v1_xboole_0(C_562) | v1_xboole_0('#skF_2') | v1_xboole_0(A_560))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_807, c_2166])).
% 7.98/2.76  tff(c_2797, plain, (![A_697, C_698, E_699]: (k2_partfun1(k4_subset_1(A_697, C_698, '#skF_4'), '#skF_2', k1_tmap_1(A_697, '#skF_2', C_698, '#skF_4', E_699, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_697, '#skF_2', C_698, '#skF_4', E_699, '#skF_6')) | k2_partfun1(C_698, '#skF_2', E_699, k9_subset_1(A_697, C_698, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_697, C_698, '#skF_4')) | ~m1_subset_1(E_699, k1_zfmisc_1(k2_zfmisc_1(C_698, '#skF_2'))) | ~v1_funct_2(E_699, C_698, '#skF_2') | ~v1_funct_1(E_699) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_697)) | ~m1_subset_1(C_698, k1_zfmisc_1(A_697)) | v1_xboole_0(C_698) | v1_xboole_0(A_697))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_2172])).
% 7.98/2.76  tff(c_2804, plain, (![A_697]: (k2_partfun1(k4_subset_1(A_697, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_697, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_697, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_697, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_697, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_697)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_697)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_697))), inference(resolution, [status(thm)], [c_46, c_2797])).
% 7.98/2.76  tff(c_2814, plain, (![A_697]: (k2_partfun1(k4_subset_1(A_697, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_697, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_697, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_697, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_697, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_697)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_697)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_697))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_810, c_2804])).
% 7.98/2.76  tff(c_2816, plain, (![A_700]: (k2_partfun1(k4_subset_1(A_700, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_700, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_700, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_700, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_700, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_700)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_700)) | v1_xboole_0(A_700))), inference(negUnitSimplification, [status(thm)], [c_60, c_2814])).
% 7.98/2.76  tff(c_93, plain, (![C_223, A_224, B_225]: (v4_relat_1(C_223, A_224) | ~m1_subset_1(C_223, k1_zfmisc_1(k2_zfmisc_1(A_224, B_225))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.98/2.76  tff(c_100, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_93])).
% 7.98/2.76  tff(c_111, plain, (![B_229, A_230]: (k7_relat_1(B_229, A_230)=B_229 | ~v4_relat_1(B_229, A_230) | ~v1_relat_1(B_229))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.98/2.76  tff(c_117, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_100, c_111])).
% 7.98/2.76  tff(c_123, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_117])).
% 7.98/2.76  tff(c_151, plain, (![C_235, A_236, B_237]: (k7_relat_1(k7_relat_1(C_235, A_236), B_237)=k1_xboole_0 | ~r1_xboole_0(A_236, B_237) | ~v1_relat_1(C_235))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.98/2.76  tff(c_169, plain, (![B_237]: (k7_relat_1('#skF_6', B_237)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_237) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_123, c_151])).
% 7.98/2.76  tff(c_203, plain, (![B_239]: (k7_relat_1('#skF_6', B_239)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_239))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_169])).
% 7.98/2.76  tff(c_220, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_203])).
% 7.98/2.76  tff(c_132, plain, (![A_231, B_232]: (r1_xboole_0(A_231, B_232) | ~r1_subset_1(A_231, B_232) | v1_xboole_0(B_232) | v1_xboole_0(A_231))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.98/2.76  tff(c_532, plain, (![A_270, B_271]: (k3_xboole_0(A_270, B_271)=k1_xboole_0 | ~r1_subset_1(A_270, B_271) | v1_xboole_0(B_271) | v1_xboole_0(A_270))), inference(resolution, [status(thm)], [c_132, c_2])).
% 7.98/2.76  tff(c_538, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_532])).
% 7.98/2.76  tff(c_542, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_60, c_56, c_538])).
% 7.98/2.76  tff(c_101, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_93])).
% 7.98/2.76  tff(c_114, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_101, c_111])).
% 7.98/2.76  tff(c_120, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_91, c_114])).
% 7.98/2.76  tff(c_166, plain, (![B_237]: (k7_relat_1('#skF_5', B_237)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_237) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_120, c_151])).
% 7.98/2.76  tff(c_176, plain, (![B_238]: (k7_relat_1('#skF_5', B_238)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_238))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_166])).
% 7.98/2.76  tff(c_193, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_176])).
% 7.98/2.76  tff(c_353, plain, (![A_249, B_250, C_251, D_252]: (k2_partfun1(A_249, B_250, C_251, D_252)=k7_relat_1(C_251, D_252) | ~m1_subset_1(C_251, k1_zfmisc_1(k2_zfmisc_1(A_249, B_250))) | ~v1_funct_1(C_251))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.98/2.76  tff(c_357, plain, (![D_252]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_252)=k7_relat_1('#skF_5', D_252) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_46, c_353])).
% 7.98/2.76  tff(c_363, plain, (![D_252]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_252)=k7_relat_1('#skF_5', D_252))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_357])).
% 7.98/2.76  tff(c_355, plain, (![D_252]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_252)=k7_relat_1('#skF_6', D_252) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_40, c_353])).
% 7.98/2.76  tff(c_360, plain, (![D_252]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_252)=k7_relat_1('#skF_6', D_252))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_355])).
% 7.98/2.76  tff(c_287, plain, (![A_243, B_244, C_245]: (k9_subset_1(A_243, B_244, C_245)=k3_xboole_0(B_244, C_245) | ~m1_subset_1(C_245, k1_zfmisc_1(A_243)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.98/2.76  tff(c_299, plain, (![B_244]: (k9_subset_1('#skF_1', B_244, '#skF_4')=k3_xboole_0(B_244, '#skF_4'))), inference(resolution, [status(thm)], [c_54, c_287])).
% 7.98/2.76  tff(c_38, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.98/2.76  tff(c_92, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_38])).
% 7.98/2.76  tff(c_310, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_299, c_299, c_92])).
% 7.98/2.76  tff(c_591, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_220, c_542, c_193, c_542, c_363, c_360, c_310])).
% 7.98/2.76  tff(c_592, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_38])).
% 7.98/2.76  tff(c_903, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_592])).
% 7.98/2.76  tff(c_2827, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2816, c_903])).
% 7.98/2.76  tff(c_2841, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_766, c_1035, c_730, c_1035, c_668, c_668, c_1157, c_2827])).
% 7.98/2.76  tff(c_2843, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_2841])).
% 7.98/2.76  tff(c_2844, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_592])).
% 7.98/2.76  tff(c_4711, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4702, c_2844])).
% 7.98/2.76  tff(c_4722, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_766, c_2993, c_730, c_2993, c_668, c_668, c_3286, c_4711])).
% 7.98/2.76  tff(c_4724, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_4722])).
% 7.98/2.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.98/2.76  
% 7.98/2.76  Inference rules
% 7.98/2.76  ----------------------
% 7.98/2.76  #Ref     : 0
% 7.98/2.76  #Sup     : 983
% 7.98/2.76  #Fact    : 0
% 7.98/2.76  #Define  : 0
% 7.98/2.76  #Split   : 35
% 7.98/2.76  #Chain   : 0
% 7.98/2.76  #Close   : 0
% 7.98/2.76  
% 7.98/2.76  Ordering : KBO
% 7.98/2.76  
% 7.98/2.76  Simplification rules
% 7.98/2.76  ----------------------
% 7.98/2.76  #Subsume      : 220
% 7.98/2.76  #Demod        : 613
% 7.98/2.76  #Tautology    : 325
% 7.98/2.76  #SimpNegUnit  : 246
% 7.98/2.76  #BackRed      : 3
% 7.98/2.76  
% 7.98/2.76  #Partial instantiations: 0
% 7.98/2.76  #Strategies tried      : 1
% 7.98/2.76  
% 7.98/2.76  Timing (in seconds)
% 7.98/2.76  ----------------------
% 7.98/2.76  Preprocessing        : 0.41
% 7.98/2.76  Parsing              : 0.20
% 7.98/2.76  CNF conversion       : 0.06
% 7.98/2.76  Main loop            : 1.56
% 7.98/2.76  Inferencing          : 0.54
% 7.98/2.76  Reduction            : 0.53
% 7.98/2.76  Demodulation         : 0.38
% 7.98/2.76  BG Simplification    : 0.05
% 7.98/2.76  Subsumption          : 0.35
% 7.98/2.76  Abstraction          : 0.07
% 7.98/2.76  MUC search           : 0.00
% 7.98/2.76  Cooper               : 0.00
% 7.98/2.76  Total                : 2.03
% 7.98/2.76  Index Insertion      : 0.00
% 7.98/2.76  Index Deletion       : 0.00
% 7.98/2.76  Index Matching       : 0.00
% 7.98/2.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
