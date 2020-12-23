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
% DateTime   : Thu Dec  3 10:26:15 EST 2020

% Result     : Theorem 8.17s
% Output     : CNFRefutation 8.28s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 485 expanded)
%              Number of leaves         :   38 ( 193 expanded)
%              Depth                    :   12
%              Number of atoms          :  579 (2498 expanded)
%              Number of equality atoms :  112 ( 510 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_194,negated_conjecture,(
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

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_31,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_60,axiom,(
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

tff(f_152,axiom,(
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

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_118,axiom,(
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

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_414,plain,(
    ! [C_257,A_258,B_259] :
      ( v1_relat_1(C_257)
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(A_258,B_259))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_421,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_414])).

tff(c_16,plain,(
    ! [A_13] :
      ( k7_relat_1(A_13,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_426,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_421,c_16])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_4] : r1_xboole_0(A_4,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_75,plain,(
    ! [A_218,B_219] :
      ( k4_xboole_0(A_218,B_219) = A_218
      | ~ r1_xboole_0(A_218,B_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_83,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(resolution,[status(thm)],[c_6,c_75])).

tff(c_395,plain,(
    ! [A_255,B_256] : k4_xboole_0(A_255,k4_xboole_0(A_255,B_256)) = k3_xboole_0(A_255,B_256) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_410,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k3_xboole_0(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_395])).

tff(c_413,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_410])).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_52,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_3165,plain,(
    ! [A_506,B_507] :
      ( r1_xboole_0(A_506,B_507)
      | ~ r1_subset_1(A_506,B_507)
      | v1_xboole_0(B_507)
      | v1_xboole_0(A_506) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = A_5
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3245,plain,(
    ! [A_517,B_518] :
      ( k4_xboole_0(A_517,B_518) = A_517
      | ~ r1_subset_1(A_517,B_518)
      | v1_xboole_0(B_518)
      | v1_xboole_0(A_517) ) ),
    inference(resolution,[status(thm)],[c_3165,c_8])).

tff(c_3248,plain,
    ( k4_xboole_0('#skF_3','#skF_4') = '#skF_3'
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_3245])).

tff(c_3251,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_56,c_3248])).

tff(c_4,plain,(
    ! [A_2,B_3] : k4_xboole_0(A_2,k4_xboole_0(A_2,B_3)) = k3_xboole_0(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_3255,plain,(
    k4_xboole_0('#skF_3','#skF_3') = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3251,c_4])).

tff(c_3258,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_3255])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_422,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_414])).

tff(c_430,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_422,c_16])).

tff(c_3194,plain,(
    ! [A_510,B_511,C_512] :
      ( k9_subset_1(A_510,B_511,C_512) = k3_xboole_0(B_511,C_512)
      | ~ m1_subset_1(C_512,k1_zfmisc_1(A_510)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3206,plain,(
    ! [B_511] : k9_subset_1('#skF_1',B_511,'#skF_4') = k3_xboole_0(B_511,'#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_3194])).

tff(c_50,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_48,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_44,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_42,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_3407,plain,(
    ! [B_532,A_536,F_533,C_534,E_535,D_531] :
      ( v1_funct_1(k1_tmap_1(A_536,B_532,C_534,D_531,E_535,F_533))
      | ~ m1_subset_1(F_533,k1_zfmisc_1(k2_zfmisc_1(D_531,B_532)))
      | ~ v1_funct_2(F_533,D_531,B_532)
      | ~ v1_funct_1(F_533)
      | ~ m1_subset_1(E_535,k1_zfmisc_1(k2_zfmisc_1(C_534,B_532)))
      | ~ v1_funct_2(E_535,C_534,B_532)
      | ~ v1_funct_1(E_535)
      | ~ m1_subset_1(D_531,k1_zfmisc_1(A_536))
      | v1_xboole_0(D_531)
      | ~ m1_subset_1(C_534,k1_zfmisc_1(A_536))
      | v1_xboole_0(C_534)
      | v1_xboole_0(B_532)
      | v1_xboole_0(A_536) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_3409,plain,(
    ! [A_536,C_534,E_535] :
      ( v1_funct_1(k1_tmap_1(A_536,'#skF_2',C_534,'#skF_4',E_535,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_535,k1_zfmisc_1(k2_zfmisc_1(C_534,'#skF_2')))
      | ~ v1_funct_2(E_535,C_534,'#skF_2')
      | ~ v1_funct_1(E_535)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_536))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_534,k1_zfmisc_1(A_536))
      | v1_xboole_0(C_534)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_536) ) ),
    inference(resolution,[status(thm)],[c_40,c_3407])).

tff(c_3414,plain,(
    ! [A_536,C_534,E_535] :
      ( v1_funct_1(k1_tmap_1(A_536,'#skF_2',C_534,'#skF_4',E_535,'#skF_6'))
      | ~ m1_subset_1(E_535,k1_zfmisc_1(k2_zfmisc_1(C_534,'#skF_2')))
      | ~ v1_funct_2(E_535,C_534,'#skF_2')
      | ~ v1_funct_1(E_535)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_536))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_534,k1_zfmisc_1(A_536))
      | v1_xboole_0(C_534)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_536) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_3409])).

tff(c_3532,plain,(
    ! [A_541,C_542,E_543] :
      ( v1_funct_1(k1_tmap_1(A_541,'#skF_2',C_542,'#skF_4',E_543,'#skF_6'))
      | ~ m1_subset_1(E_543,k1_zfmisc_1(k2_zfmisc_1(C_542,'#skF_2')))
      | ~ v1_funct_2(E_543,C_542,'#skF_2')
      | ~ v1_funct_1(E_543)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_541))
      | ~ m1_subset_1(C_542,k1_zfmisc_1(A_541))
      | v1_xboole_0(C_542)
      | v1_xboole_0(A_541) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_3414])).

tff(c_3536,plain,(
    ! [A_541] :
      ( v1_funct_1(k1_tmap_1(A_541,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_541))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_541))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_541) ) ),
    inference(resolution,[status(thm)],[c_46,c_3532])).

tff(c_3543,plain,(
    ! [A_541] :
      ( v1_funct_1(k1_tmap_1(A_541,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_541))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_541))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_541) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_3536])).

tff(c_3552,plain,(
    ! [A_545] :
      ( v1_funct_1(k1_tmap_1(A_545,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_545))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_545))
      | v1_xboole_0(A_545) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_3543])).

tff(c_3555,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_3552])).

tff(c_3558,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3555])).

tff(c_3559,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_3558])).

tff(c_3364,plain,(
    ! [A_525,B_526,C_527,D_528] :
      ( k2_partfun1(A_525,B_526,C_527,D_528) = k7_relat_1(C_527,D_528)
      | ~ m1_subset_1(C_527,k1_zfmisc_1(k2_zfmisc_1(A_525,B_526)))
      | ~ v1_funct_1(C_527) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3368,plain,(
    ! [D_528] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_528) = k7_relat_1('#skF_5',D_528)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_46,c_3364])).

tff(c_3374,plain,(
    ! [D_528] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_528) = k7_relat_1('#skF_5',D_528) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_3368])).

tff(c_3366,plain,(
    ! [D_528] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_528) = k7_relat_1('#skF_6',D_528)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_40,c_3364])).

tff(c_3371,plain,(
    ! [D_528] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_528) = k7_relat_1('#skF_6',D_528) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_3366])).

tff(c_34,plain,(
    ! [C_152,F_155,D_153,A_150,B_151,E_154] :
      ( v1_funct_2(k1_tmap_1(A_150,B_151,C_152,D_153,E_154,F_155),k4_subset_1(A_150,C_152,D_153),B_151)
      | ~ m1_subset_1(F_155,k1_zfmisc_1(k2_zfmisc_1(D_153,B_151)))
      | ~ v1_funct_2(F_155,D_153,B_151)
      | ~ v1_funct_1(F_155)
      | ~ m1_subset_1(E_154,k1_zfmisc_1(k2_zfmisc_1(C_152,B_151)))
      | ~ v1_funct_2(E_154,C_152,B_151)
      | ~ v1_funct_1(E_154)
      | ~ m1_subset_1(D_153,k1_zfmisc_1(A_150))
      | v1_xboole_0(D_153)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(A_150))
      | v1_xboole_0(C_152)
      | v1_xboole_0(B_151)
      | v1_xboole_0(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_32,plain,(
    ! [C_152,F_155,D_153,A_150,B_151,E_154] :
      ( m1_subset_1(k1_tmap_1(A_150,B_151,C_152,D_153,E_154,F_155),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_150,C_152,D_153),B_151)))
      | ~ m1_subset_1(F_155,k1_zfmisc_1(k2_zfmisc_1(D_153,B_151)))
      | ~ v1_funct_2(F_155,D_153,B_151)
      | ~ v1_funct_1(F_155)
      | ~ m1_subset_1(E_154,k1_zfmisc_1(k2_zfmisc_1(C_152,B_151)))
      | ~ v1_funct_2(E_154,C_152,B_151)
      | ~ v1_funct_1(E_154)
      | ~ m1_subset_1(D_153,k1_zfmisc_1(A_150))
      | v1_xboole_0(D_153)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(A_150))
      | v1_xboole_0(C_152)
      | v1_xboole_0(B_151)
      | v1_xboole_0(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_3870,plain,(
    ! [B_576,E_577,D_579,C_575,F_578,A_580] :
      ( k2_partfun1(k4_subset_1(A_580,C_575,D_579),B_576,k1_tmap_1(A_580,B_576,C_575,D_579,E_577,F_578),C_575) = E_577
      | ~ m1_subset_1(k1_tmap_1(A_580,B_576,C_575,D_579,E_577,F_578),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_580,C_575,D_579),B_576)))
      | ~ v1_funct_2(k1_tmap_1(A_580,B_576,C_575,D_579,E_577,F_578),k4_subset_1(A_580,C_575,D_579),B_576)
      | ~ v1_funct_1(k1_tmap_1(A_580,B_576,C_575,D_579,E_577,F_578))
      | k2_partfun1(D_579,B_576,F_578,k9_subset_1(A_580,C_575,D_579)) != k2_partfun1(C_575,B_576,E_577,k9_subset_1(A_580,C_575,D_579))
      | ~ m1_subset_1(F_578,k1_zfmisc_1(k2_zfmisc_1(D_579,B_576)))
      | ~ v1_funct_2(F_578,D_579,B_576)
      | ~ v1_funct_1(F_578)
      | ~ m1_subset_1(E_577,k1_zfmisc_1(k2_zfmisc_1(C_575,B_576)))
      | ~ v1_funct_2(E_577,C_575,B_576)
      | ~ v1_funct_1(E_577)
      | ~ m1_subset_1(D_579,k1_zfmisc_1(A_580))
      | v1_xboole_0(D_579)
      | ~ m1_subset_1(C_575,k1_zfmisc_1(A_580))
      | v1_xboole_0(C_575)
      | v1_xboole_0(B_576)
      | v1_xboole_0(A_580) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_4872,plain,(
    ! [C_669,B_667,E_670,D_666,A_671,F_668] :
      ( k2_partfun1(k4_subset_1(A_671,C_669,D_666),B_667,k1_tmap_1(A_671,B_667,C_669,D_666,E_670,F_668),C_669) = E_670
      | ~ v1_funct_2(k1_tmap_1(A_671,B_667,C_669,D_666,E_670,F_668),k4_subset_1(A_671,C_669,D_666),B_667)
      | ~ v1_funct_1(k1_tmap_1(A_671,B_667,C_669,D_666,E_670,F_668))
      | k2_partfun1(D_666,B_667,F_668,k9_subset_1(A_671,C_669,D_666)) != k2_partfun1(C_669,B_667,E_670,k9_subset_1(A_671,C_669,D_666))
      | ~ m1_subset_1(F_668,k1_zfmisc_1(k2_zfmisc_1(D_666,B_667)))
      | ~ v1_funct_2(F_668,D_666,B_667)
      | ~ v1_funct_1(F_668)
      | ~ m1_subset_1(E_670,k1_zfmisc_1(k2_zfmisc_1(C_669,B_667)))
      | ~ v1_funct_2(E_670,C_669,B_667)
      | ~ v1_funct_1(E_670)
      | ~ m1_subset_1(D_666,k1_zfmisc_1(A_671))
      | v1_xboole_0(D_666)
      | ~ m1_subset_1(C_669,k1_zfmisc_1(A_671))
      | v1_xboole_0(C_669)
      | v1_xboole_0(B_667)
      | v1_xboole_0(A_671) ) ),
    inference(resolution,[status(thm)],[c_32,c_3870])).

tff(c_5141,plain,(
    ! [F_695,C_696,D_693,A_698,E_697,B_694] :
      ( k2_partfun1(k4_subset_1(A_698,C_696,D_693),B_694,k1_tmap_1(A_698,B_694,C_696,D_693,E_697,F_695),C_696) = E_697
      | ~ v1_funct_1(k1_tmap_1(A_698,B_694,C_696,D_693,E_697,F_695))
      | k2_partfun1(D_693,B_694,F_695,k9_subset_1(A_698,C_696,D_693)) != k2_partfun1(C_696,B_694,E_697,k9_subset_1(A_698,C_696,D_693))
      | ~ m1_subset_1(F_695,k1_zfmisc_1(k2_zfmisc_1(D_693,B_694)))
      | ~ v1_funct_2(F_695,D_693,B_694)
      | ~ v1_funct_1(F_695)
      | ~ m1_subset_1(E_697,k1_zfmisc_1(k2_zfmisc_1(C_696,B_694)))
      | ~ v1_funct_2(E_697,C_696,B_694)
      | ~ v1_funct_1(E_697)
      | ~ m1_subset_1(D_693,k1_zfmisc_1(A_698))
      | v1_xboole_0(D_693)
      | ~ m1_subset_1(C_696,k1_zfmisc_1(A_698))
      | v1_xboole_0(C_696)
      | v1_xboole_0(B_694)
      | v1_xboole_0(A_698) ) ),
    inference(resolution,[status(thm)],[c_34,c_4872])).

tff(c_5145,plain,(
    ! [A_698,C_696,E_697] :
      ( k2_partfun1(k4_subset_1(A_698,C_696,'#skF_4'),'#skF_2',k1_tmap_1(A_698,'#skF_2',C_696,'#skF_4',E_697,'#skF_6'),C_696) = E_697
      | ~ v1_funct_1(k1_tmap_1(A_698,'#skF_2',C_696,'#skF_4',E_697,'#skF_6'))
      | k2_partfun1(C_696,'#skF_2',E_697,k9_subset_1(A_698,C_696,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_698,C_696,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_697,k1_zfmisc_1(k2_zfmisc_1(C_696,'#skF_2')))
      | ~ v1_funct_2(E_697,C_696,'#skF_2')
      | ~ v1_funct_1(E_697)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_698))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_696,k1_zfmisc_1(A_698))
      | v1_xboole_0(C_696)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_698) ) ),
    inference(resolution,[status(thm)],[c_40,c_5141])).

tff(c_5151,plain,(
    ! [A_698,C_696,E_697] :
      ( k2_partfun1(k4_subset_1(A_698,C_696,'#skF_4'),'#skF_2',k1_tmap_1(A_698,'#skF_2',C_696,'#skF_4',E_697,'#skF_6'),C_696) = E_697
      | ~ v1_funct_1(k1_tmap_1(A_698,'#skF_2',C_696,'#skF_4',E_697,'#skF_6'))
      | k2_partfun1(C_696,'#skF_2',E_697,k9_subset_1(A_698,C_696,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_698,C_696,'#skF_4'))
      | ~ m1_subset_1(E_697,k1_zfmisc_1(k2_zfmisc_1(C_696,'#skF_2')))
      | ~ v1_funct_2(E_697,C_696,'#skF_2')
      | ~ v1_funct_1(E_697)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_698))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_696,k1_zfmisc_1(A_698))
      | v1_xboole_0(C_696)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_698) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_3371,c_5145])).

tff(c_5849,plain,(
    ! [A_746,C_747,E_748] :
      ( k2_partfun1(k4_subset_1(A_746,C_747,'#skF_4'),'#skF_2',k1_tmap_1(A_746,'#skF_2',C_747,'#skF_4',E_748,'#skF_6'),C_747) = E_748
      | ~ v1_funct_1(k1_tmap_1(A_746,'#skF_2',C_747,'#skF_4',E_748,'#skF_6'))
      | k2_partfun1(C_747,'#skF_2',E_748,k9_subset_1(A_746,C_747,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_746,C_747,'#skF_4'))
      | ~ m1_subset_1(E_748,k1_zfmisc_1(k2_zfmisc_1(C_747,'#skF_2')))
      | ~ v1_funct_2(E_748,C_747,'#skF_2')
      | ~ v1_funct_1(E_748)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_746))
      | ~ m1_subset_1(C_747,k1_zfmisc_1(A_746))
      | v1_xboole_0(C_747)
      | v1_xboole_0(A_746) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_5151])).

tff(c_5856,plain,(
    ! [A_746] :
      ( k2_partfun1(k4_subset_1(A_746,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_746,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_746,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_746,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_746,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_746))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_746))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_746) ) ),
    inference(resolution,[status(thm)],[c_46,c_5849])).

tff(c_5866,plain,(
    ! [A_746] :
      ( k2_partfun1(k4_subset_1(A_746,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_746,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_746,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_746,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_746,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_746))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_746))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_746) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_3374,c_5856])).

tff(c_5868,plain,(
    ! [A_749] :
      ( k2_partfun1(k4_subset_1(A_749,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_749,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_749,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_749,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_749,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_749))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_749))
      | v1_xboole_0(A_749) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_5866])).

tff(c_515,plain,(
    ! [A_266,B_267] :
      ( r1_xboole_0(A_266,B_267)
      | ~ r1_subset_1(A_266,B_267)
      | v1_xboole_0(B_267)
      | v1_xboole_0(A_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_595,plain,(
    ! [A_277,B_278] :
      ( k4_xboole_0(A_277,B_278) = A_277
      | ~ r1_subset_1(A_277,B_278)
      | v1_xboole_0(B_278)
      | v1_xboole_0(A_277) ) ),
    inference(resolution,[status(thm)],[c_515,c_8])).

tff(c_598,plain,
    ( k4_xboole_0('#skF_3','#skF_4') = '#skF_3'
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_595])).

tff(c_601,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_56,c_598])).

tff(c_605,plain,(
    k4_xboole_0('#skF_3','#skF_3') = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_601,c_4])).

tff(c_608,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_605])).

tff(c_545,plain,(
    ! [A_270,B_271,C_272] :
      ( k9_subset_1(A_270,B_271,C_272) = k3_xboole_0(B_271,C_272)
      | ~ m1_subset_1(C_272,k1_zfmisc_1(A_270)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_557,plain,(
    ! [B_271] : k9_subset_1('#skF_1',B_271,'#skF_4') = k3_xboole_0(B_271,'#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_545])).

tff(c_817,plain,(
    ! [C_296,E_297,F_295,A_298,D_293,B_294] :
      ( v1_funct_1(k1_tmap_1(A_298,B_294,C_296,D_293,E_297,F_295))
      | ~ m1_subset_1(F_295,k1_zfmisc_1(k2_zfmisc_1(D_293,B_294)))
      | ~ v1_funct_2(F_295,D_293,B_294)
      | ~ v1_funct_1(F_295)
      | ~ m1_subset_1(E_297,k1_zfmisc_1(k2_zfmisc_1(C_296,B_294)))
      | ~ v1_funct_2(E_297,C_296,B_294)
      | ~ v1_funct_1(E_297)
      | ~ m1_subset_1(D_293,k1_zfmisc_1(A_298))
      | v1_xboole_0(D_293)
      | ~ m1_subset_1(C_296,k1_zfmisc_1(A_298))
      | v1_xboole_0(C_296)
      | v1_xboole_0(B_294)
      | v1_xboole_0(A_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_819,plain,(
    ! [A_298,C_296,E_297] :
      ( v1_funct_1(k1_tmap_1(A_298,'#skF_2',C_296,'#skF_4',E_297,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_297,k1_zfmisc_1(k2_zfmisc_1(C_296,'#skF_2')))
      | ~ v1_funct_2(E_297,C_296,'#skF_2')
      | ~ v1_funct_1(E_297)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_298))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_296,k1_zfmisc_1(A_298))
      | v1_xboole_0(C_296)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_298) ) ),
    inference(resolution,[status(thm)],[c_40,c_817])).

tff(c_824,plain,(
    ! [A_298,C_296,E_297] :
      ( v1_funct_1(k1_tmap_1(A_298,'#skF_2',C_296,'#skF_4',E_297,'#skF_6'))
      | ~ m1_subset_1(E_297,k1_zfmisc_1(k2_zfmisc_1(C_296,'#skF_2')))
      | ~ v1_funct_2(E_297,C_296,'#skF_2')
      | ~ v1_funct_1(E_297)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_298))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_296,k1_zfmisc_1(A_298))
      | v1_xboole_0(C_296)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_298) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_819])).

tff(c_880,plain,(
    ! [A_301,C_302,E_303] :
      ( v1_funct_1(k1_tmap_1(A_301,'#skF_2',C_302,'#skF_4',E_303,'#skF_6'))
      | ~ m1_subset_1(E_303,k1_zfmisc_1(k2_zfmisc_1(C_302,'#skF_2')))
      | ~ v1_funct_2(E_303,C_302,'#skF_2')
      | ~ v1_funct_1(E_303)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_301))
      | ~ m1_subset_1(C_302,k1_zfmisc_1(A_301))
      | v1_xboole_0(C_302)
      | v1_xboole_0(A_301) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_824])).

tff(c_884,plain,(
    ! [A_301] :
      ( v1_funct_1(k1_tmap_1(A_301,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_301))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_301))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_301) ) ),
    inference(resolution,[status(thm)],[c_46,c_880])).

tff(c_891,plain,(
    ! [A_301] :
      ( v1_funct_1(k1_tmap_1(A_301,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_301))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_301))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_301) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_884])).

tff(c_900,plain,(
    ! [A_305] :
      ( v1_funct_1(k1_tmap_1(A_305,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_305))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_305))
      | v1_xboole_0(A_305) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_891])).

tff(c_903,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_900])).

tff(c_906,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_903])).

tff(c_907,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_906])).

tff(c_710,plain,(
    ! [A_285,B_286,C_287,D_288] :
      ( k2_partfun1(A_285,B_286,C_287,D_288) = k7_relat_1(C_287,D_288)
      | ~ m1_subset_1(C_287,k1_zfmisc_1(k2_zfmisc_1(A_285,B_286)))
      | ~ v1_funct_1(C_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_714,plain,(
    ! [D_288] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_288) = k7_relat_1('#skF_5',D_288)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_46,c_710])).

tff(c_720,plain,(
    ! [D_288] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_288) = k7_relat_1('#skF_5',D_288) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_714])).

tff(c_712,plain,(
    ! [D_288] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_288) = k7_relat_1('#skF_6',D_288)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_40,c_710])).

tff(c_717,plain,(
    ! [D_288] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_288) = k7_relat_1('#skF_6',D_288) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_712])).

tff(c_1418,plain,(
    ! [B_352,E_353,F_354,D_355,A_356,C_351] :
      ( k2_partfun1(k4_subset_1(A_356,C_351,D_355),B_352,k1_tmap_1(A_356,B_352,C_351,D_355,E_353,F_354),D_355) = F_354
      | ~ m1_subset_1(k1_tmap_1(A_356,B_352,C_351,D_355,E_353,F_354),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_356,C_351,D_355),B_352)))
      | ~ v1_funct_2(k1_tmap_1(A_356,B_352,C_351,D_355,E_353,F_354),k4_subset_1(A_356,C_351,D_355),B_352)
      | ~ v1_funct_1(k1_tmap_1(A_356,B_352,C_351,D_355,E_353,F_354))
      | k2_partfun1(D_355,B_352,F_354,k9_subset_1(A_356,C_351,D_355)) != k2_partfun1(C_351,B_352,E_353,k9_subset_1(A_356,C_351,D_355))
      | ~ m1_subset_1(F_354,k1_zfmisc_1(k2_zfmisc_1(D_355,B_352)))
      | ~ v1_funct_2(F_354,D_355,B_352)
      | ~ v1_funct_1(F_354)
      | ~ m1_subset_1(E_353,k1_zfmisc_1(k2_zfmisc_1(C_351,B_352)))
      | ~ v1_funct_2(E_353,C_351,B_352)
      | ~ v1_funct_1(E_353)
      | ~ m1_subset_1(D_355,k1_zfmisc_1(A_356))
      | v1_xboole_0(D_355)
      | ~ m1_subset_1(C_351,k1_zfmisc_1(A_356))
      | v1_xboole_0(C_351)
      | v1_xboole_0(B_352)
      | v1_xboole_0(A_356) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2081,plain,(
    ! [D_416,F_418,C_419,E_420,A_421,B_417] :
      ( k2_partfun1(k4_subset_1(A_421,C_419,D_416),B_417,k1_tmap_1(A_421,B_417,C_419,D_416,E_420,F_418),D_416) = F_418
      | ~ v1_funct_2(k1_tmap_1(A_421,B_417,C_419,D_416,E_420,F_418),k4_subset_1(A_421,C_419,D_416),B_417)
      | ~ v1_funct_1(k1_tmap_1(A_421,B_417,C_419,D_416,E_420,F_418))
      | k2_partfun1(D_416,B_417,F_418,k9_subset_1(A_421,C_419,D_416)) != k2_partfun1(C_419,B_417,E_420,k9_subset_1(A_421,C_419,D_416))
      | ~ m1_subset_1(F_418,k1_zfmisc_1(k2_zfmisc_1(D_416,B_417)))
      | ~ v1_funct_2(F_418,D_416,B_417)
      | ~ v1_funct_1(F_418)
      | ~ m1_subset_1(E_420,k1_zfmisc_1(k2_zfmisc_1(C_419,B_417)))
      | ~ v1_funct_2(E_420,C_419,B_417)
      | ~ v1_funct_1(E_420)
      | ~ m1_subset_1(D_416,k1_zfmisc_1(A_421))
      | v1_xboole_0(D_416)
      | ~ m1_subset_1(C_419,k1_zfmisc_1(A_421))
      | v1_xboole_0(C_419)
      | v1_xboole_0(B_417)
      | v1_xboole_0(A_421) ) ),
    inference(resolution,[status(thm)],[c_32,c_1418])).

tff(c_2588,plain,(
    ! [A_460,F_457,D_455,C_458,B_456,E_459] :
      ( k2_partfun1(k4_subset_1(A_460,C_458,D_455),B_456,k1_tmap_1(A_460,B_456,C_458,D_455,E_459,F_457),D_455) = F_457
      | ~ v1_funct_1(k1_tmap_1(A_460,B_456,C_458,D_455,E_459,F_457))
      | k2_partfun1(D_455,B_456,F_457,k9_subset_1(A_460,C_458,D_455)) != k2_partfun1(C_458,B_456,E_459,k9_subset_1(A_460,C_458,D_455))
      | ~ m1_subset_1(F_457,k1_zfmisc_1(k2_zfmisc_1(D_455,B_456)))
      | ~ v1_funct_2(F_457,D_455,B_456)
      | ~ v1_funct_1(F_457)
      | ~ m1_subset_1(E_459,k1_zfmisc_1(k2_zfmisc_1(C_458,B_456)))
      | ~ v1_funct_2(E_459,C_458,B_456)
      | ~ v1_funct_1(E_459)
      | ~ m1_subset_1(D_455,k1_zfmisc_1(A_460))
      | v1_xboole_0(D_455)
      | ~ m1_subset_1(C_458,k1_zfmisc_1(A_460))
      | v1_xboole_0(C_458)
      | v1_xboole_0(B_456)
      | v1_xboole_0(A_460) ) ),
    inference(resolution,[status(thm)],[c_34,c_2081])).

tff(c_2592,plain,(
    ! [A_460,C_458,E_459] :
      ( k2_partfun1(k4_subset_1(A_460,C_458,'#skF_4'),'#skF_2',k1_tmap_1(A_460,'#skF_2',C_458,'#skF_4',E_459,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_460,'#skF_2',C_458,'#skF_4',E_459,'#skF_6'))
      | k2_partfun1(C_458,'#skF_2',E_459,k9_subset_1(A_460,C_458,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_460,C_458,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_459,k1_zfmisc_1(k2_zfmisc_1(C_458,'#skF_2')))
      | ~ v1_funct_2(E_459,C_458,'#skF_2')
      | ~ v1_funct_1(E_459)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_460))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_458,k1_zfmisc_1(A_460))
      | v1_xboole_0(C_458)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_460) ) ),
    inference(resolution,[status(thm)],[c_40,c_2588])).

tff(c_2598,plain,(
    ! [A_460,C_458,E_459] :
      ( k2_partfun1(k4_subset_1(A_460,C_458,'#skF_4'),'#skF_2',k1_tmap_1(A_460,'#skF_2',C_458,'#skF_4',E_459,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_460,'#skF_2',C_458,'#skF_4',E_459,'#skF_6'))
      | k2_partfun1(C_458,'#skF_2',E_459,k9_subset_1(A_460,C_458,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_460,C_458,'#skF_4'))
      | ~ m1_subset_1(E_459,k1_zfmisc_1(k2_zfmisc_1(C_458,'#skF_2')))
      | ~ v1_funct_2(E_459,C_458,'#skF_2')
      | ~ v1_funct_1(E_459)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_460))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_458,k1_zfmisc_1(A_460))
      | v1_xboole_0(C_458)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_460) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_717,c_2592])).

tff(c_3115,plain,(
    ! [A_502,C_503,E_504] :
      ( k2_partfun1(k4_subset_1(A_502,C_503,'#skF_4'),'#skF_2',k1_tmap_1(A_502,'#skF_2',C_503,'#skF_4',E_504,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_502,'#skF_2',C_503,'#skF_4',E_504,'#skF_6'))
      | k2_partfun1(C_503,'#skF_2',E_504,k9_subset_1(A_502,C_503,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_502,C_503,'#skF_4'))
      | ~ m1_subset_1(E_504,k1_zfmisc_1(k2_zfmisc_1(C_503,'#skF_2')))
      | ~ v1_funct_2(E_504,C_503,'#skF_2')
      | ~ v1_funct_1(E_504)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_502))
      | ~ m1_subset_1(C_503,k1_zfmisc_1(A_502))
      | v1_xboole_0(C_503)
      | v1_xboole_0(A_502) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_2598])).

tff(c_3122,plain,(
    ! [A_502] :
      ( k2_partfun1(k4_subset_1(A_502,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_502,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_502,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_502,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_502,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_502))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_502))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_502) ) ),
    inference(resolution,[status(thm)],[c_46,c_3115])).

tff(c_3132,plain,(
    ! [A_502] :
      ( k2_partfun1(k4_subset_1(A_502,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_502,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_502,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_502,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_502,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_502))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_502))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_502) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_720,c_3122])).

tff(c_3134,plain,(
    ! [A_505] :
      ( k2_partfun1(k4_subset_1(A_505,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_505,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_505,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_505,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_505,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_505))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_505))
      | v1_xboole_0(A_505) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_3132])).

tff(c_153,plain,(
    ! [C_225,A_226,B_227] :
      ( v1_relat_1(C_225)
      | ~ m1_subset_1(C_225,k1_zfmisc_1(k2_zfmisc_1(A_226,B_227))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_160,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_153])).

tff(c_165,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_160,c_16])).

tff(c_94,plain,(
    ! [A_221,B_222] : k4_xboole_0(A_221,k4_xboole_0(A_221,B_222)) = k3_xboole_0(A_221,B_222) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_109,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k3_xboole_0(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_94])).

tff(c_112,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_109])).

tff(c_209,plain,(
    ! [A_232,B_233] :
      ( r1_xboole_0(A_232,B_233)
      | ~ r1_subset_1(A_232,B_233)
      | v1_xboole_0(B_233)
      | v1_xboole_0(A_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_318,plain,(
    ! [A_249,B_250] :
      ( k4_xboole_0(A_249,B_250) = A_249
      | ~ r1_subset_1(A_249,B_250)
      | v1_xboole_0(B_250)
      | v1_xboole_0(A_249) ) ),
    inference(resolution,[status(thm)],[c_209,c_8])).

tff(c_321,plain,
    ( k4_xboole_0('#skF_3','#skF_4') = '#skF_3'
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_318])).

tff(c_324,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_56,c_321])).

tff(c_328,plain,(
    k4_xboole_0('#skF_3','#skF_3') = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_4])).

tff(c_331,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_328])).

tff(c_161,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_153])).

tff(c_188,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_161,c_16])).

tff(c_289,plain,(
    ! [A_243,B_244,C_245,D_246] :
      ( k2_partfun1(A_243,B_244,C_245,D_246) = k7_relat_1(C_245,D_246)
      | ~ m1_subset_1(C_245,k1_zfmisc_1(k2_zfmisc_1(A_243,B_244)))
      | ~ v1_funct_1(C_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_293,plain,(
    ! [D_246] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_246) = k7_relat_1('#skF_5',D_246)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_46,c_289])).

tff(c_299,plain,(
    ! [D_246] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_246) = k7_relat_1('#skF_5',D_246) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_293])).

tff(c_291,plain,(
    ! [D_246] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_246) = k7_relat_1('#skF_6',D_246)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_40,c_289])).

tff(c_296,plain,(
    ! [D_246] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_246) = k7_relat_1('#skF_6',D_246) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_291])).

tff(c_239,plain,(
    ! [A_236,B_237,C_238] :
      ( k9_subset_1(A_236,B_237,C_238) = k3_xboole_0(B_237,C_238)
      | ~ m1_subset_1(C_238,k1_zfmisc_1(A_236)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_251,plain,(
    ! [B_237] : k9_subset_1('#skF_1',B_237,'#skF_4') = k3_xboole_0(B_237,'#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_239])).

tff(c_38,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_93,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_261,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_251,c_93])).

tff(c_392,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_331,c_188,c_331,c_299,c_296,c_261])).

tff(c_393,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_513,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_393])).

tff(c_3145,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3134,c_513])).

tff(c_3159,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_426,c_608,c_430,c_608,c_557,c_557,c_907,c_3145])).

tff(c_3161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_3159])).

tff(c_3162,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_393])).

tff(c_5877,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5868,c_3162])).

tff(c_5888,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_426,c_3258,c_430,c_3258,c_3206,c_3206,c_3559,c_5877])).

tff(c_5890,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_5888])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:25:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.17/2.93  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.28/2.95  
% 8.28/2.95  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.28/2.95  %$ v1_funct_2 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.28/2.95  
% 8.28/2.95  %Foreground sorts:
% 8.28/2.95  
% 8.28/2.95  
% 8.28/2.95  %Background operators:
% 8.28/2.95  
% 8.28/2.95  
% 8.28/2.95  %Foreground operators:
% 8.28/2.95  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 8.28/2.95  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.28/2.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.28/2.95  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.28/2.95  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.28/2.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.28/2.95  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 8.28/2.95  tff('#skF_5', type, '#skF_5': $i).
% 8.28/2.95  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.28/2.95  tff('#skF_6', type, '#skF_6': $i).
% 8.28/2.95  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.28/2.95  tff('#skF_2', type, '#skF_2': $i).
% 8.28/2.95  tff('#skF_3', type, '#skF_3': $i).
% 8.28/2.95  tff('#skF_1', type, '#skF_1': $i).
% 8.28/2.95  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.28/2.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.28/2.95  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.28/2.95  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.28/2.95  tff('#skF_4', type, '#skF_4': $i).
% 8.28/2.95  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.28/2.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.28/2.95  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 8.28/2.95  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.28/2.95  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.28/2.95  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 8.28/2.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.28/2.95  
% 8.28/2.98  tff(f_194, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 8.28/2.98  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.28/2.98  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_relat_1)).
% 8.28/2.98  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 8.28/2.98  tff(f_31, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 8.28/2.98  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 8.28/2.98  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.28/2.98  tff(f_60, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 8.28/2.98  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 8.28/2.98  tff(f_152, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 8.28/2.98  tff(f_70, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 8.28/2.98  tff(f_118, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 8.28/2.98  tff(c_64, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_194])).
% 8.28/2.98  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_194])).
% 8.28/2.98  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_194])).
% 8.28/2.98  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_194])).
% 8.28/2.98  tff(c_414, plain, (![C_257, A_258, B_259]: (v1_relat_1(C_257) | ~m1_subset_1(C_257, k1_zfmisc_1(k2_zfmisc_1(A_258, B_259))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.28/2.98  tff(c_421, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_40, c_414])).
% 8.28/2.98  tff(c_16, plain, (![A_13]: (k7_relat_1(A_13, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.28/2.98  tff(c_426, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_421, c_16])).
% 8.28/2.98  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.28/2.98  tff(c_6, plain, (![A_4]: (r1_xboole_0(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.28/2.98  tff(c_75, plain, (![A_218, B_219]: (k4_xboole_0(A_218, B_219)=A_218 | ~r1_xboole_0(A_218, B_219))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.28/2.98  tff(c_83, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(resolution, [status(thm)], [c_6, c_75])).
% 8.28/2.98  tff(c_395, plain, (![A_255, B_256]: (k4_xboole_0(A_255, k4_xboole_0(A_255, B_256))=k3_xboole_0(A_255, B_256))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.28/2.98  tff(c_410, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k3_xboole_0(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_83, c_395])).
% 8.28/2.98  tff(c_413, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_410])).
% 8.28/2.98  tff(c_60, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_194])).
% 8.28/2.98  tff(c_56, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_194])).
% 8.28/2.98  tff(c_52, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_194])).
% 8.28/2.98  tff(c_3165, plain, (![A_506, B_507]: (r1_xboole_0(A_506, B_507) | ~r1_subset_1(A_506, B_507) | v1_xboole_0(B_507) | v1_xboole_0(A_506))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.28/2.98  tff(c_8, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=A_5 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.28/2.98  tff(c_3245, plain, (![A_517, B_518]: (k4_xboole_0(A_517, B_518)=A_517 | ~r1_subset_1(A_517, B_518) | v1_xboole_0(B_518) | v1_xboole_0(A_517))), inference(resolution, [status(thm)], [c_3165, c_8])).
% 8.28/2.98  tff(c_3248, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3' | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_3245])).
% 8.28/2.98  tff(c_3251, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_60, c_56, c_3248])).
% 8.28/2.98  tff(c_4, plain, (![A_2, B_3]: (k4_xboole_0(A_2, k4_xboole_0(A_2, B_3))=k3_xboole_0(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.28/2.98  tff(c_3255, plain, (k4_xboole_0('#skF_3', '#skF_3')=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3251, c_4])).
% 8.28/2.98  tff(c_3258, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_413, c_3255])).
% 8.28/2.98  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_194])).
% 8.28/2.98  tff(c_422, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_414])).
% 8.28/2.98  tff(c_430, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_422, c_16])).
% 8.28/2.98  tff(c_3194, plain, (![A_510, B_511, C_512]: (k9_subset_1(A_510, B_511, C_512)=k3_xboole_0(B_511, C_512) | ~m1_subset_1(C_512, k1_zfmisc_1(A_510)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.28/2.98  tff(c_3206, plain, (![B_511]: (k9_subset_1('#skF_1', B_511, '#skF_4')=k3_xboole_0(B_511, '#skF_4'))), inference(resolution, [status(thm)], [c_54, c_3194])).
% 8.28/2.98  tff(c_50, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_194])).
% 8.28/2.98  tff(c_48, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 8.28/2.98  tff(c_62, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 8.28/2.98  tff(c_44, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_194])).
% 8.28/2.98  tff(c_42, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 8.28/2.98  tff(c_3407, plain, (![B_532, A_536, F_533, C_534, E_535, D_531]: (v1_funct_1(k1_tmap_1(A_536, B_532, C_534, D_531, E_535, F_533)) | ~m1_subset_1(F_533, k1_zfmisc_1(k2_zfmisc_1(D_531, B_532))) | ~v1_funct_2(F_533, D_531, B_532) | ~v1_funct_1(F_533) | ~m1_subset_1(E_535, k1_zfmisc_1(k2_zfmisc_1(C_534, B_532))) | ~v1_funct_2(E_535, C_534, B_532) | ~v1_funct_1(E_535) | ~m1_subset_1(D_531, k1_zfmisc_1(A_536)) | v1_xboole_0(D_531) | ~m1_subset_1(C_534, k1_zfmisc_1(A_536)) | v1_xboole_0(C_534) | v1_xboole_0(B_532) | v1_xboole_0(A_536))), inference(cnfTransformation, [status(thm)], [f_152])).
% 8.28/2.98  tff(c_3409, plain, (![A_536, C_534, E_535]: (v1_funct_1(k1_tmap_1(A_536, '#skF_2', C_534, '#skF_4', E_535, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_535, k1_zfmisc_1(k2_zfmisc_1(C_534, '#skF_2'))) | ~v1_funct_2(E_535, C_534, '#skF_2') | ~v1_funct_1(E_535) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_536)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_534, k1_zfmisc_1(A_536)) | v1_xboole_0(C_534) | v1_xboole_0('#skF_2') | v1_xboole_0(A_536))), inference(resolution, [status(thm)], [c_40, c_3407])).
% 8.28/2.98  tff(c_3414, plain, (![A_536, C_534, E_535]: (v1_funct_1(k1_tmap_1(A_536, '#skF_2', C_534, '#skF_4', E_535, '#skF_6')) | ~m1_subset_1(E_535, k1_zfmisc_1(k2_zfmisc_1(C_534, '#skF_2'))) | ~v1_funct_2(E_535, C_534, '#skF_2') | ~v1_funct_1(E_535) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_536)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_534, k1_zfmisc_1(A_536)) | v1_xboole_0(C_534) | v1_xboole_0('#skF_2') | v1_xboole_0(A_536))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_3409])).
% 8.28/2.98  tff(c_3532, plain, (![A_541, C_542, E_543]: (v1_funct_1(k1_tmap_1(A_541, '#skF_2', C_542, '#skF_4', E_543, '#skF_6')) | ~m1_subset_1(E_543, k1_zfmisc_1(k2_zfmisc_1(C_542, '#skF_2'))) | ~v1_funct_2(E_543, C_542, '#skF_2') | ~v1_funct_1(E_543) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_541)) | ~m1_subset_1(C_542, k1_zfmisc_1(A_541)) | v1_xboole_0(C_542) | v1_xboole_0(A_541))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_3414])).
% 8.28/2.98  tff(c_3536, plain, (![A_541]: (v1_funct_1(k1_tmap_1(A_541, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_541)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_541)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_541))), inference(resolution, [status(thm)], [c_46, c_3532])).
% 8.28/2.98  tff(c_3543, plain, (![A_541]: (v1_funct_1(k1_tmap_1(A_541, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_541)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_541)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_541))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_3536])).
% 8.28/2.98  tff(c_3552, plain, (![A_545]: (v1_funct_1(k1_tmap_1(A_545, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_545)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_545)) | v1_xboole_0(A_545))), inference(negUnitSimplification, [status(thm)], [c_60, c_3543])).
% 8.28/2.98  tff(c_3555, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_58, c_3552])).
% 8.28/2.98  tff(c_3558, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3555])).
% 8.28/2.98  tff(c_3559, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_64, c_3558])).
% 8.28/2.98  tff(c_3364, plain, (![A_525, B_526, C_527, D_528]: (k2_partfun1(A_525, B_526, C_527, D_528)=k7_relat_1(C_527, D_528) | ~m1_subset_1(C_527, k1_zfmisc_1(k2_zfmisc_1(A_525, B_526))) | ~v1_funct_1(C_527))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.28/2.98  tff(c_3368, plain, (![D_528]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_528)=k7_relat_1('#skF_5', D_528) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_46, c_3364])).
% 8.28/2.98  tff(c_3374, plain, (![D_528]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_528)=k7_relat_1('#skF_5', D_528))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_3368])).
% 8.28/2.98  tff(c_3366, plain, (![D_528]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_528)=k7_relat_1('#skF_6', D_528) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_40, c_3364])).
% 8.28/2.98  tff(c_3371, plain, (![D_528]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_528)=k7_relat_1('#skF_6', D_528))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_3366])).
% 8.28/2.98  tff(c_34, plain, (![C_152, F_155, D_153, A_150, B_151, E_154]: (v1_funct_2(k1_tmap_1(A_150, B_151, C_152, D_153, E_154, F_155), k4_subset_1(A_150, C_152, D_153), B_151) | ~m1_subset_1(F_155, k1_zfmisc_1(k2_zfmisc_1(D_153, B_151))) | ~v1_funct_2(F_155, D_153, B_151) | ~v1_funct_1(F_155) | ~m1_subset_1(E_154, k1_zfmisc_1(k2_zfmisc_1(C_152, B_151))) | ~v1_funct_2(E_154, C_152, B_151) | ~v1_funct_1(E_154) | ~m1_subset_1(D_153, k1_zfmisc_1(A_150)) | v1_xboole_0(D_153) | ~m1_subset_1(C_152, k1_zfmisc_1(A_150)) | v1_xboole_0(C_152) | v1_xboole_0(B_151) | v1_xboole_0(A_150))), inference(cnfTransformation, [status(thm)], [f_152])).
% 8.28/2.98  tff(c_32, plain, (![C_152, F_155, D_153, A_150, B_151, E_154]: (m1_subset_1(k1_tmap_1(A_150, B_151, C_152, D_153, E_154, F_155), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_150, C_152, D_153), B_151))) | ~m1_subset_1(F_155, k1_zfmisc_1(k2_zfmisc_1(D_153, B_151))) | ~v1_funct_2(F_155, D_153, B_151) | ~v1_funct_1(F_155) | ~m1_subset_1(E_154, k1_zfmisc_1(k2_zfmisc_1(C_152, B_151))) | ~v1_funct_2(E_154, C_152, B_151) | ~v1_funct_1(E_154) | ~m1_subset_1(D_153, k1_zfmisc_1(A_150)) | v1_xboole_0(D_153) | ~m1_subset_1(C_152, k1_zfmisc_1(A_150)) | v1_xboole_0(C_152) | v1_xboole_0(B_151) | v1_xboole_0(A_150))), inference(cnfTransformation, [status(thm)], [f_152])).
% 8.28/2.98  tff(c_3870, plain, (![B_576, E_577, D_579, C_575, F_578, A_580]: (k2_partfun1(k4_subset_1(A_580, C_575, D_579), B_576, k1_tmap_1(A_580, B_576, C_575, D_579, E_577, F_578), C_575)=E_577 | ~m1_subset_1(k1_tmap_1(A_580, B_576, C_575, D_579, E_577, F_578), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_580, C_575, D_579), B_576))) | ~v1_funct_2(k1_tmap_1(A_580, B_576, C_575, D_579, E_577, F_578), k4_subset_1(A_580, C_575, D_579), B_576) | ~v1_funct_1(k1_tmap_1(A_580, B_576, C_575, D_579, E_577, F_578)) | k2_partfun1(D_579, B_576, F_578, k9_subset_1(A_580, C_575, D_579))!=k2_partfun1(C_575, B_576, E_577, k9_subset_1(A_580, C_575, D_579)) | ~m1_subset_1(F_578, k1_zfmisc_1(k2_zfmisc_1(D_579, B_576))) | ~v1_funct_2(F_578, D_579, B_576) | ~v1_funct_1(F_578) | ~m1_subset_1(E_577, k1_zfmisc_1(k2_zfmisc_1(C_575, B_576))) | ~v1_funct_2(E_577, C_575, B_576) | ~v1_funct_1(E_577) | ~m1_subset_1(D_579, k1_zfmisc_1(A_580)) | v1_xboole_0(D_579) | ~m1_subset_1(C_575, k1_zfmisc_1(A_580)) | v1_xboole_0(C_575) | v1_xboole_0(B_576) | v1_xboole_0(A_580))), inference(cnfTransformation, [status(thm)], [f_118])).
% 8.28/2.98  tff(c_4872, plain, (![C_669, B_667, E_670, D_666, A_671, F_668]: (k2_partfun1(k4_subset_1(A_671, C_669, D_666), B_667, k1_tmap_1(A_671, B_667, C_669, D_666, E_670, F_668), C_669)=E_670 | ~v1_funct_2(k1_tmap_1(A_671, B_667, C_669, D_666, E_670, F_668), k4_subset_1(A_671, C_669, D_666), B_667) | ~v1_funct_1(k1_tmap_1(A_671, B_667, C_669, D_666, E_670, F_668)) | k2_partfun1(D_666, B_667, F_668, k9_subset_1(A_671, C_669, D_666))!=k2_partfun1(C_669, B_667, E_670, k9_subset_1(A_671, C_669, D_666)) | ~m1_subset_1(F_668, k1_zfmisc_1(k2_zfmisc_1(D_666, B_667))) | ~v1_funct_2(F_668, D_666, B_667) | ~v1_funct_1(F_668) | ~m1_subset_1(E_670, k1_zfmisc_1(k2_zfmisc_1(C_669, B_667))) | ~v1_funct_2(E_670, C_669, B_667) | ~v1_funct_1(E_670) | ~m1_subset_1(D_666, k1_zfmisc_1(A_671)) | v1_xboole_0(D_666) | ~m1_subset_1(C_669, k1_zfmisc_1(A_671)) | v1_xboole_0(C_669) | v1_xboole_0(B_667) | v1_xboole_0(A_671))), inference(resolution, [status(thm)], [c_32, c_3870])).
% 8.28/2.98  tff(c_5141, plain, (![F_695, C_696, D_693, A_698, E_697, B_694]: (k2_partfun1(k4_subset_1(A_698, C_696, D_693), B_694, k1_tmap_1(A_698, B_694, C_696, D_693, E_697, F_695), C_696)=E_697 | ~v1_funct_1(k1_tmap_1(A_698, B_694, C_696, D_693, E_697, F_695)) | k2_partfun1(D_693, B_694, F_695, k9_subset_1(A_698, C_696, D_693))!=k2_partfun1(C_696, B_694, E_697, k9_subset_1(A_698, C_696, D_693)) | ~m1_subset_1(F_695, k1_zfmisc_1(k2_zfmisc_1(D_693, B_694))) | ~v1_funct_2(F_695, D_693, B_694) | ~v1_funct_1(F_695) | ~m1_subset_1(E_697, k1_zfmisc_1(k2_zfmisc_1(C_696, B_694))) | ~v1_funct_2(E_697, C_696, B_694) | ~v1_funct_1(E_697) | ~m1_subset_1(D_693, k1_zfmisc_1(A_698)) | v1_xboole_0(D_693) | ~m1_subset_1(C_696, k1_zfmisc_1(A_698)) | v1_xboole_0(C_696) | v1_xboole_0(B_694) | v1_xboole_0(A_698))), inference(resolution, [status(thm)], [c_34, c_4872])).
% 8.28/2.98  tff(c_5145, plain, (![A_698, C_696, E_697]: (k2_partfun1(k4_subset_1(A_698, C_696, '#skF_4'), '#skF_2', k1_tmap_1(A_698, '#skF_2', C_696, '#skF_4', E_697, '#skF_6'), C_696)=E_697 | ~v1_funct_1(k1_tmap_1(A_698, '#skF_2', C_696, '#skF_4', E_697, '#skF_6')) | k2_partfun1(C_696, '#skF_2', E_697, k9_subset_1(A_698, C_696, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_698, C_696, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_697, k1_zfmisc_1(k2_zfmisc_1(C_696, '#skF_2'))) | ~v1_funct_2(E_697, C_696, '#skF_2') | ~v1_funct_1(E_697) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_698)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_696, k1_zfmisc_1(A_698)) | v1_xboole_0(C_696) | v1_xboole_0('#skF_2') | v1_xboole_0(A_698))), inference(resolution, [status(thm)], [c_40, c_5141])).
% 8.28/2.98  tff(c_5151, plain, (![A_698, C_696, E_697]: (k2_partfun1(k4_subset_1(A_698, C_696, '#skF_4'), '#skF_2', k1_tmap_1(A_698, '#skF_2', C_696, '#skF_4', E_697, '#skF_6'), C_696)=E_697 | ~v1_funct_1(k1_tmap_1(A_698, '#skF_2', C_696, '#skF_4', E_697, '#skF_6')) | k2_partfun1(C_696, '#skF_2', E_697, k9_subset_1(A_698, C_696, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_698, C_696, '#skF_4')) | ~m1_subset_1(E_697, k1_zfmisc_1(k2_zfmisc_1(C_696, '#skF_2'))) | ~v1_funct_2(E_697, C_696, '#skF_2') | ~v1_funct_1(E_697) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_698)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_696, k1_zfmisc_1(A_698)) | v1_xboole_0(C_696) | v1_xboole_0('#skF_2') | v1_xboole_0(A_698))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_3371, c_5145])).
% 8.28/2.98  tff(c_5849, plain, (![A_746, C_747, E_748]: (k2_partfun1(k4_subset_1(A_746, C_747, '#skF_4'), '#skF_2', k1_tmap_1(A_746, '#skF_2', C_747, '#skF_4', E_748, '#skF_6'), C_747)=E_748 | ~v1_funct_1(k1_tmap_1(A_746, '#skF_2', C_747, '#skF_4', E_748, '#skF_6')) | k2_partfun1(C_747, '#skF_2', E_748, k9_subset_1(A_746, C_747, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_746, C_747, '#skF_4')) | ~m1_subset_1(E_748, k1_zfmisc_1(k2_zfmisc_1(C_747, '#skF_2'))) | ~v1_funct_2(E_748, C_747, '#skF_2') | ~v1_funct_1(E_748) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_746)) | ~m1_subset_1(C_747, k1_zfmisc_1(A_746)) | v1_xboole_0(C_747) | v1_xboole_0(A_746))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_5151])).
% 8.28/2.98  tff(c_5856, plain, (![A_746]: (k2_partfun1(k4_subset_1(A_746, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_746, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_746, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_746, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_746, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_746)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_746)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_746))), inference(resolution, [status(thm)], [c_46, c_5849])).
% 8.28/2.98  tff(c_5866, plain, (![A_746]: (k2_partfun1(k4_subset_1(A_746, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_746, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_746, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_746, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_746, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_746)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_746)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_746))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_3374, c_5856])).
% 8.28/2.98  tff(c_5868, plain, (![A_749]: (k2_partfun1(k4_subset_1(A_749, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_749, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_749, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_749, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_749, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_749)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_749)) | v1_xboole_0(A_749))), inference(negUnitSimplification, [status(thm)], [c_60, c_5866])).
% 8.28/2.98  tff(c_515, plain, (![A_266, B_267]: (r1_xboole_0(A_266, B_267) | ~r1_subset_1(A_266, B_267) | v1_xboole_0(B_267) | v1_xboole_0(A_266))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.28/2.98  tff(c_595, plain, (![A_277, B_278]: (k4_xboole_0(A_277, B_278)=A_277 | ~r1_subset_1(A_277, B_278) | v1_xboole_0(B_278) | v1_xboole_0(A_277))), inference(resolution, [status(thm)], [c_515, c_8])).
% 8.28/2.98  tff(c_598, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3' | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_595])).
% 8.28/2.98  tff(c_601, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_60, c_56, c_598])).
% 8.28/2.98  tff(c_605, plain, (k4_xboole_0('#skF_3', '#skF_3')=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_601, c_4])).
% 8.28/2.98  tff(c_608, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_413, c_605])).
% 8.28/2.98  tff(c_545, plain, (![A_270, B_271, C_272]: (k9_subset_1(A_270, B_271, C_272)=k3_xboole_0(B_271, C_272) | ~m1_subset_1(C_272, k1_zfmisc_1(A_270)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.28/2.98  tff(c_557, plain, (![B_271]: (k9_subset_1('#skF_1', B_271, '#skF_4')=k3_xboole_0(B_271, '#skF_4'))), inference(resolution, [status(thm)], [c_54, c_545])).
% 8.28/2.98  tff(c_817, plain, (![C_296, E_297, F_295, A_298, D_293, B_294]: (v1_funct_1(k1_tmap_1(A_298, B_294, C_296, D_293, E_297, F_295)) | ~m1_subset_1(F_295, k1_zfmisc_1(k2_zfmisc_1(D_293, B_294))) | ~v1_funct_2(F_295, D_293, B_294) | ~v1_funct_1(F_295) | ~m1_subset_1(E_297, k1_zfmisc_1(k2_zfmisc_1(C_296, B_294))) | ~v1_funct_2(E_297, C_296, B_294) | ~v1_funct_1(E_297) | ~m1_subset_1(D_293, k1_zfmisc_1(A_298)) | v1_xboole_0(D_293) | ~m1_subset_1(C_296, k1_zfmisc_1(A_298)) | v1_xboole_0(C_296) | v1_xboole_0(B_294) | v1_xboole_0(A_298))), inference(cnfTransformation, [status(thm)], [f_152])).
% 8.28/2.98  tff(c_819, plain, (![A_298, C_296, E_297]: (v1_funct_1(k1_tmap_1(A_298, '#skF_2', C_296, '#skF_4', E_297, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_297, k1_zfmisc_1(k2_zfmisc_1(C_296, '#skF_2'))) | ~v1_funct_2(E_297, C_296, '#skF_2') | ~v1_funct_1(E_297) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_298)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_296, k1_zfmisc_1(A_298)) | v1_xboole_0(C_296) | v1_xboole_0('#skF_2') | v1_xboole_0(A_298))), inference(resolution, [status(thm)], [c_40, c_817])).
% 8.28/2.98  tff(c_824, plain, (![A_298, C_296, E_297]: (v1_funct_1(k1_tmap_1(A_298, '#skF_2', C_296, '#skF_4', E_297, '#skF_6')) | ~m1_subset_1(E_297, k1_zfmisc_1(k2_zfmisc_1(C_296, '#skF_2'))) | ~v1_funct_2(E_297, C_296, '#skF_2') | ~v1_funct_1(E_297) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_298)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_296, k1_zfmisc_1(A_298)) | v1_xboole_0(C_296) | v1_xboole_0('#skF_2') | v1_xboole_0(A_298))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_819])).
% 8.28/2.98  tff(c_880, plain, (![A_301, C_302, E_303]: (v1_funct_1(k1_tmap_1(A_301, '#skF_2', C_302, '#skF_4', E_303, '#skF_6')) | ~m1_subset_1(E_303, k1_zfmisc_1(k2_zfmisc_1(C_302, '#skF_2'))) | ~v1_funct_2(E_303, C_302, '#skF_2') | ~v1_funct_1(E_303) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_301)) | ~m1_subset_1(C_302, k1_zfmisc_1(A_301)) | v1_xboole_0(C_302) | v1_xboole_0(A_301))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_824])).
% 8.28/2.98  tff(c_884, plain, (![A_301]: (v1_funct_1(k1_tmap_1(A_301, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_301)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_301)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_301))), inference(resolution, [status(thm)], [c_46, c_880])).
% 8.28/2.98  tff(c_891, plain, (![A_301]: (v1_funct_1(k1_tmap_1(A_301, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_301)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_301)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_301))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_884])).
% 8.28/2.98  tff(c_900, plain, (![A_305]: (v1_funct_1(k1_tmap_1(A_305, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_305)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_305)) | v1_xboole_0(A_305))), inference(negUnitSimplification, [status(thm)], [c_60, c_891])).
% 8.28/2.98  tff(c_903, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_58, c_900])).
% 8.28/2.98  tff(c_906, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_903])).
% 8.28/2.98  tff(c_907, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_64, c_906])).
% 8.28/2.98  tff(c_710, plain, (![A_285, B_286, C_287, D_288]: (k2_partfun1(A_285, B_286, C_287, D_288)=k7_relat_1(C_287, D_288) | ~m1_subset_1(C_287, k1_zfmisc_1(k2_zfmisc_1(A_285, B_286))) | ~v1_funct_1(C_287))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.28/2.98  tff(c_714, plain, (![D_288]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_288)=k7_relat_1('#skF_5', D_288) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_46, c_710])).
% 8.28/2.98  tff(c_720, plain, (![D_288]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_288)=k7_relat_1('#skF_5', D_288))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_714])).
% 8.28/2.98  tff(c_712, plain, (![D_288]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_288)=k7_relat_1('#skF_6', D_288) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_40, c_710])).
% 8.28/2.98  tff(c_717, plain, (![D_288]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_288)=k7_relat_1('#skF_6', D_288))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_712])).
% 8.28/2.98  tff(c_1418, plain, (![B_352, E_353, F_354, D_355, A_356, C_351]: (k2_partfun1(k4_subset_1(A_356, C_351, D_355), B_352, k1_tmap_1(A_356, B_352, C_351, D_355, E_353, F_354), D_355)=F_354 | ~m1_subset_1(k1_tmap_1(A_356, B_352, C_351, D_355, E_353, F_354), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_356, C_351, D_355), B_352))) | ~v1_funct_2(k1_tmap_1(A_356, B_352, C_351, D_355, E_353, F_354), k4_subset_1(A_356, C_351, D_355), B_352) | ~v1_funct_1(k1_tmap_1(A_356, B_352, C_351, D_355, E_353, F_354)) | k2_partfun1(D_355, B_352, F_354, k9_subset_1(A_356, C_351, D_355))!=k2_partfun1(C_351, B_352, E_353, k9_subset_1(A_356, C_351, D_355)) | ~m1_subset_1(F_354, k1_zfmisc_1(k2_zfmisc_1(D_355, B_352))) | ~v1_funct_2(F_354, D_355, B_352) | ~v1_funct_1(F_354) | ~m1_subset_1(E_353, k1_zfmisc_1(k2_zfmisc_1(C_351, B_352))) | ~v1_funct_2(E_353, C_351, B_352) | ~v1_funct_1(E_353) | ~m1_subset_1(D_355, k1_zfmisc_1(A_356)) | v1_xboole_0(D_355) | ~m1_subset_1(C_351, k1_zfmisc_1(A_356)) | v1_xboole_0(C_351) | v1_xboole_0(B_352) | v1_xboole_0(A_356))), inference(cnfTransformation, [status(thm)], [f_118])).
% 8.28/2.98  tff(c_2081, plain, (![D_416, F_418, C_419, E_420, A_421, B_417]: (k2_partfun1(k4_subset_1(A_421, C_419, D_416), B_417, k1_tmap_1(A_421, B_417, C_419, D_416, E_420, F_418), D_416)=F_418 | ~v1_funct_2(k1_tmap_1(A_421, B_417, C_419, D_416, E_420, F_418), k4_subset_1(A_421, C_419, D_416), B_417) | ~v1_funct_1(k1_tmap_1(A_421, B_417, C_419, D_416, E_420, F_418)) | k2_partfun1(D_416, B_417, F_418, k9_subset_1(A_421, C_419, D_416))!=k2_partfun1(C_419, B_417, E_420, k9_subset_1(A_421, C_419, D_416)) | ~m1_subset_1(F_418, k1_zfmisc_1(k2_zfmisc_1(D_416, B_417))) | ~v1_funct_2(F_418, D_416, B_417) | ~v1_funct_1(F_418) | ~m1_subset_1(E_420, k1_zfmisc_1(k2_zfmisc_1(C_419, B_417))) | ~v1_funct_2(E_420, C_419, B_417) | ~v1_funct_1(E_420) | ~m1_subset_1(D_416, k1_zfmisc_1(A_421)) | v1_xboole_0(D_416) | ~m1_subset_1(C_419, k1_zfmisc_1(A_421)) | v1_xboole_0(C_419) | v1_xboole_0(B_417) | v1_xboole_0(A_421))), inference(resolution, [status(thm)], [c_32, c_1418])).
% 8.28/2.98  tff(c_2588, plain, (![A_460, F_457, D_455, C_458, B_456, E_459]: (k2_partfun1(k4_subset_1(A_460, C_458, D_455), B_456, k1_tmap_1(A_460, B_456, C_458, D_455, E_459, F_457), D_455)=F_457 | ~v1_funct_1(k1_tmap_1(A_460, B_456, C_458, D_455, E_459, F_457)) | k2_partfun1(D_455, B_456, F_457, k9_subset_1(A_460, C_458, D_455))!=k2_partfun1(C_458, B_456, E_459, k9_subset_1(A_460, C_458, D_455)) | ~m1_subset_1(F_457, k1_zfmisc_1(k2_zfmisc_1(D_455, B_456))) | ~v1_funct_2(F_457, D_455, B_456) | ~v1_funct_1(F_457) | ~m1_subset_1(E_459, k1_zfmisc_1(k2_zfmisc_1(C_458, B_456))) | ~v1_funct_2(E_459, C_458, B_456) | ~v1_funct_1(E_459) | ~m1_subset_1(D_455, k1_zfmisc_1(A_460)) | v1_xboole_0(D_455) | ~m1_subset_1(C_458, k1_zfmisc_1(A_460)) | v1_xboole_0(C_458) | v1_xboole_0(B_456) | v1_xboole_0(A_460))), inference(resolution, [status(thm)], [c_34, c_2081])).
% 8.28/2.98  tff(c_2592, plain, (![A_460, C_458, E_459]: (k2_partfun1(k4_subset_1(A_460, C_458, '#skF_4'), '#skF_2', k1_tmap_1(A_460, '#skF_2', C_458, '#skF_4', E_459, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_460, '#skF_2', C_458, '#skF_4', E_459, '#skF_6')) | k2_partfun1(C_458, '#skF_2', E_459, k9_subset_1(A_460, C_458, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_460, C_458, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_459, k1_zfmisc_1(k2_zfmisc_1(C_458, '#skF_2'))) | ~v1_funct_2(E_459, C_458, '#skF_2') | ~v1_funct_1(E_459) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_460)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_458, k1_zfmisc_1(A_460)) | v1_xboole_0(C_458) | v1_xboole_0('#skF_2') | v1_xboole_0(A_460))), inference(resolution, [status(thm)], [c_40, c_2588])).
% 8.28/2.98  tff(c_2598, plain, (![A_460, C_458, E_459]: (k2_partfun1(k4_subset_1(A_460, C_458, '#skF_4'), '#skF_2', k1_tmap_1(A_460, '#skF_2', C_458, '#skF_4', E_459, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_460, '#skF_2', C_458, '#skF_4', E_459, '#skF_6')) | k2_partfun1(C_458, '#skF_2', E_459, k9_subset_1(A_460, C_458, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_460, C_458, '#skF_4')) | ~m1_subset_1(E_459, k1_zfmisc_1(k2_zfmisc_1(C_458, '#skF_2'))) | ~v1_funct_2(E_459, C_458, '#skF_2') | ~v1_funct_1(E_459) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_460)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_458, k1_zfmisc_1(A_460)) | v1_xboole_0(C_458) | v1_xboole_0('#skF_2') | v1_xboole_0(A_460))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_717, c_2592])).
% 8.28/2.98  tff(c_3115, plain, (![A_502, C_503, E_504]: (k2_partfun1(k4_subset_1(A_502, C_503, '#skF_4'), '#skF_2', k1_tmap_1(A_502, '#skF_2', C_503, '#skF_4', E_504, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_502, '#skF_2', C_503, '#skF_4', E_504, '#skF_6')) | k2_partfun1(C_503, '#skF_2', E_504, k9_subset_1(A_502, C_503, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_502, C_503, '#skF_4')) | ~m1_subset_1(E_504, k1_zfmisc_1(k2_zfmisc_1(C_503, '#skF_2'))) | ~v1_funct_2(E_504, C_503, '#skF_2') | ~v1_funct_1(E_504) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_502)) | ~m1_subset_1(C_503, k1_zfmisc_1(A_502)) | v1_xboole_0(C_503) | v1_xboole_0(A_502))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_2598])).
% 8.28/2.98  tff(c_3122, plain, (![A_502]: (k2_partfun1(k4_subset_1(A_502, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_502, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_502, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_502, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_502, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_502)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_502)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_502))), inference(resolution, [status(thm)], [c_46, c_3115])).
% 8.28/2.98  tff(c_3132, plain, (![A_502]: (k2_partfun1(k4_subset_1(A_502, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_502, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_502, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_502, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_502, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_502)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_502)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_502))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_720, c_3122])).
% 8.28/2.98  tff(c_3134, plain, (![A_505]: (k2_partfun1(k4_subset_1(A_505, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_505, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_505, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_505, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_505, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_505)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_505)) | v1_xboole_0(A_505))), inference(negUnitSimplification, [status(thm)], [c_60, c_3132])).
% 8.28/2.98  tff(c_153, plain, (![C_225, A_226, B_227]: (v1_relat_1(C_225) | ~m1_subset_1(C_225, k1_zfmisc_1(k2_zfmisc_1(A_226, B_227))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.28/2.98  tff(c_160, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_40, c_153])).
% 8.28/2.98  tff(c_165, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_160, c_16])).
% 8.28/2.98  tff(c_94, plain, (![A_221, B_222]: (k4_xboole_0(A_221, k4_xboole_0(A_221, B_222))=k3_xboole_0(A_221, B_222))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.28/2.98  tff(c_109, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k3_xboole_0(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_83, c_94])).
% 8.28/2.98  tff(c_112, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_109])).
% 8.28/2.98  tff(c_209, plain, (![A_232, B_233]: (r1_xboole_0(A_232, B_233) | ~r1_subset_1(A_232, B_233) | v1_xboole_0(B_233) | v1_xboole_0(A_232))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.28/2.98  tff(c_318, plain, (![A_249, B_250]: (k4_xboole_0(A_249, B_250)=A_249 | ~r1_subset_1(A_249, B_250) | v1_xboole_0(B_250) | v1_xboole_0(A_249))), inference(resolution, [status(thm)], [c_209, c_8])).
% 8.28/2.98  tff(c_321, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3' | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_318])).
% 8.28/2.98  tff(c_324, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_60, c_56, c_321])).
% 8.28/2.98  tff(c_328, plain, (k4_xboole_0('#skF_3', '#skF_3')=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_324, c_4])).
% 8.28/2.98  tff(c_331, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_112, c_328])).
% 8.28/2.98  tff(c_161, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_153])).
% 8.28/2.98  tff(c_188, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_161, c_16])).
% 8.28/2.98  tff(c_289, plain, (![A_243, B_244, C_245, D_246]: (k2_partfun1(A_243, B_244, C_245, D_246)=k7_relat_1(C_245, D_246) | ~m1_subset_1(C_245, k1_zfmisc_1(k2_zfmisc_1(A_243, B_244))) | ~v1_funct_1(C_245))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.28/2.98  tff(c_293, plain, (![D_246]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_246)=k7_relat_1('#skF_5', D_246) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_46, c_289])).
% 8.28/2.98  tff(c_299, plain, (![D_246]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_246)=k7_relat_1('#skF_5', D_246))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_293])).
% 8.28/2.98  tff(c_291, plain, (![D_246]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_246)=k7_relat_1('#skF_6', D_246) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_40, c_289])).
% 8.28/2.98  tff(c_296, plain, (![D_246]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_246)=k7_relat_1('#skF_6', D_246))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_291])).
% 8.28/2.98  tff(c_239, plain, (![A_236, B_237, C_238]: (k9_subset_1(A_236, B_237, C_238)=k3_xboole_0(B_237, C_238) | ~m1_subset_1(C_238, k1_zfmisc_1(A_236)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.28/2.98  tff(c_251, plain, (![B_237]: (k9_subset_1('#skF_1', B_237, '#skF_4')=k3_xboole_0(B_237, '#skF_4'))), inference(resolution, [status(thm)], [c_54, c_239])).
% 8.28/2.98  tff(c_38, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_194])).
% 8.28/2.98  tff(c_93, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_38])).
% 8.28/2.98  tff(c_261, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_251, c_251, c_93])).
% 8.28/2.98  tff(c_392, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_165, c_331, c_188, c_331, c_299, c_296, c_261])).
% 8.28/2.98  tff(c_393, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_38])).
% 8.28/2.98  tff(c_513, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_393])).
% 8.28/2.98  tff(c_3145, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3134, c_513])).
% 8.28/2.98  tff(c_3159, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_426, c_608, c_430, c_608, c_557, c_557, c_907, c_3145])).
% 8.28/2.98  tff(c_3161, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_3159])).
% 8.28/2.98  tff(c_3162, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_393])).
% 8.28/2.98  tff(c_5877, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5868, c_3162])).
% 8.28/2.98  tff(c_5888, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_426, c_3258, c_430, c_3258, c_3206, c_3206, c_3559, c_5877])).
% 8.28/2.98  tff(c_5890, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_5888])).
% 8.28/2.98  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.28/2.98  
% 8.28/2.98  Inference rules
% 8.28/2.98  ----------------------
% 8.28/2.98  #Ref     : 0
% 8.28/2.98  #Sup     : 1399
% 8.28/2.98  #Fact    : 0
% 8.28/2.98  #Define  : 0
% 8.28/2.98  #Split   : 9
% 8.28/2.98  #Chain   : 0
% 8.28/2.98  #Close   : 0
% 8.28/2.98  
% 8.28/2.98  Ordering : KBO
% 8.28/2.98  
% 8.28/2.98  Simplification rules
% 8.28/2.98  ----------------------
% 8.28/2.98  #Subsume      : 19
% 8.28/2.98  #Demod        : 3138
% 8.28/2.98  #Tautology    : 901
% 8.28/2.98  #SimpNegUnit  : 129
% 8.28/2.98  #BackRed      : 5
% 8.28/2.98  
% 8.28/2.98  #Partial instantiations: 0
% 8.28/2.98  #Strategies tried      : 1
% 8.28/2.98  
% 8.28/2.98  Timing (in seconds)
% 8.28/2.98  ----------------------
% 8.28/2.98  Preprocessing        : 0.41
% 8.28/2.98  Parsing              : 0.20
% 8.28/2.98  CNF conversion       : 0.06
% 8.28/2.98  Main loop            : 1.74
% 8.28/2.98  Inferencing          : 0.56
% 8.28/2.98  Reduction            : 0.78
% 8.28/2.98  Demodulation         : 0.68
% 8.28/2.98  BG Simplification    : 0.07
% 8.28/2.98  Subsumption          : 0.26
% 8.28/2.98  Abstraction          : 0.11
% 8.28/2.98  MUC search           : 0.00
% 8.28/2.98  Cooper               : 0.00
% 8.28/2.98  Total                : 2.21
% 8.28/2.98  Index Insertion      : 0.00
% 8.28/2.98  Index Deletion       : 0.00
% 8.28/2.98  Index Matching       : 0.00
% 8.28/2.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
