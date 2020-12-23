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

% Result     : Theorem 5.24s
% Output     : CNFRefutation 5.41s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 413 expanded)
%              Number of leaves         :   36 ( 169 expanded)
%              Depth                    :   12
%              Number of atoms          :  545 (2432 expanded)
%              Number of equality atoms :   87 ( 438 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_192,negated_conjecture,(
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

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_150,axiom,(
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

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_116,axiom,(
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

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_56,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_306,plain,(
    ! [C_252,A_253,B_254] :
      ( v1_relat_1(C_252)
      | ~ m1_subset_1(C_252,k1_zfmisc_1(k2_zfmisc_1(A_253,B_254))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_314,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_306])).

tff(c_6,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_315,plain,(
    ! [B_255,A_256] :
      ( k7_relat_1(B_255,A_256) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_255),A_256)
      | ~ v1_relat_1(B_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_326,plain,(
    ! [B_257] :
      ( k7_relat_1(B_257,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_257) ) ),
    inference(resolution,[status(thm)],[c_6,c_315])).

tff(c_333,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_314,c_326])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_313,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_306])).

tff(c_334,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_313,c_326])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_50,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_370,plain,(
    ! [A_262,B_263] :
      ( r1_xboole_0(A_262,B_263)
      | ~ r1_subset_1(A_262,B_263)
      | v1_xboole_0(B_263)
      | v1_xboole_0(A_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_464,plain,(
    ! [A_277,B_278] :
      ( k3_xboole_0(A_277,B_278) = k1_xboole_0
      | ~ r1_subset_1(A_277,B_278)
      | v1_xboole_0(B_278)
      | v1_xboole_0(A_277) ) ),
    inference(resolution,[status(thm)],[c_370,c_2])).

tff(c_470,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_464])).

tff(c_474,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_54,c_470])).

tff(c_384,plain,(
    ! [A_264,B_265,C_266] :
      ( k9_subset_1(A_264,B_265,C_266) = k3_xboole_0(B_265,C_266)
      | ~ m1_subset_1(C_266,k1_zfmisc_1(A_264)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_396,plain,(
    ! [B_265] : k9_subset_1('#skF_1',B_265,'#skF_4') = k3_xboole_0(B_265,'#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_384])).

tff(c_48,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_46,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_42,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_40,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_1083,plain,(
    ! [E_421,F_424,C_425,D_422,B_426,A_423] :
      ( v1_funct_1(k1_tmap_1(A_423,B_426,C_425,D_422,E_421,F_424))
      | ~ m1_subset_1(F_424,k1_zfmisc_1(k2_zfmisc_1(D_422,B_426)))
      | ~ v1_funct_2(F_424,D_422,B_426)
      | ~ v1_funct_1(F_424)
      | ~ m1_subset_1(E_421,k1_zfmisc_1(k2_zfmisc_1(C_425,B_426)))
      | ~ v1_funct_2(E_421,C_425,B_426)
      | ~ v1_funct_1(E_421)
      | ~ m1_subset_1(D_422,k1_zfmisc_1(A_423))
      | v1_xboole_0(D_422)
      | ~ m1_subset_1(C_425,k1_zfmisc_1(A_423))
      | v1_xboole_0(C_425)
      | v1_xboole_0(B_426)
      | v1_xboole_0(A_423) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_1087,plain,(
    ! [A_423,C_425,E_421] :
      ( v1_funct_1(k1_tmap_1(A_423,'#skF_2',C_425,'#skF_4',E_421,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_421,k1_zfmisc_1(k2_zfmisc_1(C_425,'#skF_2')))
      | ~ v1_funct_2(E_421,C_425,'#skF_2')
      | ~ v1_funct_1(E_421)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_423))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_425,k1_zfmisc_1(A_423))
      | v1_xboole_0(C_425)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_423) ) ),
    inference(resolution,[status(thm)],[c_38,c_1083])).

tff(c_1094,plain,(
    ! [A_423,C_425,E_421] :
      ( v1_funct_1(k1_tmap_1(A_423,'#skF_2',C_425,'#skF_4',E_421,'#skF_6'))
      | ~ m1_subset_1(E_421,k1_zfmisc_1(k2_zfmisc_1(C_425,'#skF_2')))
      | ~ v1_funct_2(E_421,C_425,'#skF_2')
      | ~ v1_funct_1(E_421)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_423))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_425,k1_zfmisc_1(A_423))
      | v1_xboole_0(C_425)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_423) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1087])).

tff(c_1125,plain,(
    ! [A_438,C_439,E_440] :
      ( v1_funct_1(k1_tmap_1(A_438,'#skF_2',C_439,'#skF_4',E_440,'#skF_6'))
      | ~ m1_subset_1(E_440,k1_zfmisc_1(k2_zfmisc_1(C_439,'#skF_2')))
      | ~ v1_funct_2(E_440,C_439,'#skF_2')
      | ~ v1_funct_1(E_440)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_438))
      | ~ m1_subset_1(C_439,k1_zfmisc_1(A_438))
      | v1_xboole_0(C_439)
      | v1_xboole_0(A_438) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_1094])).

tff(c_1127,plain,(
    ! [A_438] :
      ( v1_funct_1(k1_tmap_1(A_438,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_438))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_438))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_438) ) ),
    inference(resolution,[status(thm)],[c_44,c_1125])).

tff(c_1132,plain,(
    ! [A_438] :
      ( v1_funct_1(k1_tmap_1(A_438,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_438))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_438))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_438) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1127])).

tff(c_1145,plain,(
    ! [A_442] :
      ( v1_funct_1(k1_tmap_1(A_442,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_442))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_442))
      | v1_xboole_0(A_442) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1132])).

tff(c_1148,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_1145])).

tff(c_1151,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1148])).

tff(c_1152,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1151])).

tff(c_475,plain,(
    ! [A_279,B_280,C_281,D_282] :
      ( k2_partfun1(A_279,B_280,C_281,D_282) = k7_relat_1(C_281,D_282)
      | ~ m1_subset_1(C_281,k1_zfmisc_1(k2_zfmisc_1(A_279,B_280)))
      | ~ v1_funct_1(C_281) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_477,plain,(
    ! [D_282] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_282) = k7_relat_1('#skF_5',D_282)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_44,c_475])).

tff(c_482,plain,(
    ! [D_282] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_282) = k7_relat_1('#skF_5',D_282) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_477])).

tff(c_479,plain,(
    ! [D_282] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_282) = k7_relat_1('#skF_6',D_282)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_38,c_475])).

tff(c_485,plain,(
    ! [D_282] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_282) = k7_relat_1('#skF_6',D_282) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_479])).

tff(c_32,plain,(
    ! [F_153,E_152,D_151,B_149,A_148,C_150] :
      ( v1_funct_2(k1_tmap_1(A_148,B_149,C_150,D_151,E_152,F_153),k4_subset_1(A_148,C_150,D_151),B_149)
      | ~ m1_subset_1(F_153,k1_zfmisc_1(k2_zfmisc_1(D_151,B_149)))
      | ~ v1_funct_2(F_153,D_151,B_149)
      | ~ v1_funct_1(F_153)
      | ~ m1_subset_1(E_152,k1_zfmisc_1(k2_zfmisc_1(C_150,B_149)))
      | ~ v1_funct_2(E_152,C_150,B_149)
      | ~ v1_funct_1(E_152)
      | ~ m1_subset_1(D_151,k1_zfmisc_1(A_148))
      | v1_xboole_0(D_151)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(A_148))
      | v1_xboole_0(C_150)
      | v1_xboole_0(B_149)
      | v1_xboole_0(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_30,plain,(
    ! [F_153,E_152,D_151,B_149,A_148,C_150] :
      ( m1_subset_1(k1_tmap_1(A_148,B_149,C_150,D_151,E_152,F_153),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_148,C_150,D_151),B_149)))
      | ~ m1_subset_1(F_153,k1_zfmisc_1(k2_zfmisc_1(D_151,B_149)))
      | ~ v1_funct_2(F_153,D_151,B_149)
      | ~ v1_funct_1(F_153)
      | ~ m1_subset_1(E_152,k1_zfmisc_1(k2_zfmisc_1(C_150,B_149)))
      | ~ v1_funct_2(E_152,C_150,B_149)
      | ~ v1_funct_1(E_152)
      | ~ m1_subset_1(D_151,k1_zfmisc_1(A_148))
      | v1_xboole_0(D_151)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(A_148))
      | v1_xboole_0(C_150)
      | v1_xboole_0(B_149)
      | v1_xboole_0(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_1287,plain,(
    ! [F_475,A_470,C_471,B_472,E_474,D_473] :
      ( k2_partfun1(k4_subset_1(A_470,C_471,D_473),B_472,k1_tmap_1(A_470,B_472,C_471,D_473,E_474,F_475),C_471) = E_474
      | ~ m1_subset_1(k1_tmap_1(A_470,B_472,C_471,D_473,E_474,F_475),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_470,C_471,D_473),B_472)))
      | ~ v1_funct_2(k1_tmap_1(A_470,B_472,C_471,D_473,E_474,F_475),k4_subset_1(A_470,C_471,D_473),B_472)
      | ~ v1_funct_1(k1_tmap_1(A_470,B_472,C_471,D_473,E_474,F_475))
      | k2_partfun1(D_473,B_472,F_475,k9_subset_1(A_470,C_471,D_473)) != k2_partfun1(C_471,B_472,E_474,k9_subset_1(A_470,C_471,D_473))
      | ~ m1_subset_1(F_475,k1_zfmisc_1(k2_zfmisc_1(D_473,B_472)))
      | ~ v1_funct_2(F_475,D_473,B_472)
      | ~ v1_funct_1(F_475)
      | ~ m1_subset_1(E_474,k1_zfmisc_1(k2_zfmisc_1(C_471,B_472)))
      | ~ v1_funct_2(E_474,C_471,B_472)
      | ~ v1_funct_1(E_474)
      | ~ m1_subset_1(D_473,k1_zfmisc_1(A_470))
      | v1_xboole_0(D_473)
      | ~ m1_subset_1(C_471,k1_zfmisc_1(A_470))
      | v1_xboole_0(C_471)
      | v1_xboole_0(B_472)
      | v1_xboole_0(A_470) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1457,plain,(
    ! [F_527,D_525,A_526,B_529,C_528,E_524] :
      ( k2_partfun1(k4_subset_1(A_526,C_528,D_525),B_529,k1_tmap_1(A_526,B_529,C_528,D_525,E_524,F_527),C_528) = E_524
      | ~ v1_funct_2(k1_tmap_1(A_526,B_529,C_528,D_525,E_524,F_527),k4_subset_1(A_526,C_528,D_525),B_529)
      | ~ v1_funct_1(k1_tmap_1(A_526,B_529,C_528,D_525,E_524,F_527))
      | k2_partfun1(D_525,B_529,F_527,k9_subset_1(A_526,C_528,D_525)) != k2_partfun1(C_528,B_529,E_524,k9_subset_1(A_526,C_528,D_525))
      | ~ m1_subset_1(F_527,k1_zfmisc_1(k2_zfmisc_1(D_525,B_529)))
      | ~ v1_funct_2(F_527,D_525,B_529)
      | ~ v1_funct_1(F_527)
      | ~ m1_subset_1(E_524,k1_zfmisc_1(k2_zfmisc_1(C_528,B_529)))
      | ~ v1_funct_2(E_524,C_528,B_529)
      | ~ v1_funct_1(E_524)
      | ~ m1_subset_1(D_525,k1_zfmisc_1(A_526))
      | v1_xboole_0(D_525)
      | ~ m1_subset_1(C_528,k1_zfmisc_1(A_526))
      | v1_xboole_0(C_528)
      | v1_xboole_0(B_529)
      | v1_xboole_0(A_526) ) ),
    inference(resolution,[status(thm)],[c_30,c_1287])).

tff(c_1461,plain,(
    ! [A_532,F_533,E_530,B_535,C_534,D_531] :
      ( k2_partfun1(k4_subset_1(A_532,C_534,D_531),B_535,k1_tmap_1(A_532,B_535,C_534,D_531,E_530,F_533),C_534) = E_530
      | ~ v1_funct_1(k1_tmap_1(A_532,B_535,C_534,D_531,E_530,F_533))
      | k2_partfun1(D_531,B_535,F_533,k9_subset_1(A_532,C_534,D_531)) != k2_partfun1(C_534,B_535,E_530,k9_subset_1(A_532,C_534,D_531))
      | ~ m1_subset_1(F_533,k1_zfmisc_1(k2_zfmisc_1(D_531,B_535)))
      | ~ v1_funct_2(F_533,D_531,B_535)
      | ~ v1_funct_1(F_533)
      | ~ m1_subset_1(E_530,k1_zfmisc_1(k2_zfmisc_1(C_534,B_535)))
      | ~ v1_funct_2(E_530,C_534,B_535)
      | ~ v1_funct_1(E_530)
      | ~ m1_subset_1(D_531,k1_zfmisc_1(A_532))
      | v1_xboole_0(D_531)
      | ~ m1_subset_1(C_534,k1_zfmisc_1(A_532))
      | v1_xboole_0(C_534)
      | v1_xboole_0(B_535)
      | v1_xboole_0(A_532) ) ),
    inference(resolution,[status(thm)],[c_32,c_1457])).

tff(c_1467,plain,(
    ! [A_532,C_534,E_530] :
      ( k2_partfun1(k4_subset_1(A_532,C_534,'#skF_4'),'#skF_2',k1_tmap_1(A_532,'#skF_2',C_534,'#skF_4',E_530,'#skF_6'),C_534) = E_530
      | ~ v1_funct_1(k1_tmap_1(A_532,'#skF_2',C_534,'#skF_4',E_530,'#skF_6'))
      | k2_partfun1(C_534,'#skF_2',E_530,k9_subset_1(A_532,C_534,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_532,C_534,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_530,k1_zfmisc_1(k2_zfmisc_1(C_534,'#skF_2')))
      | ~ v1_funct_2(E_530,C_534,'#skF_2')
      | ~ v1_funct_1(E_530)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_532))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_534,k1_zfmisc_1(A_532))
      | v1_xboole_0(C_534)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_532) ) ),
    inference(resolution,[status(thm)],[c_38,c_1461])).

tff(c_1475,plain,(
    ! [A_532,C_534,E_530] :
      ( k2_partfun1(k4_subset_1(A_532,C_534,'#skF_4'),'#skF_2',k1_tmap_1(A_532,'#skF_2',C_534,'#skF_4',E_530,'#skF_6'),C_534) = E_530
      | ~ v1_funct_1(k1_tmap_1(A_532,'#skF_2',C_534,'#skF_4',E_530,'#skF_6'))
      | k2_partfun1(C_534,'#skF_2',E_530,k9_subset_1(A_532,C_534,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_532,C_534,'#skF_4'))
      | ~ m1_subset_1(E_530,k1_zfmisc_1(k2_zfmisc_1(C_534,'#skF_2')))
      | ~ v1_funct_2(E_530,C_534,'#skF_2')
      | ~ v1_funct_1(E_530)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_532))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_534,k1_zfmisc_1(A_532))
      | v1_xboole_0(C_534)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_532) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_485,c_1467])).

tff(c_1558,plain,(
    ! [A_558,C_559,E_560] :
      ( k2_partfun1(k4_subset_1(A_558,C_559,'#skF_4'),'#skF_2',k1_tmap_1(A_558,'#skF_2',C_559,'#skF_4',E_560,'#skF_6'),C_559) = E_560
      | ~ v1_funct_1(k1_tmap_1(A_558,'#skF_2',C_559,'#skF_4',E_560,'#skF_6'))
      | k2_partfun1(C_559,'#skF_2',E_560,k9_subset_1(A_558,C_559,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_558,C_559,'#skF_4'))
      | ~ m1_subset_1(E_560,k1_zfmisc_1(k2_zfmisc_1(C_559,'#skF_2')))
      | ~ v1_funct_2(E_560,C_559,'#skF_2')
      | ~ v1_funct_1(E_560)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_558))
      | ~ m1_subset_1(C_559,k1_zfmisc_1(A_558))
      | v1_xboole_0(C_559)
      | v1_xboole_0(A_558) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_1475])).

tff(c_1563,plain,(
    ! [A_558] :
      ( k2_partfun1(k4_subset_1(A_558,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_558,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_558,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_558,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_558,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_558))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_558))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_558) ) ),
    inference(resolution,[status(thm)],[c_44,c_1558])).

tff(c_1571,plain,(
    ! [A_558] :
      ( k2_partfun1(k4_subset_1(A_558,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_558,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_558,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_558,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_558,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_558))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_558))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_558) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_482,c_1563])).

tff(c_1599,plain,(
    ! [A_562] :
      ( k2_partfun1(k4_subset_1(A_562,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_562,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_562,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_562,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_562,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_562))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_562))
      | v1_xboole_0(A_562) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1571])).

tff(c_525,plain,(
    ! [C_293,A_291,E_289,F_292,D_290,B_294] :
      ( v1_funct_1(k1_tmap_1(A_291,B_294,C_293,D_290,E_289,F_292))
      | ~ m1_subset_1(F_292,k1_zfmisc_1(k2_zfmisc_1(D_290,B_294)))
      | ~ v1_funct_2(F_292,D_290,B_294)
      | ~ v1_funct_1(F_292)
      | ~ m1_subset_1(E_289,k1_zfmisc_1(k2_zfmisc_1(C_293,B_294)))
      | ~ v1_funct_2(E_289,C_293,B_294)
      | ~ v1_funct_1(E_289)
      | ~ m1_subset_1(D_290,k1_zfmisc_1(A_291))
      | v1_xboole_0(D_290)
      | ~ m1_subset_1(C_293,k1_zfmisc_1(A_291))
      | v1_xboole_0(C_293)
      | v1_xboole_0(B_294)
      | v1_xboole_0(A_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_529,plain,(
    ! [A_291,C_293,E_289] :
      ( v1_funct_1(k1_tmap_1(A_291,'#skF_2',C_293,'#skF_4',E_289,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_289,k1_zfmisc_1(k2_zfmisc_1(C_293,'#skF_2')))
      | ~ v1_funct_2(E_289,C_293,'#skF_2')
      | ~ v1_funct_1(E_289)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_291))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_293,k1_zfmisc_1(A_291))
      | v1_xboole_0(C_293)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_291) ) ),
    inference(resolution,[status(thm)],[c_38,c_525])).

tff(c_536,plain,(
    ! [A_291,C_293,E_289] :
      ( v1_funct_1(k1_tmap_1(A_291,'#skF_2',C_293,'#skF_4',E_289,'#skF_6'))
      | ~ m1_subset_1(E_289,k1_zfmisc_1(k2_zfmisc_1(C_293,'#skF_2')))
      | ~ v1_funct_2(E_289,C_293,'#skF_2')
      | ~ v1_funct_1(E_289)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_291))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_293,k1_zfmisc_1(A_291))
      | v1_xboole_0(C_293)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_291) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_529])).

tff(c_567,plain,(
    ! [A_306,C_307,E_308] :
      ( v1_funct_1(k1_tmap_1(A_306,'#skF_2',C_307,'#skF_4',E_308,'#skF_6'))
      | ~ m1_subset_1(E_308,k1_zfmisc_1(k2_zfmisc_1(C_307,'#skF_2')))
      | ~ v1_funct_2(E_308,C_307,'#skF_2')
      | ~ v1_funct_1(E_308)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_306))
      | ~ m1_subset_1(C_307,k1_zfmisc_1(A_306))
      | v1_xboole_0(C_307)
      | v1_xboole_0(A_306) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_536])).

tff(c_569,plain,(
    ! [A_306] :
      ( v1_funct_1(k1_tmap_1(A_306,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_306))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_306))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_306) ) ),
    inference(resolution,[status(thm)],[c_44,c_567])).

tff(c_574,plain,(
    ! [A_306] :
      ( v1_funct_1(k1_tmap_1(A_306,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_306))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_306))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_306) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_569])).

tff(c_587,plain,(
    ! [A_310] :
      ( v1_funct_1(k1_tmap_1(A_310,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_310))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_310))
      | v1_xboole_0(A_310) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_574])).

tff(c_590,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_587])).

tff(c_593,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_590])).

tff(c_594,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_593])).

tff(c_755,plain,(
    ! [E_356,C_353,A_352,D_355,B_354,F_357] :
      ( k2_partfun1(k4_subset_1(A_352,C_353,D_355),B_354,k1_tmap_1(A_352,B_354,C_353,D_355,E_356,F_357),D_355) = F_357
      | ~ m1_subset_1(k1_tmap_1(A_352,B_354,C_353,D_355,E_356,F_357),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_352,C_353,D_355),B_354)))
      | ~ v1_funct_2(k1_tmap_1(A_352,B_354,C_353,D_355,E_356,F_357),k4_subset_1(A_352,C_353,D_355),B_354)
      | ~ v1_funct_1(k1_tmap_1(A_352,B_354,C_353,D_355,E_356,F_357))
      | k2_partfun1(D_355,B_354,F_357,k9_subset_1(A_352,C_353,D_355)) != k2_partfun1(C_353,B_354,E_356,k9_subset_1(A_352,C_353,D_355))
      | ~ m1_subset_1(F_357,k1_zfmisc_1(k2_zfmisc_1(D_355,B_354)))
      | ~ v1_funct_2(F_357,D_355,B_354)
      | ~ v1_funct_1(F_357)
      | ~ m1_subset_1(E_356,k1_zfmisc_1(k2_zfmisc_1(C_353,B_354)))
      | ~ v1_funct_2(E_356,C_353,B_354)
      | ~ v1_funct_1(E_356)
      | ~ m1_subset_1(D_355,k1_zfmisc_1(A_352))
      | v1_xboole_0(D_355)
      | ~ m1_subset_1(C_353,k1_zfmisc_1(A_352))
      | v1_xboole_0(C_353)
      | v1_xboole_0(B_354)
      | v1_xboole_0(A_352) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_855,plain,(
    ! [E_381,B_386,A_383,F_384,D_382,C_385] :
      ( k2_partfun1(k4_subset_1(A_383,C_385,D_382),B_386,k1_tmap_1(A_383,B_386,C_385,D_382,E_381,F_384),D_382) = F_384
      | ~ v1_funct_2(k1_tmap_1(A_383,B_386,C_385,D_382,E_381,F_384),k4_subset_1(A_383,C_385,D_382),B_386)
      | ~ v1_funct_1(k1_tmap_1(A_383,B_386,C_385,D_382,E_381,F_384))
      | k2_partfun1(D_382,B_386,F_384,k9_subset_1(A_383,C_385,D_382)) != k2_partfun1(C_385,B_386,E_381,k9_subset_1(A_383,C_385,D_382))
      | ~ m1_subset_1(F_384,k1_zfmisc_1(k2_zfmisc_1(D_382,B_386)))
      | ~ v1_funct_2(F_384,D_382,B_386)
      | ~ v1_funct_1(F_384)
      | ~ m1_subset_1(E_381,k1_zfmisc_1(k2_zfmisc_1(C_385,B_386)))
      | ~ v1_funct_2(E_381,C_385,B_386)
      | ~ v1_funct_1(E_381)
      | ~ m1_subset_1(D_382,k1_zfmisc_1(A_383))
      | v1_xboole_0(D_382)
      | ~ m1_subset_1(C_385,k1_zfmisc_1(A_383))
      | v1_xboole_0(C_385)
      | v1_xboole_0(B_386)
      | v1_xboole_0(A_383) ) ),
    inference(resolution,[status(thm)],[c_30,c_755])).

tff(c_880,plain,(
    ! [B_397,A_394,C_396,E_392,F_395,D_393] :
      ( k2_partfun1(k4_subset_1(A_394,C_396,D_393),B_397,k1_tmap_1(A_394,B_397,C_396,D_393,E_392,F_395),D_393) = F_395
      | ~ v1_funct_1(k1_tmap_1(A_394,B_397,C_396,D_393,E_392,F_395))
      | k2_partfun1(D_393,B_397,F_395,k9_subset_1(A_394,C_396,D_393)) != k2_partfun1(C_396,B_397,E_392,k9_subset_1(A_394,C_396,D_393))
      | ~ m1_subset_1(F_395,k1_zfmisc_1(k2_zfmisc_1(D_393,B_397)))
      | ~ v1_funct_2(F_395,D_393,B_397)
      | ~ v1_funct_1(F_395)
      | ~ m1_subset_1(E_392,k1_zfmisc_1(k2_zfmisc_1(C_396,B_397)))
      | ~ v1_funct_2(E_392,C_396,B_397)
      | ~ v1_funct_1(E_392)
      | ~ m1_subset_1(D_393,k1_zfmisc_1(A_394))
      | v1_xboole_0(D_393)
      | ~ m1_subset_1(C_396,k1_zfmisc_1(A_394))
      | v1_xboole_0(C_396)
      | v1_xboole_0(B_397)
      | v1_xboole_0(A_394) ) ),
    inference(resolution,[status(thm)],[c_32,c_855])).

tff(c_886,plain,(
    ! [A_394,C_396,E_392] :
      ( k2_partfun1(k4_subset_1(A_394,C_396,'#skF_4'),'#skF_2',k1_tmap_1(A_394,'#skF_2',C_396,'#skF_4',E_392,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_394,'#skF_2',C_396,'#skF_4',E_392,'#skF_6'))
      | k2_partfun1(C_396,'#skF_2',E_392,k9_subset_1(A_394,C_396,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_394,C_396,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_392,k1_zfmisc_1(k2_zfmisc_1(C_396,'#skF_2')))
      | ~ v1_funct_2(E_392,C_396,'#skF_2')
      | ~ v1_funct_1(E_392)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_394))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_396,k1_zfmisc_1(A_394))
      | v1_xboole_0(C_396)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_394) ) ),
    inference(resolution,[status(thm)],[c_38,c_880])).

tff(c_894,plain,(
    ! [A_394,C_396,E_392] :
      ( k2_partfun1(k4_subset_1(A_394,C_396,'#skF_4'),'#skF_2',k1_tmap_1(A_394,'#skF_2',C_396,'#skF_4',E_392,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_394,'#skF_2',C_396,'#skF_4',E_392,'#skF_6'))
      | k2_partfun1(C_396,'#skF_2',E_392,k9_subset_1(A_394,C_396,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_394,C_396,'#skF_4'))
      | ~ m1_subset_1(E_392,k1_zfmisc_1(k2_zfmisc_1(C_396,'#skF_2')))
      | ~ v1_funct_2(E_392,C_396,'#skF_2')
      | ~ v1_funct_1(E_392)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_394))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_396,k1_zfmisc_1(A_394))
      | v1_xboole_0(C_396)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_394) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_485,c_886])).

tff(c_981,plain,(
    ! [A_411,C_412,E_413] :
      ( k2_partfun1(k4_subset_1(A_411,C_412,'#skF_4'),'#skF_2',k1_tmap_1(A_411,'#skF_2',C_412,'#skF_4',E_413,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_411,'#skF_2',C_412,'#skF_4',E_413,'#skF_6'))
      | k2_partfun1(C_412,'#skF_2',E_413,k9_subset_1(A_411,C_412,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_411,C_412,'#skF_4'))
      | ~ m1_subset_1(E_413,k1_zfmisc_1(k2_zfmisc_1(C_412,'#skF_2')))
      | ~ v1_funct_2(E_413,C_412,'#skF_2')
      | ~ v1_funct_1(E_413)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_411))
      | ~ m1_subset_1(C_412,k1_zfmisc_1(A_411))
      | v1_xboole_0(C_412)
      | v1_xboole_0(A_411) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_894])).

tff(c_986,plain,(
    ! [A_411] :
      ( k2_partfun1(k4_subset_1(A_411,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_411,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_411,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_411,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_411,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_411))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_411))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_411) ) ),
    inference(resolution,[status(thm)],[c_44,c_981])).

tff(c_994,plain,(
    ! [A_411] :
      ( k2_partfun1(k4_subset_1(A_411,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_411,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_411,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_411,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_411,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_411))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_411))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_411) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_482,c_986])).

tff(c_1033,plain,(
    ! [A_416] :
      ( k2_partfun1(k4_subset_1(A_416,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_416,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_416,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_416,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_416,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_416))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_416))
      | v1_xboole_0(A_416) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_994])).

tff(c_103,plain,(
    ! [C_219,A_220,B_221] :
      ( v1_relat_1(C_219)
      | ~ m1_subset_1(C_219,k1_zfmisc_1(k2_zfmisc_1(A_220,B_221))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_111,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_103])).

tff(c_117,plain,(
    ! [B_224,A_225] :
      ( k7_relat_1(B_224,A_225) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_224),A_225)
      | ~ v1_relat_1(B_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_132,plain,(
    ! [B_226] :
      ( k7_relat_1(B_226,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_226) ) ),
    inference(resolution,[status(thm)],[c_6,c_117])).

tff(c_139,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_111,c_132])).

tff(c_262,plain,(
    ! [A_244,B_245,C_246,D_247] :
      ( k2_partfun1(A_244,B_245,C_246,D_247) = k7_relat_1(C_246,D_247)
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(A_244,B_245)))
      | ~ v1_funct_1(C_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_266,plain,(
    ! [D_247] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_247) = k7_relat_1('#skF_6',D_247)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_38,c_262])).

tff(c_272,plain,(
    ! [D_247] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_247) = k7_relat_1('#skF_6',D_247) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_266])).

tff(c_110,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_103])).

tff(c_140,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_110,c_132])).

tff(c_264,plain,(
    ! [D_247] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_247) = k7_relat_1('#skF_5',D_247)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_44,c_262])).

tff(c_269,plain,(
    ! [D_247] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_247) = k7_relat_1('#skF_5',D_247) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_264])).

tff(c_163,plain,(
    ! [A_229,B_230] :
      ( r1_xboole_0(A_229,B_230)
      | ~ r1_subset_1(A_229,B_230)
      | v1_xboole_0(B_230)
      | v1_xboole_0(A_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_228,plain,(
    ! [A_240,B_241] :
      ( k3_xboole_0(A_240,B_241) = k1_xboole_0
      | ~ r1_subset_1(A_240,B_241)
      | v1_xboole_0(B_241)
      | v1_xboole_0(A_240) ) ),
    inference(resolution,[status(thm)],[c_163,c_2])).

tff(c_234,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_228])).

tff(c_238,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_54,c_234])).

tff(c_177,plain,(
    ! [A_231,B_232,C_233] :
      ( k9_subset_1(A_231,B_232,C_233) = k3_xboole_0(B_232,C_233)
      | ~ m1_subset_1(C_233,k1_zfmisc_1(A_231)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_189,plain,(
    ! [B_232] : k9_subset_1('#skF_1',B_232,'#skF_4') = k3_xboole_0(B_232,'#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_177])).

tff(c_36,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_101,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_199,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_189,c_101])).

tff(c_302,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_272,c_140,c_269,c_238,c_238,c_199])).

tff(c_303,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_508,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_303])).

tff(c_1044,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1033,c_508])).

tff(c_1058,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_333,c_474,c_334,c_474,c_396,c_396,c_594,c_1044])).

tff(c_1060,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1058])).

tff(c_1061,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_303])).

tff(c_1608,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1599,c_1061])).

tff(c_1619,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_333,c_334,c_474,c_396,c_474,c_396,c_1152,c_1608])).

tff(c_1621,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1619])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:29:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.24/1.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.41/1.98  
% 5.41/1.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.41/1.98  %$ v1_funct_2 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.41/1.98  
% 5.41/1.98  %Foreground sorts:
% 5.41/1.98  
% 5.41/1.98  
% 5.41/1.98  %Background operators:
% 5.41/1.98  
% 5.41/1.98  
% 5.41/1.98  %Foreground operators:
% 5.41/1.98  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 5.41/1.98  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.41/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.41/1.98  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.41/1.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.41/1.98  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.41/1.98  tff('#skF_5', type, '#skF_5': $i).
% 5.41/1.98  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.41/1.98  tff('#skF_6', type, '#skF_6': $i).
% 5.41/1.98  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.41/1.98  tff('#skF_2', type, '#skF_2': $i).
% 5.41/1.98  tff('#skF_3', type, '#skF_3': $i).
% 5.41/1.98  tff('#skF_1', type, '#skF_1': $i).
% 5.41/1.98  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.41/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.41/1.98  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.41/1.98  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.41/1.98  tff('#skF_4', type, '#skF_4': $i).
% 5.41/1.98  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.41/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.41/1.98  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 5.41/1.98  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.41/1.98  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.41/1.98  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.41/1.98  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 5.41/1.98  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.41/1.98  
% 5.41/2.01  tff(f_192, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 5.41/2.01  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.41/2.01  tff(f_31, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.41/2.01  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 5.41/2.01  tff(f_58, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 5.41/2.01  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.41/2.01  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 5.41/2.01  tff(f_150, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 5.41/2.01  tff(f_68, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 5.41/2.01  tff(f_116, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 5.41/2.01  tff(c_62, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_192])).
% 5.41/2.01  tff(c_56, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_192])).
% 5.41/2.01  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_192])).
% 5.41/2.01  tff(c_38, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_192])).
% 5.41/2.01  tff(c_306, plain, (![C_252, A_253, B_254]: (v1_relat_1(C_252) | ~m1_subset_1(C_252, k1_zfmisc_1(k2_zfmisc_1(A_253, B_254))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.41/2.01  tff(c_314, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_38, c_306])).
% 5.41/2.01  tff(c_6, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.41/2.01  tff(c_315, plain, (![B_255, A_256]: (k7_relat_1(B_255, A_256)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_255), A_256) | ~v1_relat_1(B_255))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.41/2.01  tff(c_326, plain, (![B_257]: (k7_relat_1(B_257, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_257))), inference(resolution, [status(thm)], [c_6, c_315])).
% 5.41/2.01  tff(c_333, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_314, c_326])).
% 5.41/2.01  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_192])).
% 5.41/2.01  tff(c_313, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_306])).
% 5.41/2.01  tff(c_334, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_313, c_326])).
% 5.41/2.01  tff(c_58, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_192])).
% 5.41/2.01  tff(c_54, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_192])).
% 5.41/2.01  tff(c_50, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_192])).
% 5.41/2.01  tff(c_370, plain, (![A_262, B_263]: (r1_xboole_0(A_262, B_263) | ~r1_subset_1(A_262, B_263) | v1_xboole_0(B_263) | v1_xboole_0(A_262))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.41/2.01  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.41/2.01  tff(c_464, plain, (![A_277, B_278]: (k3_xboole_0(A_277, B_278)=k1_xboole_0 | ~r1_subset_1(A_277, B_278) | v1_xboole_0(B_278) | v1_xboole_0(A_277))), inference(resolution, [status(thm)], [c_370, c_2])).
% 5.41/2.01  tff(c_470, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_464])).
% 5.41/2.01  tff(c_474, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_58, c_54, c_470])).
% 5.41/2.01  tff(c_384, plain, (![A_264, B_265, C_266]: (k9_subset_1(A_264, B_265, C_266)=k3_xboole_0(B_265, C_266) | ~m1_subset_1(C_266, k1_zfmisc_1(A_264)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.41/2.01  tff(c_396, plain, (![B_265]: (k9_subset_1('#skF_1', B_265, '#skF_4')=k3_xboole_0(B_265, '#skF_4'))), inference(resolution, [status(thm)], [c_52, c_384])).
% 5.41/2.01  tff(c_48, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_192])).
% 5.41/2.01  tff(c_46, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 5.41/2.01  tff(c_60, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 5.41/2.01  tff(c_42, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_192])).
% 5.41/2.01  tff(c_40, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 5.41/2.01  tff(c_1083, plain, (![E_421, F_424, C_425, D_422, B_426, A_423]: (v1_funct_1(k1_tmap_1(A_423, B_426, C_425, D_422, E_421, F_424)) | ~m1_subset_1(F_424, k1_zfmisc_1(k2_zfmisc_1(D_422, B_426))) | ~v1_funct_2(F_424, D_422, B_426) | ~v1_funct_1(F_424) | ~m1_subset_1(E_421, k1_zfmisc_1(k2_zfmisc_1(C_425, B_426))) | ~v1_funct_2(E_421, C_425, B_426) | ~v1_funct_1(E_421) | ~m1_subset_1(D_422, k1_zfmisc_1(A_423)) | v1_xboole_0(D_422) | ~m1_subset_1(C_425, k1_zfmisc_1(A_423)) | v1_xboole_0(C_425) | v1_xboole_0(B_426) | v1_xboole_0(A_423))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.41/2.01  tff(c_1087, plain, (![A_423, C_425, E_421]: (v1_funct_1(k1_tmap_1(A_423, '#skF_2', C_425, '#skF_4', E_421, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_421, k1_zfmisc_1(k2_zfmisc_1(C_425, '#skF_2'))) | ~v1_funct_2(E_421, C_425, '#skF_2') | ~v1_funct_1(E_421) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_423)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_425, k1_zfmisc_1(A_423)) | v1_xboole_0(C_425) | v1_xboole_0('#skF_2') | v1_xboole_0(A_423))), inference(resolution, [status(thm)], [c_38, c_1083])).
% 5.41/2.01  tff(c_1094, plain, (![A_423, C_425, E_421]: (v1_funct_1(k1_tmap_1(A_423, '#skF_2', C_425, '#skF_4', E_421, '#skF_6')) | ~m1_subset_1(E_421, k1_zfmisc_1(k2_zfmisc_1(C_425, '#skF_2'))) | ~v1_funct_2(E_421, C_425, '#skF_2') | ~v1_funct_1(E_421) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_423)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_425, k1_zfmisc_1(A_423)) | v1_xboole_0(C_425) | v1_xboole_0('#skF_2') | v1_xboole_0(A_423))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_1087])).
% 5.41/2.01  tff(c_1125, plain, (![A_438, C_439, E_440]: (v1_funct_1(k1_tmap_1(A_438, '#skF_2', C_439, '#skF_4', E_440, '#skF_6')) | ~m1_subset_1(E_440, k1_zfmisc_1(k2_zfmisc_1(C_439, '#skF_2'))) | ~v1_funct_2(E_440, C_439, '#skF_2') | ~v1_funct_1(E_440) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_438)) | ~m1_subset_1(C_439, k1_zfmisc_1(A_438)) | v1_xboole_0(C_439) | v1_xboole_0(A_438))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_1094])).
% 5.41/2.01  tff(c_1127, plain, (![A_438]: (v1_funct_1(k1_tmap_1(A_438, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_438)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_438)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_438))), inference(resolution, [status(thm)], [c_44, c_1125])).
% 5.41/2.01  tff(c_1132, plain, (![A_438]: (v1_funct_1(k1_tmap_1(A_438, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_438)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_438)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_438))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1127])).
% 5.41/2.01  tff(c_1145, plain, (![A_442]: (v1_funct_1(k1_tmap_1(A_442, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_442)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_442)) | v1_xboole_0(A_442))), inference(negUnitSimplification, [status(thm)], [c_58, c_1132])).
% 5.41/2.01  tff(c_1148, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_56, c_1145])).
% 5.41/2.01  tff(c_1151, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1148])).
% 5.41/2.01  tff(c_1152, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_62, c_1151])).
% 5.41/2.01  tff(c_475, plain, (![A_279, B_280, C_281, D_282]: (k2_partfun1(A_279, B_280, C_281, D_282)=k7_relat_1(C_281, D_282) | ~m1_subset_1(C_281, k1_zfmisc_1(k2_zfmisc_1(A_279, B_280))) | ~v1_funct_1(C_281))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.41/2.01  tff(c_477, plain, (![D_282]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_282)=k7_relat_1('#skF_5', D_282) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_44, c_475])).
% 5.41/2.01  tff(c_482, plain, (![D_282]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_282)=k7_relat_1('#skF_5', D_282))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_477])).
% 5.41/2.01  tff(c_479, plain, (![D_282]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_282)=k7_relat_1('#skF_6', D_282) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_38, c_475])).
% 5.41/2.01  tff(c_485, plain, (![D_282]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_282)=k7_relat_1('#skF_6', D_282))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_479])).
% 5.41/2.01  tff(c_32, plain, (![F_153, E_152, D_151, B_149, A_148, C_150]: (v1_funct_2(k1_tmap_1(A_148, B_149, C_150, D_151, E_152, F_153), k4_subset_1(A_148, C_150, D_151), B_149) | ~m1_subset_1(F_153, k1_zfmisc_1(k2_zfmisc_1(D_151, B_149))) | ~v1_funct_2(F_153, D_151, B_149) | ~v1_funct_1(F_153) | ~m1_subset_1(E_152, k1_zfmisc_1(k2_zfmisc_1(C_150, B_149))) | ~v1_funct_2(E_152, C_150, B_149) | ~v1_funct_1(E_152) | ~m1_subset_1(D_151, k1_zfmisc_1(A_148)) | v1_xboole_0(D_151) | ~m1_subset_1(C_150, k1_zfmisc_1(A_148)) | v1_xboole_0(C_150) | v1_xboole_0(B_149) | v1_xboole_0(A_148))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.41/2.01  tff(c_30, plain, (![F_153, E_152, D_151, B_149, A_148, C_150]: (m1_subset_1(k1_tmap_1(A_148, B_149, C_150, D_151, E_152, F_153), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_148, C_150, D_151), B_149))) | ~m1_subset_1(F_153, k1_zfmisc_1(k2_zfmisc_1(D_151, B_149))) | ~v1_funct_2(F_153, D_151, B_149) | ~v1_funct_1(F_153) | ~m1_subset_1(E_152, k1_zfmisc_1(k2_zfmisc_1(C_150, B_149))) | ~v1_funct_2(E_152, C_150, B_149) | ~v1_funct_1(E_152) | ~m1_subset_1(D_151, k1_zfmisc_1(A_148)) | v1_xboole_0(D_151) | ~m1_subset_1(C_150, k1_zfmisc_1(A_148)) | v1_xboole_0(C_150) | v1_xboole_0(B_149) | v1_xboole_0(A_148))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.41/2.01  tff(c_1287, plain, (![F_475, A_470, C_471, B_472, E_474, D_473]: (k2_partfun1(k4_subset_1(A_470, C_471, D_473), B_472, k1_tmap_1(A_470, B_472, C_471, D_473, E_474, F_475), C_471)=E_474 | ~m1_subset_1(k1_tmap_1(A_470, B_472, C_471, D_473, E_474, F_475), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_470, C_471, D_473), B_472))) | ~v1_funct_2(k1_tmap_1(A_470, B_472, C_471, D_473, E_474, F_475), k4_subset_1(A_470, C_471, D_473), B_472) | ~v1_funct_1(k1_tmap_1(A_470, B_472, C_471, D_473, E_474, F_475)) | k2_partfun1(D_473, B_472, F_475, k9_subset_1(A_470, C_471, D_473))!=k2_partfun1(C_471, B_472, E_474, k9_subset_1(A_470, C_471, D_473)) | ~m1_subset_1(F_475, k1_zfmisc_1(k2_zfmisc_1(D_473, B_472))) | ~v1_funct_2(F_475, D_473, B_472) | ~v1_funct_1(F_475) | ~m1_subset_1(E_474, k1_zfmisc_1(k2_zfmisc_1(C_471, B_472))) | ~v1_funct_2(E_474, C_471, B_472) | ~v1_funct_1(E_474) | ~m1_subset_1(D_473, k1_zfmisc_1(A_470)) | v1_xboole_0(D_473) | ~m1_subset_1(C_471, k1_zfmisc_1(A_470)) | v1_xboole_0(C_471) | v1_xboole_0(B_472) | v1_xboole_0(A_470))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.41/2.01  tff(c_1457, plain, (![F_527, D_525, A_526, B_529, C_528, E_524]: (k2_partfun1(k4_subset_1(A_526, C_528, D_525), B_529, k1_tmap_1(A_526, B_529, C_528, D_525, E_524, F_527), C_528)=E_524 | ~v1_funct_2(k1_tmap_1(A_526, B_529, C_528, D_525, E_524, F_527), k4_subset_1(A_526, C_528, D_525), B_529) | ~v1_funct_1(k1_tmap_1(A_526, B_529, C_528, D_525, E_524, F_527)) | k2_partfun1(D_525, B_529, F_527, k9_subset_1(A_526, C_528, D_525))!=k2_partfun1(C_528, B_529, E_524, k9_subset_1(A_526, C_528, D_525)) | ~m1_subset_1(F_527, k1_zfmisc_1(k2_zfmisc_1(D_525, B_529))) | ~v1_funct_2(F_527, D_525, B_529) | ~v1_funct_1(F_527) | ~m1_subset_1(E_524, k1_zfmisc_1(k2_zfmisc_1(C_528, B_529))) | ~v1_funct_2(E_524, C_528, B_529) | ~v1_funct_1(E_524) | ~m1_subset_1(D_525, k1_zfmisc_1(A_526)) | v1_xboole_0(D_525) | ~m1_subset_1(C_528, k1_zfmisc_1(A_526)) | v1_xboole_0(C_528) | v1_xboole_0(B_529) | v1_xboole_0(A_526))), inference(resolution, [status(thm)], [c_30, c_1287])).
% 5.41/2.01  tff(c_1461, plain, (![A_532, F_533, E_530, B_535, C_534, D_531]: (k2_partfun1(k4_subset_1(A_532, C_534, D_531), B_535, k1_tmap_1(A_532, B_535, C_534, D_531, E_530, F_533), C_534)=E_530 | ~v1_funct_1(k1_tmap_1(A_532, B_535, C_534, D_531, E_530, F_533)) | k2_partfun1(D_531, B_535, F_533, k9_subset_1(A_532, C_534, D_531))!=k2_partfun1(C_534, B_535, E_530, k9_subset_1(A_532, C_534, D_531)) | ~m1_subset_1(F_533, k1_zfmisc_1(k2_zfmisc_1(D_531, B_535))) | ~v1_funct_2(F_533, D_531, B_535) | ~v1_funct_1(F_533) | ~m1_subset_1(E_530, k1_zfmisc_1(k2_zfmisc_1(C_534, B_535))) | ~v1_funct_2(E_530, C_534, B_535) | ~v1_funct_1(E_530) | ~m1_subset_1(D_531, k1_zfmisc_1(A_532)) | v1_xboole_0(D_531) | ~m1_subset_1(C_534, k1_zfmisc_1(A_532)) | v1_xboole_0(C_534) | v1_xboole_0(B_535) | v1_xboole_0(A_532))), inference(resolution, [status(thm)], [c_32, c_1457])).
% 5.41/2.01  tff(c_1467, plain, (![A_532, C_534, E_530]: (k2_partfun1(k4_subset_1(A_532, C_534, '#skF_4'), '#skF_2', k1_tmap_1(A_532, '#skF_2', C_534, '#skF_4', E_530, '#skF_6'), C_534)=E_530 | ~v1_funct_1(k1_tmap_1(A_532, '#skF_2', C_534, '#skF_4', E_530, '#skF_6')) | k2_partfun1(C_534, '#skF_2', E_530, k9_subset_1(A_532, C_534, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_532, C_534, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_530, k1_zfmisc_1(k2_zfmisc_1(C_534, '#skF_2'))) | ~v1_funct_2(E_530, C_534, '#skF_2') | ~v1_funct_1(E_530) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_532)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_534, k1_zfmisc_1(A_532)) | v1_xboole_0(C_534) | v1_xboole_0('#skF_2') | v1_xboole_0(A_532))), inference(resolution, [status(thm)], [c_38, c_1461])).
% 5.41/2.01  tff(c_1475, plain, (![A_532, C_534, E_530]: (k2_partfun1(k4_subset_1(A_532, C_534, '#skF_4'), '#skF_2', k1_tmap_1(A_532, '#skF_2', C_534, '#skF_4', E_530, '#skF_6'), C_534)=E_530 | ~v1_funct_1(k1_tmap_1(A_532, '#skF_2', C_534, '#skF_4', E_530, '#skF_6')) | k2_partfun1(C_534, '#skF_2', E_530, k9_subset_1(A_532, C_534, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_532, C_534, '#skF_4')) | ~m1_subset_1(E_530, k1_zfmisc_1(k2_zfmisc_1(C_534, '#skF_2'))) | ~v1_funct_2(E_530, C_534, '#skF_2') | ~v1_funct_1(E_530) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_532)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_534, k1_zfmisc_1(A_532)) | v1_xboole_0(C_534) | v1_xboole_0('#skF_2') | v1_xboole_0(A_532))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_485, c_1467])).
% 5.41/2.01  tff(c_1558, plain, (![A_558, C_559, E_560]: (k2_partfun1(k4_subset_1(A_558, C_559, '#skF_4'), '#skF_2', k1_tmap_1(A_558, '#skF_2', C_559, '#skF_4', E_560, '#skF_6'), C_559)=E_560 | ~v1_funct_1(k1_tmap_1(A_558, '#skF_2', C_559, '#skF_4', E_560, '#skF_6')) | k2_partfun1(C_559, '#skF_2', E_560, k9_subset_1(A_558, C_559, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_558, C_559, '#skF_4')) | ~m1_subset_1(E_560, k1_zfmisc_1(k2_zfmisc_1(C_559, '#skF_2'))) | ~v1_funct_2(E_560, C_559, '#skF_2') | ~v1_funct_1(E_560) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_558)) | ~m1_subset_1(C_559, k1_zfmisc_1(A_558)) | v1_xboole_0(C_559) | v1_xboole_0(A_558))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_1475])).
% 5.41/2.01  tff(c_1563, plain, (![A_558]: (k2_partfun1(k4_subset_1(A_558, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_558, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_558, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_558, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_558, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_558)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_558)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_558))), inference(resolution, [status(thm)], [c_44, c_1558])).
% 5.41/2.01  tff(c_1571, plain, (![A_558]: (k2_partfun1(k4_subset_1(A_558, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_558, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_558, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_558, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_558, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_558)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_558)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_558))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_482, c_1563])).
% 5.41/2.01  tff(c_1599, plain, (![A_562]: (k2_partfun1(k4_subset_1(A_562, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_562, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_562, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_562, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_562, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_562)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_562)) | v1_xboole_0(A_562))), inference(negUnitSimplification, [status(thm)], [c_58, c_1571])).
% 5.41/2.01  tff(c_525, plain, (![C_293, A_291, E_289, F_292, D_290, B_294]: (v1_funct_1(k1_tmap_1(A_291, B_294, C_293, D_290, E_289, F_292)) | ~m1_subset_1(F_292, k1_zfmisc_1(k2_zfmisc_1(D_290, B_294))) | ~v1_funct_2(F_292, D_290, B_294) | ~v1_funct_1(F_292) | ~m1_subset_1(E_289, k1_zfmisc_1(k2_zfmisc_1(C_293, B_294))) | ~v1_funct_2(E_289, C_293, B_294) | ~v1_funct_1(E_289) | ~m1_subset_1(D_290, k1_zfmisc_1(A_291)) | v1_xboole_0(D_290) | ~m1_subset_1(C_293, k1_zfmisc_1(A_291)) | v1_xboole_0(C_293) | v1_xboole_0(B_294) | v1_xboole_0(A_291))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.41/2.01  tff(c_529, plain, (![A_291, C_293, E_289]: (v1_funct_1(k1_tmap_1(A_291, '#skF_2', C_293, '#skF_4', E_289, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_289, k1_zfmisc_1(k2_zfmisc_1(C_293, '#skF_2'))) | ~v1_funct_2(E_289, C_293, '#skF_2') | ~v1_funct_1(E_289) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_291)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_293, k1_zfmisc_1(A_291)) | v1_xboole_0(C_293) | v1_xboole_0('#skF_2') | v1_xboole_0(A_291))), inference(resolution, [status(thm)], [c_38, c_525])).
% 5.41/2.01  tff(c_536, plain, (![A_291, C_293, E_289]: (v1_funct_1(k1_tmap_1(A_291, '#skF_2', C_293, '#skF_4', E_289, '#skF_6')) | ~m1_subset_1(E_289, k1_zfmisc_1(k2_zfmisc_1(C_293, '#skF_2'))) | ~v1_funct_2(E_289, C_293, '#skF_2') | ~v1_funct_1(E_289) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_291)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_293, k1_zfmisc_1(A_291)) | v1_xboole_0(C_293) | v1_xboole_0('#skF_2') | v1_xboole_0(A_291))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_529])).
% 5.41/2.01  tff(c_567, plain, (![A_306, C_307, E_308]: (v1_funct_1(k1_tmap_1(A_306, '#skF_2', C_307, '#skF_4', E_308, '#skF_6')) | ~m1_subset_1(E_308, k1_zfmisc_1(k2_zfmisc_1(C_307, '#skF_2'))) | ~v1_funct_2(E_308, C_307, '#skF_2') | ~v1_funct_1(E_308) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_306)) | ~m1_subset_1(C_307, k1_zfmisc_1(A_306)) | v1_xboole_0(C_307) | v1_xboole_0(A_306))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_536])).
% 5.41/2.01  tff(c_569, plain, (![A_306]: (v1_funct_1(k1_tmap_1(A_306, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_306)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_306)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_306))), inference(resolution, [status(thm)], [c_44, c_567])).
% 5.41/2.01  tff(c_574, plain, (![A_306]: (v1_funct_1(k1_tmap_1(A_306, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_306)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_306)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_306))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_569])).
% 5.41/2.01  tff(c_587, plain, (![A_310]: (v1_funct_1(k1_tmap_1(A_310, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_310)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_310)) | v1_xboole_0(A_310))), inference(negUnitSimplification, [status(thm)], [c_58, c_574])).
% 5.41/2.01  tff(c_590, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_56, c_587])).
% 5.41/2.01  tff(c_593, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_590])).
% 5.41/2.01  tff(c_594, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_62, c_593])).
% 5.41/2.01  tff(c_755, plain, (![E_356, C_353, A_352, D_355, B_354, F_357]: (k2_partfun1(k4_subset_1(A_352, C_353, D_355), B_354, k1_tmap_1(A_352, B_354, C_353, D_355, E_356, F_357), D_355)=F_357 | ~m1_subset_1(k1_tmap_1(A_352, B_354, C_353, D_355, E_356, F_357), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_352, C_353, D_355), B_354))) | ~v1_funct_2(k1_tmap_1(A_352, B_354, C_353, D_355, E_356, F_357), k4_subset_1(A_352, C_353, D_355), B_354) | ~v1_funct_1(k1_tmap_1(A_352, B_354, C_353, D_355, E_356, F_357)) | k2_partfun1(D_355, B_354, F_357, k9_subset_1(A_352, C_353, D_355))!=k2_partfun1(C_353, B_354, E_356, k9_subset_1(A_352, C_353, D_355)) | ~m1_subset_1(F_357, k1_zfmisc_1(k2_zfmisc_1(D_355, B_354))) | ~v1_funct_2(F_357, D_355, B_354) | ~v1_funct_1(F_357) | ~m1_subset_1(E_356, k1_zfmisc_1(k2_zfmisc_1(C_353, B_354))) | ~v1_funct_2(E_356, C_353, B_354) | ~v1_funct_1(E_356) | ~m1_subset_1(D_355, k1_zfmisc_1(A_352)) | v1_xboole_0(D_355) | ~m1_subset_1(C_353, k1_zfmisc_1(A_352)) | v1_xboole_0(C_353) | v1_xboole_0(B_354) | v1_xboole_0(A_352))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.41/2.01  tff(c_855, plain, (![E_381, B_386, A_383, F_384, D_382, C_385]: (k2_partfun1(k4_subset_1(A_383, C_385, D_382), B_386, k1_tmap_1(A_383, B_386, C_385, D_382, E_381, F_384), D_382)=F_384 | ~v1_funct_2(k1_tmap_1(A_383, B_386, C_385, D_382, E_381, F_384), k4_subset_1(A_383, C_385, D_382), B_386) | ~v1_funct_1(k1_tmap_1(A_383, B_386, C_385, D_382, E_381, F_384)) | k2_partfun1(D_382, B_386, F_384, k9_subset_1(A_383, C_385, D_382))!=k2_partfun1(C_385, B_386, E_381, k9_subset_1(A_383, C_385, D_382)) | ~m1_subset_1(F_384, k1_zfmisc_1(k2_zfmisc_1(D_382, B_386))) | ~v1_funct_2(F_384, D_382, B_386) | ~v1_funct_1(F_384) | ~m1_subset_1(E_381, k1_zfmisc_1(k2_zfmisc_1(C_385, B_386))) | ~v1_funct_2(E_381, C_385, B_386) | ~v1_funct_1(E_381) | ~m1_subset_1(D_382, k1_zfmisc_1(A_383)) | v1_xboole_0(D_382) | ~m1_subset_1(C_385, k1_zfmisc_1(A_383)) | v1_xboole_0(C_385) | v1_xboole_0(B_386) | v1_xboole_0(A_383))), inference(resolution, [status(thm)], [c_30, c_755])).
% 5.41/2.01  tff(c_880, plain, (![B_397, A_394, C_396, E_392, F_395, D_393]: (k2_partfun1(k4_subset_1(A_394, C_396, D_393), B_397, k1_tmap_1(A_394, B_397, C_396, D_393, E_392, F_395), D_393)=F_395 | ~v1_funct_1(k1_tmap_1(A_394, B_397, C_396, D_393, E_392, F_395)) | k2_partfun1(D_393, B_397, F_395, k9_subset_1(A_394, C_396, D_393))!=k2_partfun1(C_396, B_397, E_392, k9_subset_1(A_394, C_396, D_393)) | ~m1_subset_1(F_395, k1_zfmisc_1(k2_zfmisc_1(D_393, B_397))) | ~v1_funct_2(F_395, D_393, B_397) | ~v1_funct_1(F_395) | ~m1_subset_1(E_392, k1_zfmisc_1(k2_zfmisc_1(C_396, B_397))) | ~v1_funct_2(E_392, C_396, B_397) | ~v1_funct_1(E_392) | ~m1_subset_1(D_393, k1_zfmisc_1(A_394)) | v1_xboole_0(D_393) | ~m1_subset_1(C_396, k1_zfmisc_1(A_394)) | v1_xboole_0(C_396) | v1_xboole_0(B_397) | v1_xboole_0(A_394))), inference(resolution, [status(thm)], [c_32, c_855])).
% 5.41/2.01  tff(c_886, plain, (![A_394, C_396, E_392]: (k2_partfun1(k4_subset_1(A_394, C_396, '#skF_4'), '#skF_2', k1_tmap_1(A_394, '#skF_2', C_396, '#skF_4', E_392, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_394, '#skF_2', C_396, '#skF_4', E_392, '#skF_6')) | k2_partfun1(C_396, '#skF_2', E_392, k9_subset_1(A_394, C_396, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_394, C_396, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_392, k1_zfmisc_1(k2_zfmisc_1(C_396, '#skF_2'))) | ~v1_funct_2(E_392, C_396, '#skF_2') | ~v1_funct_1(E_392) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_394)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_396, k1_zfmisc_1(A_394)) | v1_xboole_0(C_396) | v1_xboole_0('#skF_2') | v1_xboole_0(A_394))), inference(resolution, [status(thm)], [c_38, c_880])).
% 5.41/2.01  tff(c_894, plain, (![A_394, C_396, E_392]: (k2_partfun1(k4_subset_1(A_394, C_396, '#skF_4'), '#skF_2', k1_tmap_1(A_394, '#skF_2', C_396, '#skF_4', E_392, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_394, '#skF_2', C_396, '#skF_4', E_392, '#skF_6')) | k2_partfun1(C_396, '#skF_2', E_392, k9_subset_1(A_394, C_396, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_394, C_396, '#skF_4')) | ~m1_subset_1(E_392, k1_zfmisc_1(k2_zfmisc_1(C_396, '#skF_2'))) | ~v1_funct_2(E_392, C_396, '#skF_2') | ~v1_funct_1(E_392) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_394)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_396, k1_zfmisc_1(A_394)) | v1_xboole_0(C_396) | v1_xboole_0('#skF_2') | v1_xboole_0(A_394))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_485, c_886])).
% 5.41/2.01  tff(c_981, plain, (![A_411, C_412, E_413]: (k2_partfun1(k4_subset_1(A_411, C_412, '#skF_4'), '#skF_2', k1_tmap_1(A_411, '#skF_2', C_412, '#skF_4', E_413, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_411, '#skF_2', C_412, '#skF_4', E_413, '#skF_6')) | k2_partfun1(C_412, '#skF_2', E_413, k9_subset_1(A_411, C_412, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_411, C_412, '#skF_4')) | ~m1_subset_1(E_413, k1_zfmisc_1(k2_zfmisc_1(C_412, '#skF_2'))) | ~v1_funct_2(E_413, C_412, '#skF_2') | ~v1_funct_1(E_413) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_411)) | ~m1_subset_1(C_412, k1_zfmisc_1(A_411)) | v1_xboole_0(C_412) | v1_xboole_0(A_411))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_894])).
% 5.41/2.01  tff(c_986, plain, (![A_411]: (k2_partfun1(k4_subset_1(A_411, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_411, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_411, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_411, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_411, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_411)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_411)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_411))), inference(resolution, [status(thm)], [c_44, c_981])).
% 5.41/2.01  tff(c_994, plain, (![A_411]: (k2_partfun1(k4_subset_1(A_411, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_411, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_411, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_411, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_411, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_411)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_411)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_411))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_482, c_986])).
% 5.41/2.01  tff(c_1033, plain, (![A_416]: (k2_partfun1(k4_subset_1(A_416, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_416, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_416, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_416, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_416, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_416)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_416)) | v1_xboole_0(A_416))), inference(negUnitSimplification, [status(thm)], [c_58, c_994])).
% 5.41/2.01  tff(c_103, plain, (![C_219, A_220, B_221]: (v1_relat_1(C_219) | ~m1_subset_1(C_219, k1_zfmisc_1(k2_zfmisc_1(A_220, B_221))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.41/2.01  tff(c_111, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_38, c_103])).
% 5.41/2.01  tff(c_117, plain, (![B_224, A_225]: (k7_relat_1(B_224, A_225)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_224), A_225) | ~v1_relat_1(B_224))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.41/2.01  tff(c_132, plain, (![B_226]: (k7_relat_1(B_226, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_226))), inference(resolution, [status(thm)], [c_6, c_117])).
% 5.41/2.01  tff(c_139, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_111, c_132])).
% 5.41/2.01  tff(c_262, plain, (![A_244, B_245, C_246, D_247]: (k2_partfun1(A_244, B_245, C_246, D_247)=k7_relat_1(C_246, D_247) | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1(A_244, B_245))) | ~v1_funct_1(C_246))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.41/2.01  tff(c_266, plain, (![D_247]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_247)=k7_relat_1('#skF_6', D_247) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_38, c_262])).
% 5.41/2.01  tff(c_272, plain, (![D_247]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_247)=k7_relat_1('#skF_6', D_247))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_266])).
% 5.41/2.01  tff(c_110, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_103])).
% 5.41/2.01  tff(c_140, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_110, c_132])).
% 5.41/2.01  tff(c_264, plain, (![D_247]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_247)=k7_relat_1('#skF_5', D_247) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_44, c_262])).
% 5.41/2.01  tff(c_269, plain, (![D_247]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_247)=k7_relat_1('#skF_5', D_247))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_264])).
% 5.41/2.01  tff(c_163, plain, (![A_229, B_230]: (r1_xboole_0(A_229, B_230) | ~r1_subset_1(A_229, B_230) | v1_xboole_0(B_230) | v1_xboole_0(A_229))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.41/2.01  tff(c_228, plain, (![A_240, B_241]: (k3_xboole_0(A_240, B_241)=k1_xboole_0 | ~r1_subset_1(A_240, B_241) | v1_xboole_0(B_241) | v1_xboole_0(A_240))), inference(resolution, [status(thm)], [c_163, c_2])).
% 5.41/2.01  tff(c_234, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_228])).
% 5.41/2.01  tff(c_238, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_58, c_54, c_234])).
% 5.41/2.01  tff(c_177, plain, (![A_231, B_232, C_233]: (k9_subset_1(A_231, B_232, C_233)=k3_xboole_0(B_232, C_233) | ~m1_subset_1(C_233, k1_zfmisc_1(A_231)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.41/2.01  tff(c_189, plain, (![B_232]: (k9_subset_1('#skF_1', B_232, '#skF_4')=k3_xboole_0(B_232, '#skF_4'))), inference(resolution, [status(thm)], [c_52, c_177])).
% 5.41/2.01  tff(c_36, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_192])).
% 5.41/2.01  tff(c_101, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_36])).
% 5.41/2.01  tff(c_199, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_189, c_101])).
% 5.41/2.01  tff(c_302, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_272, c_140, c_269, c_238, c_238, c_199])).
% 5.41/2.01  tff(c_303, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_36])).
% 5.41/2.01  tff(c_508, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_303])).
% 5.41/2.01  tff(c_1044, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1033, c_508])).
% 5.41/2.01  tff(c_1058, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_333, c_474, c_334, c_474, c_396, c_396, c_594, c_1044])).
% 5.41/2.01  tff(c_1060, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_1058])).
% 5.41/2.01  tff(c_1061, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_303])).
% 5.41/2.01  tff(c_1608, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1599, c_1061])).
% 5.41/2.01  tff(c_1619, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_333, c_334, c_474, c_396, c_474, c_396, c_1152, c_1608])).
% 5.41/2.01  tff(c_1621, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_1619])).
% 5.41/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.41/2.01  
% 5.41/2.01  Inference rules
% 5.41/2.01  ----------------------
% 5.41/2.01  #Ref     : 0
% 5.41/2.01  #Sup     : 324
% 5.41/2.01  #Fact    : 0
% 5.41/2.01  #Define  : 0
% 5.41/2.01  #Split   : 9
% 5.41/2.01  #Chain   : 0
% 5.41/2.01  #Close   : 0
% 5.41/2.01  
% 5.41/2.01  Ordering : KBO
% 5.41/2.01  
% 5.41/2.01  Simplification rules
% 5.41/2.01  ----------------------
% 5.41/2.01  #Subsume      : 19
% 5.41/2.01  #Demod        : 211
% 5.41/2.01  #Tautology    : 122
% 5.41/2.01  #SimpNegUnit  : 110
% 5.41/2.01  #BackRed      : 2
% 5.41/2.01  
% 5.41/2.01  #Partial instantiations: 0
% 5.41/2.01  #Strategies tried      : 1
% 5.41/2.01  
% 5.41/2.01  Timing (in seconds)
% 5.41/2.01  ----------------------
% 5.41/2.01  Preprocessing        : 0.39
% 5.41/2.01  Parsing              : 0.19
% 5.41/2.01  CNF conversion       : 0.06
% 5.41/2.01  Main loop            : 0.79
% 5.41/2.01  Inferencing          : 0.28
% 5.41/2.01  Reduction            : 0.25
% 5.41/2.01  Demodulation         : 0.18
% 5.41/2.01  BG Simplification    : 0.04
% 5.41/2.01  Subsumption          : 0.18
% 5.41/2.01  Abstraction          : 0.04
% 5.41/2.01  MUC search           : 0.00
% 5.41/2.01  Cooper               : 0.00
% 5.41/2.01  Total                : 1.23
% 5.41/2.01  Index Insertion      : 0.00
% 5.41/2.01  Index Deletion       : 0.00
% 5.41/2.01  Index Matching       : 0.00
% 5.41/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
