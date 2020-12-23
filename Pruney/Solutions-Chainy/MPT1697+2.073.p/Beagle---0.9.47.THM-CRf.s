%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:21 EST 2020

% Result     : Theorem 6.79s
% Output     : CNFRefutation 7.11s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 393 expanded)
%              Number of leaves         :   34 ( 162 expanded)
%              Depth                    :   12
%              Number of atoms          :  535 (2395 expanded)
%              Number of equality atoms :   84 ( 431 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_181,negated_conjecture,(
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

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_47,axiom,(
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

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_139,axiom,(
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

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_105,axiom,(
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

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_32,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_64,plain,(
    ! [C_211,A_212,B_213] :
      ( v1_relat_1(C_211)
      | ~ m1_subset_1(C_211,k1_zfmisc_1(k2_zfmisc_1(A_212,B_213))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_71,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_32,c_64])).

tff(c_8,plain,(
    ! [A_6] :
      ( k7_relat_1(A_6,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_76,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_71,c_8])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_44,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_210,plain,(
    ! [A_235,B_236] :
      ( r1_xboole_0(A_235,B_236)
      | ~ r1_subset_1(A_235,B_236)
      | v1_xboole_0(B_236)
      | v1_xboole_0(A_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_763,plain,(
    ! [A_366,B_367] :
      ( k3_xboole_0(A_366,B_367) = k1_xboole_0
      | ~ r1_subset_1(A_366,B_367)
      | v1_xboole_0(B_367)
      | v1_xboole_0(A_366) ) ),
    inference(resolution,[status(thm)],[c_210,c_2])).

tff(c_769,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_763])).

tff(c_773,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_48,c_769])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_72,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_64])).

tff(c_80,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_72,c_8])).

tff(c_228,plain,(
    ! [A_239,B_240,C_241] :
      ( k9_subset_1(A_239,B_240,C_241) = k3_xboole_0(B_240,C_241)
      | ~ m1_subset_1(C_241,k1_zfmisc_1(A_239)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_240,plain,(
    ! [B_240] : k9_subset_1('#skF_1',B_240,'#skF_4') = k3_xboole_0(B_240,'#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_228])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_40,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_36,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_34,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_783,plain,(
    ! [D_372,C_371,A_368,F_370,B_369,E_373] :
      ( v1_funct_1(k1_tmap_1(A_368,B_369,C_371,D_372,E_373,F_370))
      | ~ m1_subset_1(F_370,k1_zfmisc_1(k2_zfmisc_1(D_372,B_369)))
      | ~ v1_funct_2(F_370,D_372,B_369)
      | ~ v1_funct_1(F_370)
      | ~ m1_subset_1(E_373,k1_zfmisc_1(k2_zfmisc_1(C_371,B_369)))
      | ~ v1_funct_2(E_373,C_371,B_369)
      | ~ v1_funct_1(E_373)
      | ~ m1_subset_1(D_372,k1_zfmisc_1(A_368))
      | v1_xboole_0(D_372)
      | ~ m1_subset_1(C_371,k1_zfmisc_1(A_368))
      | v1_xboole_0(C_371)
      | v1_xboole_0(B_369)
      | v1_xboole_0(A_368) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_785,plain,(
    ! [A_368,C_371,E_373] :
      ( v1_funct_1(k1_tmap_1(A_368,'#skF_2',C_371,'#skF_4',E_373,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_373,k1_zfmisc_1(k2_zfmisc_1(C_371,'#skF_2')))
      | ~ v1_funct_2(E_373,C_371,'#skF_2')
      | ~ v1_funct_1(E_373)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_368))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_371,k1_zfmisc_1(A_368))
      | v1_xboole_0(C_371)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_368) ) ),
    inference(resolution,[status(thm)],[c_32,c_783])).

tff(c_790,plain,(
    ! [A_368,C_371,E_373] :
      ( v1_funct_1(k1_tmap_1(A_368,'#skF_2',C_371,'#skF_4',E_373,'#skF_6'))
      | ~ m1_subset_1(E_373,k1_zfmisc_1(k2_zfmisc_1(C_371,'#skF_2')))
      | ~ v1_funct_2(E_373,C_371,'#skF_2')
      | ~ v1_funct_1(E_373)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_368))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_371,k1_zfmisc_1(A_368))
      | v1_xboole_0(C_371)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_368) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_785])).

tff(c_796,plain,(
    ! [A_374,C_375,E_376] :
      ( v1_funct_1(k1_tmap_1(A_374,'#skF_2',C_375,'#skF_4',E_376,'#skF_6'))
      | ~ m1_subset_1(E_376,k1_zfmisc_1(k2_zfmisc_1(C_375,'#skF_2')))
      | ~ v1_funct_2(E_376,C_375,'#skF_2')
      | ~ v1_funct_1(E_376)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_374))
      | ~ m1_subset_1(C_375,k1_zfmisc_1(A_374))
      | v1_xboole_0(C_375)
      | v1_xboole_0(A_374) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_790])).

tff(c_800,plain,(
    ! [A_374] :
      ( v1_funct_1(k1_tmap_1(A_374,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_374))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_374))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_374) ) ),
    inference(resolution,[status(thm)],[c_38,c_796])).

tff(c_807,plain,(
    ! [A_374] :
      ( v1_funct_1(k1_tmap_1(A_374,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_374))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_374))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_374) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_800])).

tff(c_816,plain,(
    ! [A_378] :
      ( v1_funct_1(k1_tmap_1(A_378,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_378))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_378))
      | v1_xboole_0(A_378) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_807])).

tff(c_819,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_816])).

tff(c_822,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_819])).

tff(c_823,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_822])).

tff(c_269,plain,(
    ! [A_245,B_246,C_247,D_248] :
      ( k2_partfun1(A_245,B_246,C_247,D_248) = k7_relat_1(C_247,D_248)
      | ~ m1_subset_1(C_247,k1_zfmisc_1(k2_zfmisc_1(A_245,B_246)))
      | ~ v1_funct_1(C_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_273,plain,(
    ! [D_248] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_248) = k7_relat_1('#skF_5',D_248)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_38,c_269])).

tff(c_279,plain,(
    ! [D_248] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_248) = k7_relat_1('#skF_5',D_248) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_273])).

tff(c_271,plain,(
    ! [D_248] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_248) = k7_relat_1('#skF_6',D_248)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_32,c_269])).

tff(c_276,plain,(
    ! [D_248] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_248) = k7_relat_1('#skF_6',D_248) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_271])).

tff(c_26,plain,(
    ! [B_144,A_143,F_148,C_145,E_147,D_146] :
      ( v1_funct_2(k1_tmap_1(A_143,B_144,C_145,D_146,E_147,F_148),k4_subset_1(A_143,C_145,D_146),B_144)
      | ~ m1_subset_1(F_148,k1_zfmisc_1(k2_zfmisc_1(D_146,B_144)))
      | ~ v1_funct_2(F_148,D_146,B_144)
      | ~ v1_funct_1(F_148)
      | ~ m1_subset_1(E_147,k1_zfmisc_1(k2_zfmisc_1(C_145,B_144)))
      | ~ v1_funct_2(E_147,C_145,B_144)
      | ~ v1_funct_1(E_147)
      | ~ m1_subset_1(D_146,k1_zfmisc_1(A_143))
      | v1_xboole_0(D_146)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(A_143))
      | v1_xboole_0(C_145)
      | v1_xboole_0(B_144)
      | v1_xboole_0(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_24,plain,(
    ! [B_144,A_143,F_148,C_145,E_147,D_146] :
      ( m1_subset_1(k1_tmap_1(A_143,B_144,C_145,D_146,E_147,F_148),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_143,C_145,D_146),B_144)))
      | ~ m1_subset_1(F_148,k1_zfmisc_1(k2_zfmisc_1(D_146,B_144)))
      | ~ v1_funct_2(F_148,D_146,B_144)
      | ~ v1_funct_1(F_148)
      | ~ m1_subset_1(E_147,k1_zfmisc_1(k2_zfmisc_1(C_145,B_144)))
      | ~ v1_funct_2(E_147,C_145,B_144)
      | ~ v1_funct_1(E_147)
      | ~ m1_subset_1(D_146,k1_zfmisc_1(A_143))
      | v1_xboole_0(D_146)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(A_143))
      | v1_xboole_0(C_145)
      | v1_xboole_0(B_144)
      | v1_xboole_0(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_996,plain,(
    ! [A_427,F_428,C_424,B_429,E_426,D_425] :
      ( k2_partfun1(k4_subset_1(A_427,C_424,D_425),B_429,k1_tmap_1(A_427,B_429,C_424,D_425,E_426,F_428),C_424) = E_426
      | ~ m1_subset_1(k1_tmap_1(A_427,B_429,C_424,D_425,E_426,F_428),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_427,C_424,D_425),B_429)))
      | ~ v1_funct_2(k1_tmap_1(A_427,B_429,C_424,D_425,E_426,F_428),k4_subset_1(A_427,C_424,D_425),B_429)
      | ~ v1_funct_1(k1_tmap_1(A_427,B_429,C_424,D_425,E_426,F_428))
      | k2_partfun1(D_425,B_429,F_428,k9_subset_1(A_427,C_424,D_425)) != k2_partfun1(C_424,B_429,E_426,k9_subset_1(A_427,C_424,D_425))
      | ~ m1_subset_1(F_428,k1_zfmisc_1(k2_zfmisc_1(D_425,B_429)))
      | ~ v1_funct_2(F_428,D_425,B_429)
      | ~ v1_funct_1(F_428)
      | ~ m1_subset_1(E_426,k1_zfmisc_1(k2_zfmisc_1(C_424,B_429)))
      | ~ v1_funct_2(E_426,C_424,B_429)
      | ~ v1_funct_1(E_426)
      | ~ m1_subset_1(D_425,k1_zfmisc_1(A_427))
      | v1_xboole_0(D_425)
      | ~ m1_subset_1(C_424,k1_zfmisc_1(A_427))
      | v1_xboole_0(C_424)
      | v1_xboole_0(B_429)
      | v1_xboole_0(A_427) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1153,plain,(
    ! [E_476,D_475,A_471,B_472,C_474,F_473] :
      ( k2_partfun1(k4_subset_1(A_471,C_474,D_475),B_472,k1_tmap_1(A_471,B_472,C_474,D_475,E_476,F_473),C_474) = E_476
      | ~ v1_funct_2(k1_tmap_1(A_471,B_472,C_474,D_475,E_476,F_473),k4_subset_1(A_471,C_474,D_475),B_472)
      | ~ v1_funct_1(k1_tmap_1(A_471,B_472,C_474,D_475,E_476,F_473))
      | k2_partfun1(D_475,B_472,F_473,k9_subset_1(A_471,C_474,D_475)) != k2_partfun1(C_474,B_472,E_476,k9_subset_1(A_471,C_474,D_475))
      | ~ m1_subset_1(F_473,k1_zfmisc_1(k2_zfmisc_1(D_475,B_472)))
      | ~ v1_funct_2(F_473,D_475,B_472)
      | ~ v1_funct_1(F_473)
      | ~ m1_subset_1(E_476,k1_zfmisc_1(k2_zfmisc_1(C_474,B_472)))
      | ~ v1_funct_2(E_476,C_474,B_472)
      | ~ v1_funct_1(E_476)
      | ~ m1_subset_1(D_475,k1_zfmisc_1(A_471))
      | v1_xboole_0(D_475)
      | ~ m1_subset_1(C_474,k1_zfmisc_1(A_471))
      | v1_xboole_0(C_474)
      | v1_xboole_0(B_472)
      | v1_xboole_0(A_471) ) ),
    inference(resolution,[status(thm)],[c_24,c_996])).

tff(c_1157,plain,(
    ! [F_479,E_482,D_481,B_478,C_480,A_477] :
      ( k2_partfun1(k4_subset_1(A_477,C_480,D_481),B_478,k1_tmap_1(A_477,B_478,C_480,D_481,E_482,F_479),C_480) = E_482
      | ~ v1_funct_1(k1_tmap_1(A_477,B_478,C_480,D_481,E_482,F_479))
      | k2_partfun1(D_481,B_478,F_479,k9_subset_1(A_477,C_480,D_481)) != k2_partfun1(C_480,B_478,E_482,k9_subset_1(A_477,C_480,D_481))
      | ~ m1_subset_1(F_479,k1_zfmisc_1(k2_zfmisc_1(D_481,B_478)))
      | ~ v1_funct_2(F_479,D_481,B_478)
      | ~ v1_funct_1(F_479)
      | ~ m1_subset_1(E_482,k1_zfmisc_1(k2_zfmisc_1(C_480,B_478)))
      | ~ v1_funct_2(E_482,C_480,B_478)
      | ~ v1_funct_1(E_482)
      | ~ m1_subset_1(D_481,k1_zfmisc_1(A_477))
      | v1_xboole_0(D_481)
      | ~ m1_subset_1(C_480,k1_zfmisc_1(A_477))
      | v1_xboole_0(C_480)
      | v1_xboole_0(B_478)
      | v1_xboole_0(A_477) ) ),
    inference(resolution,[status(thm)],[c_26,c_1153])).

tff(c_1161,plain,(
    ! [A_477,C_480,E_482] :
      ( k2_partfun1(k4_subset_1(A_477,C_480,'#skF_4'),'#skF_2',k1_tmap_1(A_477,'#skF_2',C_480,'#skF_4',E_482,'#skF_6'),C_480) = E_482
      | ~ v1_funct_1(k1_tmap_1(A_477,'#skF_2',C_480,'#skF_4',E_482,'#skF_6'))
      | k2_partfun1(C_480,'#skF_2',E_482,k9_subset_1(A_477,C_480,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_477,C_480,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_482,k1_zfmisc_1(k2_zfmisc_1(C_480,'#skF_2')))
      | ~ v1_funct_2(E_482,C_480,'#skF_2')
      | ~ v1_funct_1(E_482)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_477))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_480,k1_zfmisc_1(A_477))
      | v1_xboole_0(C_480)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_477) ) ),
    inference(resolution,[status(thm)],[c_32,c_1157])).

tff(c_1167,plain,(
    ! [A_477,C_480,E_482] :
      ( k2_partfun1(k4_subset_1(A_477,C_480,'#skF_4'),'#skF_2',k1_tmap_1(A_477,'#skF_2',C_480,'#skF_4',E_482,'#skF_6'),C_480) = E_482
      | ~ v1_funct_1(k1_tmap_1(A_477,'#skF_2',C_480,'#skF_4',E_482,'#skF_6'))
      | k2_partfun1(C_480,'#skF_2',E_482,k9_subset_1(A_477,C_480,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_477,C_480,'#skF_4'))
      | ~ m1_subset_1(E_482,k1_zfmisc_1(k2_zfmisc_1(C_480,'#skF_2')))
      | ~ v1_funct_2(E_482,C_480,'#skF_2')
      | ~ v1_funct_1(E_482)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_477))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_480,k1_zfmisc_1(A_477))
      | v1_xboole_0(C_480)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_477) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_276,c_1161])).

tff(c_1173,plain,(
    ! [A_483,C_484,E_485] :
      ( k2_partfun1(k4_subset_1(A_483,C_484,'#skF_4'),'#skF_2',k1_tmap_1(A_483,'#skF_2',C_484,'#skF_4',E_485,'#skF_6'),C_484) = E_485
      | ~ v1_funct_1(k1_tmap_1(A_483,'#skF_2',C_484,'#skF_4',E_485,'#skF_6'))
      | k2_partfun1(C_484,'#skF_2',E_485,k9_subset_1(A_483,C_484,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_483,C_484,'#skF_4'))
      | ~ m1_subset_1(E_485,k1_zfmisc_1(k2_zfmisc_1(C_484,'#skF_2')))
      | ~ v1_funct_2(E_485,C_484,'#skF_2')
      | ~ v1_funct_1(E_485)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_483))
      | ~ m1_subset_1(C_484,k1_zfmisc_1(A_483))
      | v1_xboole_0(C_484)
      | v1_xboole_0(A_483) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_1167])).

tff(c_1180,plain,(
    ! [A_483] :
      ( k2_partfun1(k4_subset_1(A_483,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_483,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_483,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_483,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_483,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_483))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_483))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_483) ) ),
    inference(resolution,[status(thm)],[c_38,c_1173])).

tff(c_1190,plain,(
    ! [A_483] :
      ( k2_partfun1(k4_subset_1(A_483,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_483,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_483,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_483,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_483,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_483))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_483))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_483) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_279,c_1180])).

tff(c_1229,plain,(
    ! [A_494] :
      ( k2_partfun1(k4_subset_1(A_494,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_494,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_494,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_494,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_494,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_494))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_494))
      | v1_xboole_0(A_494) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1190])).

tff(c_309,plain,(
    ! [A_254,B_255] :
      ( k3_xboole_0(A_254,B_255) = k1_xboole_0
      | ~ r1_subset_1(A_254,B_255)
      | v1_xboole_0(B_255)
      | v1_xboole_0(A_254) ) ),
    inference(resolution,[status(thm)],[c_210,c_2])).

tff(c_315,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_309])).

tff(c_319,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_48,c_315])).

tff(c_325,plain,(
    ! [D_260,F_258,C_259,A_256,E_261,B_257] :
      ( v1_funct_1(k1_tmap_1(A_256,B_257,C_259,D_260,E_261,F_258))
      | ~ m1_subset_1(F_258,k1_zfmisc_1(k2_zfmisc_1(D_260,B_257)))
      | ~ v1_funct_2(F_258,D_260,B_257)
      | ~ v1_funct_1(F_258)
      | ~ m1_subset_1(E_261,k1_zfmisc_1(k2_zfmisc_1(C_259,B_257)))
      | ~ v1_funct_2(E_261,C_259,B_257)
      | ~ v1_funct_1(E_261)
      | ~ m1_subset_1(D_260,k1_zfmisc_1(A_256))
      | v1_xboole_0(D_260)
      | ~ m1_subset_1(C_259,k1_zfmisc_1(A_256))
      | v1_xboole_0(C_259)
      | v1_xboole_0(B_257)
      | v1_xboole_0(A_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_327,plain,(
    ! [A_256,C_259,E_261] :
      ( v1_funct_1(k1_tmap_1(A_256,'#skF_2',C_259,'#skF_4',E_261,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_261,k1_zfmisc_1(k2_zfmisc_1(C_259,'#skF_2')))
      | ~ v1_funct_2(E_261,C_259,'#skF_2')
      | ~ v1_funct_1(E_261)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_256))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_259,k1_zfmisc_1(A_256))
      | v1_xboole_0(C_259)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_256) ) ),
    inference(resolution,[status(thm)],[c_32,c_325])).

tff(c_332,plain,(
    ! [A_256,C_259,E_261] :
      ( v1_funct_1(k1_tmap_1(A_256,'#skF_2',C_259,'#skF_4',E_261,'#skF_6'))
      | ~ m1_subset_1(E_261,k1_zfmisc_1(k2_zfmisc_1(C_259,'#skF_2')))
      | ~ v1_funct_2(E_261,C_259,'#skF_2')
      | ~ v1_funct_1(E_261)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_256))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_259,k1_zfmisc_1(A_256))
      | v1_xboole_0(C_259)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_256) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_327])).

tff(c_338,plain,(
    ! [A_262,C_263,E_264] :
      ( v1_funct_1(k1_tmap_1(A_262,'#skF_2',C_263,'#skF_4',E_264,'#skF_6'))
      | ~ m1_subset_1(E_264,k1_zfmisc_1(k2_zfmisc_1(C_263,'#skF_2')))
      | ~ v1_funct_2(E_264,C_263,'#skF_2')
      | ~ v1_funct_1(E_264)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_262))
      | ~ m1_subset_1(C_263,k1_zfmisc_1(A_262))
      | v1_xboole_0(C_263)
      | v1_xboole_0(A_262) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_332])).

tff(c_342,plain,(
    ! [A_262] :
      ( v1_funct_1(k1_tmap_1(A_262,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_262))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_262))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_262) ) ),
    inference(resolution,[status(thm)],[c_38,c_338])).

tff(c_349,plain,(
    ! [A_262] :
      ( v1_funct_1(k1_tmap_1(A_262,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_262))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_262))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_262) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_342])).

tff(c_358,plain,(
    ! [A_266] :
      ( v1_funct_1(k1_tmap_1(A_266,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_266))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_266))
      | v1_xboole_0(A_266) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_349])).

tff(c_361,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_358])).

tff(c_364,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_361])).

tff(c_365,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_364])).

tff(c_550,plain,(
    ! [B_318,C_313,D_314,A_316,E_315,F_317] :
      ( k2_partfun1(k4_subset_1(A_316,C_313,D_314),B_318,k1_tmap_1(A_316,B_318,C_313,D_314,E_315,F_317),D_314) = F_317
      | ~ m1_subset_1(k1_tmap_1(A_316,B_318,C_313,D_314,E_315,F_317),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_316,C_313,D_314),B_318)))
      | ~ v1_funct_2(k1_tmap_1(A_316,B_318,C_313,D_314,E_315,F_317),k4_subset_1(A_316,C_313,D_314),B_318)
      | ~ v1_funct_1(k1_tmap_1(A_316,B_318,C_313,D_314,E_315,F_317))
      | k2_partfun1(D_314,B_318,F_317,k9_subset_1(A_316,C_313,D_314)) != k2_partfun1(C_313,B_318,E_315,k9_subset_1(A_316,C_313,D_314))
      | ~ m1_subset_1(F_317,k1_zfmisc_1(k2_zfmisc_1(D_314,B_318)))
      | ~ v1_funct_2(F_317,D_314,B_318)
      | ~ v1_funct_1(F_317)
      | ~ m1_subset_1(E_315,k1_zfmisc_1(k2_zfmisc_1(C_313,B_318)))
      | ~ v1_funct_2(E_315,C_313,B_318)
      | ~ v1_funct_1(E_315)
      | ~ m1_subset_1(D_314,k1_zfmisc_1(A_316))
      | v1_xboole_0(D_314)
      | ~ m1_subset_1(C_313,k1_zfmisc_1(A_316))
      | v1_xboole_0(C_313)
      | v1_xboole_0(B_318)
      | v1_xboole_0(A_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_650,plain,(
    ! [C_345,A_342,D_346,F_344,B_343,E_347] :
      ( k2_partfun1(k4_subset_1(A_342,C_345,D_346),B_343,k1_tmap_1(A_342,B_343,C_345,D_346,E_347,F_344),D_346) = F_344
      | ~ v1_funct_2(k1_tmap_1(A_342,B_343,C_345,D_346,E_347,F_344),k4_subset_1(A_342,C_345,D_346),B_343)
      | ~ v1_funct_1(k1_tmap_1(A_342,B_343,C_345,D_346,E_347,F_344))
      | k2_partfun1(D_346,B_343,F_344,k9_subset_1(A_342,C_345,D_346)) != k2_partfun1(C_345,B_343,E_347,k9_subset_1(A_342,C_345,D_346))
      | ~ m1_subset_1(F_344,k1_zfmisc_1(k2_zfmisc_1(D_346,B_343)))
      | ~ v1_funct_2(F_344,D_346,B_343)
      | ~ v1_funct_1(F_344)
      | ~ m1_subset_1(E_347,k1_zfmisc_1(k2_zfmisc_1(C_345,B_343)))
      | ~ v1_funct_2(E_347,C_345,B_343)
      | ~ v1_funct_1(E_347)
      | ~ m1_subset_1(D_346,k1_zfmisc_1(A_342))
      | v1_xboole_0(D_346)
      | ~ m1_subset_1(C_345,k1_zfmisc_1(A_342))
      | v1_xboole_0(C_345)
      | v1_xboole_0(B_343)
      | v1_xboole_0(A_342) ) ),
    inference(resolution,[status(thm)],[c_24,c_550])).

tff(c_675,plain,(
    ! [A_353,C_356,D_357,F_355,B_354,E_358] :
      ( k2_partfun1(k4_subset_1(A_353,C_356,D_357),B_354,k1_tmap_1(A_353,B_354,C_356,D_357,E_358,F_355),D_357) = F_355
      | ~ v1_funct_1(k1_tmap_1(A_353,B_354,C_356,D_357,E_358,F_355))
      | k2_partfun1(D_357,B_354,F_355,k9_subset_1(A_353,C_356,D_357)) != k2_partfun1(C_356,B_354,E_358,k9_subset_1(A_353,C_356,D_357))
      | ~ m1_subset_1(F_355,k1_zfmisc_1(k2_zfmisc_1(D_357,B_354)))
      | ~ v1_funct_2(F_355,D_357,B_354)
      | ~ v1_funct_1(F_355)
      | ~ m1_subset_1(E_358,k1_zfmisc_1(k2_zfmisc_1(C_356,B_354)))
      | ~ v1_funct_2(E_358,C_356,B_354)
      | ~ v1_funct_1(E_358)
      | ~ m1_subset_1(D_357,k1_zfmisc_1(A_353))
      | v1_xboole_0(D_357)
      | ~ m1_subset_1(C_356,k1_zfmisc_1(A_353))
      | v1_xboole_0(C_356)
      | v1_xboole_0(B_354)
      | v1_xboole_0(A_353) ) ),
    inference(resolution,[status(thm)],[c_26,c_650])).

tff(c_679,plain,(
    ! [A_353,C_356,E_358] :
      ( k2_partfun1(k4_subset_1(A_353,C_356,'#skF_4'),'#skF_2',k1_tmap_1(A_353,'#skF_2',C_356,'#skF_4',E_358,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_353,'#skF_2',C_356,'#skF_4',E_358,'#skF_6'))
      | k2_partfun1(C_356,'#skF_2',E_358,k9_subset_1(A_353,C_356,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_353,C_356,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_358,k1_zfmisc_1(k2_zfmisc_1(C_356,'#skF_2')))
      | ~ v1_funct_2(E_358,C_356,'#skF_2')
      | ~ v1_funct_1(E_358)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_353))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_356,k1_zfmisc_1(A_353))
      | v1_xboole_0(C_356)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_353) ) ),
    inference(resolution,[status(thm)],[c_32,c_675])).

tff(c_685,plain,(
    ! [A_353,C_356,E_358] :
      ( k2_partfun1(k4_subset_1(A_353,C_356,'#skF_4'),'#skF_2',k1_tmap_1(A_353,'#skF_2',C_356,'#skF_4',E_358,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_353,'#skF_2',C_356,'#skF_4',E_358,'#skF_6'))
      | k2_partfun1(C_356,'#skF_2',E_358,k9_subset_1(A_353,C_356,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_353,C_356,'#skF_4'))
      | ~ m1_subset_1(E_358,k1_zfmisc_1(k2_zfmisc_1(C_356,'#skF_2')))
      | ~ v1_funct_2(E_358,C_356,'#skF_2')
      | ~ v1_funct_1(E_358)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_353))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_356,k1_zfmisc_1(A_353))
      | v1_xboole_0(C_356)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_353) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_276,c_679])).

tff(c_691,plain,(
    ! [A_359,C_360,E_361] :
      ( k2_partfun1(k4_subset_1(A_359,C_360,'#skF_4'),'#skF_2',k1_tmap_1(A_359,'#skF_2',C_360,'#skF_4',E_361,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_359,'#skF_2',C_360,'#skF_4',E_361,'#skF_6'))
      | k2_partfun1(C_360,'#skF_2',E_361,k9_subset_1(A_359,C_360,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_359,C_360,'#skF_4'))
      | ~ m1_subset_1(E_361,k1_zfmisc_1(k2_zfmisc_1(C_360,'#skF_2')))
      | ~ v1_funct_2(E_361,C_360,'#skF_2')
      | ~ v1_funct_1(E_361)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_359))
      | ~ m1_subset_1(C_360,k1_zfmisc_1(A_359))
      | v1_xboole_0(C_360)
      | v1_xboole_0(A_359) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_685])).

tff(c_698,plain,(
    ! [A_359] :
      ( k2_partfun1(k4_subset_1(A_359,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_359,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_359,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_359,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_359,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_359))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_359))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_359) ) ),
    inference(resolution,[status(thm)],[c_38,c_691])).

tff(c_708,plain,(
    ! [A_359] :
      ( k2_partfun1(k4_subset_1(A_359,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_359,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_359,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_359,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_359,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_359))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_359))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_359) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_279,c_698])).

tff(c_732,plain,(
    ! [A_363] :
      ( k2_partfun1(k4_subset_1(A_363,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_363,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_363,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_363,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_363,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_363))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_363))
      | v1_xboole_0(A_363) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_708])).

tff(c_90,plain,(
    ! [A_214,B_215] :
      ( r1_xboole_0(A_214,B_215)
      | ~ r1_subset_1(A_214,B_215)
      | v1_xboole_0(B_215)
      | v1_xboole_0(A_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_183,plain,(
    ! [A_233,B_234] :
      ( k3_xboole_0(A_233,B_234) = k1_xboole_0
      | ~ r1_subset_1(A_233,B_234)
      | v1_xboole_0(B_234)
      | v1_xboole_0(A_233) ) ),
    inference(resolution,[status(thm)],[c_90,c_2])).

tff(c_189,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_183])).

tff(c_193,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_48,c_189])).

tff(c_117,plain,(
    ! [A_221,B_222,C_223,D_224] :
      ( k2_partfun1(A_221,B_222,C_223,D_224) = k7_relat_1(C_223,D_224)
      | ~ m1_subset_1(C_223,k1_zfmisc_1(k2_zfmisc_1(A_221,B_222)))
      | ~ v1_funct_1(C_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_119,plain,(
    ! [D_224] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_224) = k7_relat_1('#skF_6',D_224)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_32,c_117])).

tff(c_124,plain,(
    ! [D_224] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_224) = k7_relat_1('#skF_6',D_224) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_119])).

tff(c_121,plain,(
    ! [D_224] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_224) = k7_relat_1('#skF_5',D_224)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_38,c_117])).

tff(c_127,plain,(
    ! [D_224] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_224) = k7_relat_1('#skF_5',D_224) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_121])).

tff(c_104,plain,(
    ! [A_218,B_219,C_220] :
      ( k9_subset_1(A_218,B_219,C_220) = k3_xboole_0(B_219,C_220)
      | ~ m1_subset_1(C_220,k1_zfmisc_1(A_218)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_116,plain,(
    ! [B_219] : k9_subset_1('#skF_1',B_219,'#skF_4') = k3_xboole_0(B_219,'#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_104])).

tff(c_30,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_81,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_199,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_193,c_80,c_193,c_124,c_127,c_116,c_116,c_81])).

tff(c_200,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_307,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_200])).

tff(c_743,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_732,c_307])).

tff(c_757,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_76,c_319,c_80,c_319,c_240,c_240,c_365,c_743])).

tff(c_759,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_757])).

tff(c_760,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_200])).

tff(c_1238,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1229,c_760])).

tff(c_1249,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_76,c_773,c_80,c_773,c_240,c_240,c_823,c_1238])).

tff(c_1251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1249])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:47:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.79/2.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.79/2.59  
% 6.79/2.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.11/2.59  %$ v1_funct_2 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.11/2.59  
% 7.11/2.59  %Foreground sorts:
% 7.11/2.59  
% 7.11/2.59  
% 7.11/2.59  %Background operators:
% 7.11/2.59  
% 7.11/2.59  
% 7.11/2.59  %Foreground operators:
% 7.11/2.59  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 7.11/2.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.11/2.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.11/2.59  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.11/2.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.11/2.59  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 7.11/2.59  tff('#skF_5', type, '#skF_5': $i).
% 7.11/2.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.11/2.59  tff('#skF_6', type, '#skF_6': $i).
% 7.11/2.59  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.11/2.59  tff('#skF_2', type, '#skF_2': $i).
% 7.11/2.59  tff('#skF_3', type, '#skF_3': $i).
% 7.11/2.59  tff('#skF_1', type, '#skF_1': $i).
% 7.11/2.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.11/2.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.11/2.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.11/2.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.11/2.59  tff('#skF_4', type, '#skF_4': $i).
% 7.11/2.59  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.11/2.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.11/2.59  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 7.11/2.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.11/2.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.11/2.59  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.11/2.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.11/2.59  
% 7.11/2.63  tff(f_181, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 7.11/2.63  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.11/2.63  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_relat_1)).
% 7.11/2.63  tff(f_47, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 7.11/2.63  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 7.11/2.63  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 7.11/2.63  tff(f_139, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 7.11/2.63  tff(f_57, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 7.11/2.63  tff(f_105, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 7.11/2.63  tff(c_56, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_181])).
% 7.11/2.63  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_181])).
% 7.11/2.63  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_181])).
% 7.11/2.63  tff(c_32, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_181])).
% 7.11/2.63  tff(c_64, plain, (![C_211, A_212, B_213]: (v1_relat_1(C_211) | ~m1_subset_1(C_211, k1_zfmisc_1(k2_zfmisc_1(A_212, B_213))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.11/2.63  tff(c_71, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_32, c_64])).
% 7.11/2.63  tff(c_8, plain, (![A_6]: (k7_relat_1(A_6, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.11/2.63  tff(c_76, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_71, c_8])).
% 7.11/2.63  tff(c_52, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_181])).
% 7.11/2.63  tff(c_48, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_181])).
% 7.11/2.63  tff(c_44, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_181])).
% 7.11/2.63  tff(c_210, plain, (![A_235, B_236]: (r1_xboole_0(A_235, B_236) | ~r1_subset_1(A_235, B_236) | v1_xboole_0(B_236) | v1_xboole_0(A_235))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.11/2.63  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.11/2.63  tff(c_763, plain, (![A_366, B_367]: (k3_xboole_0(A_366, B_367)=k1_xboole_0 | ~r1_subset_1(A_366, B_367) | v1_xboole_0(B_367) | v1_xboole_0(A_366))), inference(resolution, [status(thm)], [c_210, c_2])).
% 7.11/2.63  tff(c_769, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_763])).
% 7.11/2.63  tff(c_773, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_52, c_48, c_769])).
% 7.11/2.63  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_181])).
% 7.11/2.63  tff(c_72, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_64])).
% 7.11/2.63  tff(c_80, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_72, c_8])).
% 7.11/2.63  tff(c_228, plain, (![A_239, B_240, C_241]: (k9_subset_1(A_239, B_240, C_241)=k3_xboole_0(B_240, C_241) | ~m1_subset_1(C_241, k1_zfmisc_1(A_239)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.11/2.63  tff(c_240, plain, (![B_240]: (k9_subset_1('#skF_1', B_240, '#skF_4')=k3_xboole_0(B_240, '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_228])).
% 7.11/2.63  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_181])).
% 7.11/2.63  tff(c_40, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_181])).
% 7.11/2.63  tff(c_54, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_181])).
% 7.11/2.63  tff(c_36, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_181])).
% 7.11/2.63  tff(c_34, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_181])).
% 7.11/2.63  tff(c_783, plain, (![D_372, C_371, A_368, F_370, B_369, E_373]: (v1_funct_1(k1_tmap_1(A_368, B_369, C_371, D_372, E_373, F_370)) | ~m1_subset_1(F_370, k1_zfmisc_1(k2_zfmisc_1(D_372, B_369))) | ~v1_funct_2(F_370, D_372, B_369) | ~v1_funct_1(F_370) | ~m1_subset_1(E_373, k1_zfmisc_1(k2_zfmisc_1(C_371, B_369))) | ~v1_funct_2(E_373, C_371, B_369) | ~v1_funct_1(E_373) | ~m1_subset_1(D_372, k1_zfmisc_1(A_368)) | v1_xboole_0(D_372) | ~m1_subset_1(C_371, k1_zfmisc_1(A_368)) | v1_xboole_0(C_371) | v1_xboole_0(B_369) | v1_xboole_0(A_368))), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.11/2.63  tff(c_785, plain, (![A_368, C_371, E_373]: (v1_funct_1(k1_tmap_1(A_368, '#skF_2', C_371, '#skF_4', E_373, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_373, k1_zfmisc_1(k2_zfmisc_1(C_371, '#skF_2'))) | ~v1_funct_2(E_373, C_371, '#skF_2') | ~v1_funct_1(E_373) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_368)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_371, k1_zfmisc_1(A_368)) | v1_xboole_0(C_371) | v1_xboole_0('#skF_2') | v1_xboole_0(A_368))), inference(resolution, [status(thm)], [c_32, c_783])).
% 7.11/2.63  tff(c_790, plain, (![A_368, C_371, E_373]: (v1_funct_1(k1_tmap_1(A_368, '#skF_2', C_371, '#skF_4', E_373, '#skF_6')) | ~m1_subset_1(E_373, k1_zfmisc_1(k2_zfmisc_1(C_371, '#skF_2'))) | ~v1_funct_2(E_373, C_371, '#skF_2') | ~v1_funct_1(E_373) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_368)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_371, k1_zfmisc_1(A_368)) | v1_xboole_0(C_371) | v1_xboole_0('#skF_2') | v1_xboole_0(A_368))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_785])).
% 7.11/2.63  tff(c_796, plain, (![A_374, C_375, E_376]: (v1_funct_1(k1_tmap_1(A_374, '#skF_2', C_375, '#skF_4', E_376, '#skF_6')) | ~m1_subset_1(E_376, k1_zfmisc_1(k2_zfmisc_1(C_375, '#skF_2'))) | ~v1_funct_2(E_376, C_375, '#skF_2') | ~v1_funct_1(E_376) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_374)) | ~m1_subset_1(C_375, k1_zfmisc_1(A_374)) | v1_xboole_0(C_375) | v1_xboole_0(A_374))), inference(negUnitSimplification, [status(thm)], [c_54, c_48, c_790])).
% 7.11/2.63  tff(c_800, plain, (![A_374]: (v1_funct_1(k1_tmap_1(A_374, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_374)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_374)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_374))), inference(resolution, [status(thm)], [c_38, c_796])).
% 7.11/2.63  tff(c_807, plain, (![A_374]: (v1_funct_1(k1_tmap_1(A_374, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_374)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_374)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_374))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_800])).
% 7.11/2.63  tff(c_816, plain, (![A_378]: (v1_funct_1(k1_tmap_1(A_378, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_378)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_378)) | v1_xboole_0(A_378))), inference(negUnitSimplification, [status(thm)], [c_52, c_807])).
% 7.11/2.63  tff(c_819, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_816])).
% 7.11/2.63  tff(c_822, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_819])).
% 7.11/2.63  tff(c_823, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_56, c_822])).
% 7.11/2.63  tff(c_269, plain, (![A_245, B_246, C_247, D_248]: (k2_partfun1(A_245, B_246, C_247, D_248)=k7_relat_1(C_247, D_248) | ~m1_subset_1(C_247, k1_zfmisc_1(k2_zfmisc_1(A_245, B_246))) | ~v1_funct_1(C_247))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.11/2.63  tff(c_273, plain, (![D_248]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_248)=k7_relat_1('#skF_5', D_248) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_38, c_269])).
% 7.11/2.63  tff(c_279, plain, (![D_248]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_248)=k7_relat_1('#skF_5', D_248))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_273])).
% 7.11/2.63  tff(c_271, plain, (![D_248]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_248)=k7_relat_1('#skF_6', D_248) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_32, c_269])).
% 7.11/2.63  tff(c_276, plain, (![D_248]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_248)=k7_relat_1('#skF_6', D_248))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_271])).
% 7.11/2.63  tff(c_26, plain, (![B_144, A_143, F_148, C_145, E_147, D_146]: (v1_funct_2(k1_tmap_1(A_143, B_144, C_145, D_146, E_147, F_148), k4_subset_1(A_143, C_145, D_146), B_144) | ~m1_subset_1(F_148, k1_zfmisc_1(k2_zfmisc_1(D_146, B_144))) | ~v1_funct_2(F_148, D_146, B_144) | ~v1_funct_1(F_148) | ~m1_subset_1(E_147, k1_zfmisc_1(k2_zfmisc_1(C_145, B_144))) | ~v1_funct_2(E_147, C_145, B_144) | ~v1_funct_1(E_147) | ~m1_subset_1(D_146, k1_zfmisc_1(A_143)) | v1_xboole_0(D_146) | ~m1_subset_1(C_145, k1_zfmisc_1(A_143)) | v1_xboole_0(C_145) | v1_xboole_0(B_144) | v1_xboole_0(A_143))), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.11/2.63  tff(c_24, plain, (![B_144, A_143, F_148, C_145, E_147, D_146]: (m1_subset_1(k1_tmap_1(A_143, B_144, C_145, D_146, E_147, F_148), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_143, C_145, D_146), B_144))) | ~m1_subset_1(F_148, k1_zfmisc_1(k2_zfmisc_1(D_146, B_144))) | ~v1_funct_2(F_148, D_146, B_144) | ~v1_funct_1(F_148) | ~m1_subset_1(E_147, k1_zfmisc_1(k2_zfmisc_1(C_145, B_144))) | ~v1_funct_2(E_147, C_145, B_144) | ~v1_funct_1(E_147) | ~m1_subset_1(D_146, k1_zfmisc_1(A_143)) | v1_xboole_0(D_146) | ~m1_subset_1(C_145, k1_zfmisc_1(A_143)) | v1_xboole_0(C_145) | v1_xboole_0(B_144) | v1_xboole_0(A_143))), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.11/2.63  tff(c_996, plain, (![A_427, F_428, C_424, B_429, E_426, D_425]: (k2_partfun1(k4_subset_1(A_427, C_424, D_425), B_429, k1_tmap_1(A_427, B_429, C_424, D_425, E_426, F_428), C_424)=E_426 | ~m1_subset_1(k1_tmap_1(A_427, B_429, C_424, D_425, E_426, F_428), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_427, C_424, D_425), B_429))) | ~v1_funct_2(k1_tmap_1(A_427, B_429, C_424, D_425, E_426, F_428), k4_subset_1(A_427, C_424, D_425), B_429) | ~v1_funct_1(k1_tmap_1(A_427, B_429, C_424, D_425, E_426, F_428)) | k2_partfun1(D_425, B_429, F_428, k9_subset_1(A_427, C_424, D_425))!=k2_partfun1(C_424, B_429, E_426, k9_subset_1(A_427, C_424, D_425)) | ~m1_subset_1(F_428, k1_zfmisc_1(k2_zfmisc_1(D_425, B_429))) | ~v1_funct_2(F_428, D_425, B_429) | ~v1_funct_1(F_428) | ~m1_subset_1(E_426, k1_zfmisc_1(k2_zfmisc_1(C_424, B_429))) | ~v1_funct_2(E_426, C_424, B_429) | ~v1_funct_1(E_426) | ~m1_subset_1(D_425, k1_zfmisc_1(A_427)) | v1_xboole_0(D_425) | ~m1_subset_1(C_424, k1_zfmisc_1(A_427)) | v1_xboole_0(C_424) | v1_xboole_0(B_429) | v1_xboole_0(A_427))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.11/2.63  tff(c_1153, plain, (![E_476, D_475, A_471, B_472, C_474, F_473]: (k2_partfun1(k4_subset_1(A_471, C_474, D_475), B_472, k1_tmap_1(A_471, B_472, C_474, D_475, E_476, F_473), C_474)=E_476 | ~v1_funct_2(k1_tmap_1(A_471, B_472, C_474, D_475, E_476, F_473), k4_subset_1(A_471, C_474, D_475), B_472) | ~v1_funct_1(k1_tmap_1(A_471, B_472, C_474, D_475, E_476, F_473)) | k2_partfun1(D_475, B_472, F_473, k9_subset_1(A_471, C_474, D_475))!=k2_partfun1(C_474, B_472, E_476, k9_subset_1(A_471, C_474, D_475)) | ~m1_subset_1(F_473, k1_zfmisc_1(k2_zfmisc_1(D_475, B_472))) | ~v1_funct_2(F_473, D_475, B_472) | ~v1_funct_1(F_473) | ~m1_subset_1(E_476, k1_zfmisc_1(k2_zfmisc_1(C_474, B_472))) | ~v1_funct_2(E_476, C_474, B_472) | ~v1_funct_1(E_476) | ~m1_subset_1(D_475, k1_zfmisc_1(A_471)) | v1_xboole_0(D_475) | ~m1_subset_1(C_474, k1_zfmisc_1(A_471)) | v1_xboole_0(C_474) | v1_xboole_0(B_472) | v1_xboole_0(A_471))), inference(resolution, [status(thm)], [c_24, c_996])).
% 7.11/2.63  tff(c_1157, plain, (![F_479, E_482, D_481, B_478, C_480, A_477]: (k2_partfun1(k4_subset_1(A_477, C_480, D_481), B_478, k1_tmap_1(A_477, B_478, C_480, D_481, E_482, F_479), C_480)=E_482 | ~v1_funct_1(k1_tmap_1(A_477, B_478, C_480, D_481, E_482, F_479)) | k2_partfun1(D_481, B_478, F_479, k9_subset_1(A_477, C_480, D_481))!=k2_partfun1(C_480, B_478, E_482, k9_subset_1(A_477, C_480, D_481)) | ~m1_subset_1(F_479, k1_zfmisc_1(k2_zfmisc_1(D_481, B_478))) | ~v1_funct_2(F_479, D_481, B_478) | ~v1_funct_1(F_479) | ~m1_subset_1(E_482, k1_zfmisc_1(k2_zfmisc_1(C_480, B_478))) | ~v1_funct_2(E_482, C_480, B_478) | ~v1_funct_1(E_482) | ~m1_subset_1(D_481, k1_zfmisc_1(A_477)) | v1_xboole_0(D_481) | ~m1_subset_1(C_480, k1_zfmisc_1(A_477)) | v1_xboole_0(C_480) | v1_xboole_0(B_478) | v1_xboole_0(A_477))), inference(resolution, [status(thm)], [c_26, c_1153])).
% 7.11/2.63  tff(c_1161, plain, (![A_477, C_480, E_482]: (k2_partfun1(k4_subset_1(A_477, C_480, '#skF_4'), '#skF_2', k1_tmap_1(A_477, '#skF_2', C_480, '#skF_4', E_482, '#skF_6'), C_480)=E_482 | ~v1_funct_1(k1_tmap_1(A_477, '#skF_2', C_480, '#skF_4', E_482, '#skF_6')) | k2_partfun1(C_480, '#skF_2', E_482, k9_subset_1(A_477, C_480, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_477, C_480, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_482, k1_zfmisc_1(k2_zfmisc_1(C_480, '#skF_2'))) | ~v1_funct_2(E_482, C_480, '#skF_2') | ~v1_funct_1(E_482) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_477)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_480, k1_zfmisc_1(A_477)) | v1_xboole_0(C_480) | v1_xboole_0('#skF_2') | v1_xboole_0(A_477))), inference(resolution, [status(thm)], [c_32, c_1157])).
% 7.11/2.63  tff(c_1167, plain, (![A_477, C_480, E_482]: (k2_partfun1(k4_subset_1(A_477, C_480, '#skF_4'), '#skF_2', k1_tmap_1(A_477, '#skF_2', C_480, '#skF_4', E_482, '#skF_6'), C_480)=E_482 | ~v1_funct_1(k1_tmap_1(A_477, '#skF_2', C_480, '#skF_4', E_482, '#skF_6')) | k2_partfun1(C_480, '#skF_2', E_482, k9_subset_1(A_477, C_480, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_477, C_480, '#skF_4')) | ~m1_subset_1(E_482, k1_zfmisc_1(k2_zfmisc_1(C_480, '#skF_2'))) | ~v1_funct_2(E_482, C_480, '#skF_2') | ~v1_funct_1(E_482) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_477)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_480, k1_zfmisc_1(A_477)) | v1_xboole_0(C_480) | v1_xboole_0('#skF_2') | v1_xboole_0(A_477))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_276, c_1161])).
% 7.11/2.63  tff(c_1173, plain, (![A_483, C_484, E_485]: (k2_partfun1(k4_subset_1(A_483, C_484, '#skF_4'), '#skF_2', k1_tmap_1(A_483, '#skF_2', C_484, '#skF_4', E_485, '#skF_6'), C_484)=E_485 | ~v1_funct_1(k1_tmap_1(A_483, '#skF_2', C_484, '#skF_4', E_485, '#skF_6')) | k2_partfun1(C_484, '#skF_2', E_485, k9_subset_1(A_483, C_484, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_483, C_484, '#skF_4')) | ~m1_subset_1(E_485, k1_zfmisc_1(k2_zfmisc_1(C_484, '#skF_2'))) | ~v1_funct_2(E_485, C_484, '#skF_2') | ~v1_funct_1(E_485) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_483)) | ~m1_subset_1(C_484, k1_zfmisc_1(A_483)) | v1_xboole_0(C_484) | v1_xboole_0(A_483))), inference(negUnitSimplification, [status(thm)], [c_54, c_48, c_1167])).
% 7.11/2.63  tff(c_1180, plain, (![A_483]: (k2_partfun1(k4_subset_1(A_483, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_483, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_483, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_483, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_483, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_483)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_483)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_483))), inference(resolution, [status(thm)], [c_38, c_1173])).
% 7.11/2.63  tff(c_1190, plain, (![A_483]: (k2_partfun1(k4_subset_1(A_483, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_483, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_483, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_483, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_483, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_483)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_483)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_483))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_279, c_1180])).
% 7.11/2.63  tff(c_1229, plain, (![A_494]: (k2_partfun1(k4_subset_1(A_494, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_494, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_494, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_494, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_494, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_494)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_494)) | v1_xboole_0(A_494))), inference(negUnitSimplification, [status(thm)], [c_52, c_1190])).
% 7.11/2.63  tff(c_309, plain, (![A_254, B_255]: (k3_xboole_0(A_254, B_255)=k1_xboole_0 | ~r1_subset_1(A_254, B_255) | v1_xboole_0(B_255) | v1_xboole_0(A_254))), inference(resolution, [status(thm)], [c_210, c_2])).
% 7.11/2.63  tff(c_315, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_309])).
% 7.11/2.63  tff(c_319, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_52, c_48, c_315])).
% 7.11/2.63  tff(c_325, plain, (![D_260, F_258, C_259, A_256, E_261, B_257]: (v1_funct_1(k1_tmap_1(A_256, B_257, C_259, D_260, E_261, F_258)) | ~m1_subset_1(F_258, k1_zfmisc_1(k2_zfmisc_1(D_260, B_257))) | ~v1_funct_2(F_258, D_260, B_257) | ~v1_funct_1(F_258) | ~m1_subset_1(E_261, k1_zfmisc_1(k2_zfmisc_1(C_259, B_257))) | ~v1_funct_2(E_261, C_259, B_257) | ~v1_funct_1(E_261) | ~m1_subset_1(D_260, k1_zfmisc_1(A_256)) | v1_xboole_0(D_260) | ~m1_subset_1(C_259, k1_zfmisc_1(A_256)) | v1_xboole_0(C_259) | v1_xboole_0(B_257) | v1_xboole_0(A_256))), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.11/2.63  tff(c_327, plain, (![A_256, C_259, E_261]: (v1_funct_1(k1_tmap_1(A_256, '#skF_2', C_259, '#skF_4', E_261, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_261, k1_zfmisc_1(k2_zfmisc_1(C_259, '#skF_2'))) | ~v1_funct_2(E_261, C_259, '#skF_2') | ~v1_funct_1(E_261) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_256)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_259, k1_zfmisc_1(A_256)) | v1_xboole_0(C_259) | v1_xboole_0('#skF_2') | v1_xboole_0(A_256))), inference(resolution, [status(thm)], [c_32, c_325])).
% 7.11/2.63  tff(c_332, plain, (![A_256, C_259, E_261]: (v1_funct_1(k1_tmap_1(A_256, '#skF_2', C_259, '#skF_4', E_261, '#skF_6')) | ~m1_subset_1(E_261, k1_zfmisc_1(k2_zfmisc_1(C_259, '#skF_2'))) | ~v1_funct_2(E_261, C_259, '#skF_2') | ~v1_funct_1(E_261) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_256)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_259, k1_zfmisc_1(A_256)) | v1_xboole_0(C_259) | v1_xboole_0('#skF_2') | v1_xboole_0(A_256))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_327])).
% 7.11/2.63  tff(c_338, plain, (![A_262, C_263, E_264]: (v1_funct_1(k1_tmap_1(A_262, '#skF_2', C_263, '#skF_4', E_264, '#skF_6')) | ~m1_subset_1(E_264, k1_zfmisc_1(k2_zfmisc_1(C_263, '#skF_2'))) | ~v1_funct_2(E_264, C_263, '#skF_2') | ~v1_funct_1(E_264) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_262)) | ~m1_subset_1(C_263, k1_zfmisc_1(A_262)) | v1_xboole_0(C_263) | v1_xboole_0(A_262))), inference(negUnitSimplification, [status(thm)], [c_54, c_48, c_332])).
% 7.11/2.63  tff(c_342, plain, (![A_262]: (v1_funct_1(k1_tmap_1(A_262, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_262)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_262)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_262))), inference(resolution, [status(thm)], [c_38, c_338])).
% 7.11/2.63  tff(c_349, plain, (![A_262]: (v1_funct_1(k1_tmap_1(A_262, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_262)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_262)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_262))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_342])).
% 7.11/2.63  tff(c_358, plain, (![A_266]: (v1_funct_1(k1_tmap_1(A_266, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_266)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_266)) | v1_xboole_0(A_266))), inference(negUnitSimplification, [status(thm)], [c_52, c_349])).
% 7.11/2.63  tff(c_361, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_358])).
% 7.11/2.63  tff(c_364, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_361])).
% 7.11/2.63  tff(c_365, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_56, c_364])).
% 7.11/2.63  tff(c_550, plain, (![B_318, C_313, D_314, A_316, E_315, F_317]: (k2_partfun1(k4_subset_1(A_316, C_313, D_314), B_318, k1_tmap_1(A_316, B_318, C_313, D_314, E_315, F_317), D_314)=F_317 | ~m1_subset_1(k1_tmap_1(A_316, B_318, C_313, D_314, E_315, F_317), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_316, C_313, D_314), B_318))) | ~v1_funct_2(k1_tmap_1(A_316, B_318, C_313, D_314, E_315, F_317), k4_subset_1(A_316, C_313, D_314), B_318) | ~v1_funct_1(k1_tmap_1(A_316, B_318, C_313, D_314, E_315, F_317)) | k2_partfun1(D_314, B_318, F_317, k9_subset_1(A_316, C_313, D_314))!=k2_partfun1(C_313, B_318, E_315, k9_subset_1(A_316, C_313, D_314)) | ~m1_subset_1(F_317, k1_zfmisc_1(k2_zfmisc_1(D_314, B_318))) | ~v1_funct_2(F_317, D_314, B_318) | ~v1_funct_1(F_317) | ~m1_subset_1(E_315, k1_zfmisc_1(k2_zfmisc_1(C_313, B_318))) | ~v1_funct_2(E_315, C_313, B_318) | ~v1_funct_1(E_315) | ~m1_subset_1(D_314, k1_zfmisc_1(A_316)) | v1_xboole_0(D_314) | ~m1_subset_1(C_313, k1_zfmisc_1(A_316)) | v1_xboole_0(C_313) | v1_xboole_0(B_318) | v1_xboole_0(A_316))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.11/2.64  tff(c_650, plain, (![C_345, A_342, D_346, F_344, B_343, E_347]: (k2_partfun1(k4_subset_1(A_342, C_345, D_346), B_343, k1_tmap_1(A_342, B_343, C_345, D_346, E_347, F_344), D_346)=F_344 | ~v1_funct_2(k1_tmap_1(A_342, B_343, C_345, D_346, E_347, F_344), k4_subset_1(A_342, C_345, D_346), B_343) | ~v1_funct_1(k1_tmap_1(A_342, B_343, C_345, D_346, E_347, F_344)) | k2_partfun1(D_346, B_343, F_344, k9_subset_1(A_342, C_345, D_346))!=k2_partfun1(C_345, B_343, E_347, k9_subset_1(A_342, C_345, D_346)) | ~m1_subset_1(F_344, k1_zfmisc_1(k2_zfmisc_1(D_346, B_343))) | ~v1_funct_2(F_344, D_346, B_343) | ~v1_funct_1(F_344) | ~m1_subset_1(E_347, k1_zfmisc_1(k2_zfmisc_1(C_345, B_343))) | ~v1_funct_2(E_347, C_345, B_343) | ~v1_funct_1(E_347) | ~m1_subset_1(D_346, k1_zfmisc_1(A_342)) | v1_xboole_0(D_346) | ~m1_subset_1(C_345, k1_zfmisc_1(A_342)) | v1_xboole_0(C_345) | v1_xboole_0(B_343) | v1_xboole_0(A_342))), inference(resolution, [status(thm)], [c_24, c_550])).
% 7.11/2.64  tff(c_675, plain, (![A_353, C_356, D_357, F_355, B_354, E_358]: (k2_partfun1(k4_subset_1(A_353, C_356, D_357), B_354, k1_tmap_1(A_353, B_354, C_356, D_357, E_358, F_355), D_357)=F_355 | ~v1_funct_1(k1_tmap_1(A_353, B_354, C_356, D_357, E_358, F_355)) | k2_partfun1(D_357, B_354, F_355, k9_subset_1(A_353, C_356, D_357))!=k2_partfun1(C_356, B_354, E_358, k9_subset_1(A_353, C_356, D_357)) | ~m1_subset_1(F_355, k1_zfmisc_1(k2_zfmisc_1(D_357, B_354))) | ~v1_funct_2(F_355, D_357, B_354) | ~v1_funct_1(F_355) | ~m1_subset_1(E_358, k1_zfmisc_1(k2_zfmisc_1(C_356, B_354))) | ~v1_funct_2(E_358, C_356, B_354) | ~v1_funct_1(E_358) | ~m1_subset_1(D_357, k1_zfmisc_1(A_353)) | v1_xboole_0(D_357) | ~m1_subset_1(C_356, k1_zfmisc_1(A_353)) | v1_xboole_0(C_356) | v1_xboole_0(B_354) | v1_xboole_0(A_353))), inference(resolution, [status(thm)], [c_26, c_650])).
% 7.11/2.64  tff(c_679, plain, (![A_353, C_356, E_358]: (k2_partfun1(k4_subset_1(A_353, C_356, '#skF_4'), '#skF_2', k1_tmap_1(A_353, '#skF_2', C_356, '#skF_4', E_358, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_353, '#skF_2', C_356, '#skF_4', E_358, '#skF_6')) | k2_partfun1(C_356, '#skF_2', E_358, k9_subset_1(A_353, C_356, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_353, C_356, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_358, k1_zfmisc_1(k2_zfmisc_1(C_356, '#skF_2'))) | ~v1_funct_2(E_358, C_356, '#skF_2') | ~v1_funct_1(E_358) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_353)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_356, k1_zfmisc_1(A_353)) | v1_xboole_0(C_356) | v1_xboole_0('#skF_2') | v1_xboole_0(A_353))), inference(resolution, [status(thm)], [c_32, c_675])).
% 7.11/2.64  tff(c_685, plain, (![A_353, C_356, E_358]: (k2_partfun1(k4_subset_1(A_353, C_356, '#skF_4'), '#skF_2', k1_tmap_1(A_353, '#skF_2', C_356, '#skF_4', E_358, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_353, '#skF_2', C_356, '#skF_4', E_358, '#skF_6')) | k2_partfun1(C_356, '#skF_2', E_358, k9_subset_1(A_353, C_356, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_353, C_356, '#skF_4')) | ~m1_subset_1(E_358, k1_zfmisc_1(k2_zfmisc_1(C_356, '#skF_2'))) | ~v1_funct_2(E_358, C_356, '#skF_2') | ~v1_funct_1(E_358) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_353)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_356, k1_zfmisc_1(A_353)) | v1_xboole_0(C_356) | v1_xboole_0('#skF_2') | v1_xboole_0(A_353))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_276, c_679])).
% 7.11/2.64  tff(c_691, plain, (![A_359, C_360, E_361]: (k2_partfun1(k4_subset_1(A_359, C_360, '#skF_4'), '#skF_2', k1_tmap_1(A_359, '#skF_2', C_360, '#skF_4', E_361, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_359, '#skF_2', C_360, '#skF_4', E_361, '#skF_6')) | k2_partfun1(C_360, '#skF_2', E_361, k9_subset_1(A_359, C_360, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_359, C_360, '#skF_4')) | ~m1_subset_1(E_361, k1_zfmisc_1(k2_zfmisc_1(C_360, '#skF_2'))) | ~v1_funct_2(E_361, C_360, '#skF_2') | ~v1_funct_1(E_361) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_359)) | ~m1_subset_1(C_360, k1_zfmisc_1(A_359)) | v1_xboole_0(C_360) | v1_xboole_0(A_359))), inference(negUnitSimplification, [status(thm)], [c_54, c_48, c_685])).
% 7.11/2.64  tff(c_698, plain, (![A_359]: (k2_partfun1(k4_subset_1(A_359, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_359, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_359, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_359, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_359, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_359)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_359)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_359))), inference(resolution, [status(thm)], [c_38, c_691])).
% 7.11/2.64  tff(c_708, plain, (![A_359]: (k2_partfun1(k4_subset_1(A_359, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_359, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_359, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_359, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_359, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_359)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_359)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_359))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_279, c_698])).
% 7.11/2.64  tff(c_732, plain, (![A_363]: (k2_partfun1(k4_subset_1(A_363, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_363, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_363, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_363, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_363, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_363)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_363)) | v1_xboole_0(A_363))), inference(negUnitSimplification, [status(thm)], [c_52, c_708])).
% 7.11/2.64  tff(c_90, plain, (![A_214, B_215]: (r1_xboole_0(A_214, B_215) | ~r1_subset_1(A_214, B_215) | v1_xboole_0(B_215) | v1_xboole_0(A_214))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.11/2.64  tff(c_183, plain, (![A_233, B_234]: (k3_xboole_0(A_233, B_234)=k1_xboole_0 | ~r1_subset_1(A_233, B_234) | v1_xboole_0(B_234) | v1_xboole_0(A_233))), inference(resolution, [status(thm)], [c_90, c_2])).
% 7.11/2.64  tff(c_189, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_183])).
% 7.11/2.64  tff(c_193, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_52, c_48, c_189])).
% 7.11/2.64  tff(c_117, plain, (![A_221, B_222, C_223, D_224]: (k2_partfun1(A_221, B_222, C_223, D_224)=k7_relat_1(C_223, D_224) | ~m1_subset_1(C_223, k1_zfmisc_1(k2_zfmisc_1(A_221, B_222))) | ~v1_funct_1(C_223))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.11/2.64  tff(c_119, plain, (![D_224]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_224)=k7_relat_1('#skF_6', D_224) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_32, c_117])).
% 7.11/2.64  tff(c_124, plain, (![D_224]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_224)=k7_relat_1('#skF_6', D_224))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_119])).
% 7.11/2.64  tff(c_121, plain, (![D_224]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_224)=k7_relat_1('#skF_5', D_224) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_38, c_117])).
% 7.11/2.64  tff(c_127, plain, (![D_224]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_224)=k7_relat_1('#skF_5', D_224))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_121])).
% 7.11/2.64  tff(c_104, plain, (![A_218, B_219, C_220]: (k9_subset_1(A_218, B_219, C_220)=k3_xboole_0(B_219, C_220) | ~m1_subset_1(C_220, k1_zfmisc_1(A_218)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.11/2.64  tff(c_116, plain, (![B_219]: (k9_subset_1('#skF_1', B_219, '#skF_4')=k3_xboole_0(B_219, '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_104])).
% 7.11/2.64  tff(c_30, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_181])).
% 7.11/2.64  tff(c_81, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_30])).
% 7.11/2.64  tff(c_199, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_193, c_80, c_193, c_124, c_127, c_116, c_116, c_81])).
% 7.11/2.64  tff(c_200, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_30])).
% 7.11/2.64  tff(c_307, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_200])).
% 7.11/2.64  tff(c_743, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_732, c_307])).
% 7.11/2.64  tff(c_757, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_76, c_319, c_80, c_319, c_240, c_240, c_365, c_743])).
% 7.11/2.64  tff(c_759, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_757])).
% 7.11/2.64  tff(c_760, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_200])).
% 7.11/2.64  tff(c_1238, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1229, c_760])).
% 7.11/2.64  tff(c_1249, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_76, c_773, c_80, c_773, c_240, c_240, c_823, c_1238])).
% 7.11/2.64  tff(c_1251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_1249])).
% 7.11/2.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.11/2.64  
% 7.11/2.64  Inference rules
% 7.11/2.64  ----------------------
% 7.11/2.64  #Ref     : 0
% 7.11/2.64  #Sup     : 249
% 7.11/2.64  #Fact    : 0
% 7.11/2.64  #Define  : 0
% 7.11/2.64  #Split   : 2
% 7.11/2.64  #Chain   : 0
% 7.11/2.64  #Close   : 0
% 7.11/2.64  
% 7.11/2.64  Ordering : KBO
% 7.11/2.64  
% 7.11/2.64  Simplification rules
% 7.11/2.64  ----------------------
% 7.11/2.64  #Subsume      : 6
% 7.11/2.64  #Demod        : 182
% 7.11/2.64  #Tautology    : 97
% 7.11/2.64  #SimpNegUnit  : 96
% 7.11/2.64  #BackRed      : 1
% 7.11/2.64  
% 7.11/2.64  #Partial instantiations: 0
% 7.11/2.64  #Strategies tried      : 1
% 7.11/2.64  
% 7.11/2.64  Timing (in seconds)
% 7.11/2.64  ----------------------
% 7.11/2.64  Preprocessing        : 0.69
% 7.11/2.64  Parsing              : 0.34
% 7.11/2.64  CNF conversion       : 0.10
% 7.11/2.64  Main loop            : 1.14
% 7.11/2.64  Inferencing          : 0.44
% 7.11/2.64  Reduction            : 0.34
% 7.11/2.64  Demodulation         : 0.25
% 7.11/2.64  BG Simplification    : 0.06
% 7.11/2.64  Subsumption          : 0.21
% 7.11/2.64  Abstraction          : 0.07
% 7.11/2.64  MUC search           : 0.00
% 7.11/2.64  Cooper               : 0.00
% 7.11/2.64  Total                : 1.91
% 7.11/2.64  Index Insertion      : 0.00
% 7.11/2.64  Index Deletion       : 0.00
% 7.11/2.64  Index Matching       : 0.00
% 7.11/2.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
