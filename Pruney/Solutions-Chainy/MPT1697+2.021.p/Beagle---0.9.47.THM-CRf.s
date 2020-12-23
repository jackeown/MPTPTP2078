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
% DateTime   : Thu Dec  3 10:26:12 EST 2020

% Result     : Theorem 25.02s
% Output     : CNFRefutation 25.45s
% Verified   : 
% Statistics : Number of formulae       :  372 (5148 expanded)
%              Number of leaves         :   50 (1718 expanded)
%              Depth                    :   23
%              Number of atoms          : 1094 (21427 expanded)
%              Number of equality atoms :  294 (4464 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_239,negated_conjecture,(
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

tff(f_197,axiom,(
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

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_50,axiom,(
    ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_115,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_163,axiom,(
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

tff(c_84,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_82,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_80,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_76,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_78,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_74,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_70,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_68,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_66,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_64,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_62,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_60,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_54,plain,(
    ! [F_173,C_170,D_171,A_168,B_169,E_172] :
      ( v1_funct_2(k1_tmap_1(A_168,B_169,C_170,D_171,E_172,F_173),k4_subset_1(A_168,C_170,D_171),B_169)
      | ~ m1_subset_1(F_173,k1_zfmisc_1(k2_zfmisc_1(D_171,B_169)))
      | ~ v1_funct_2(F_173,D_171,B_169)
      | ~ v1_funct_1(F_173)
      | ~ m1_subset_1(E_172,k1_zfmisc_1(k2_zfmisc_1(C_170,B_169)))
      | ~ v1_funct_2(E_172,C_170,B_169)
      | ~ v1_funct_1(E_172)
      | ~ m1_subset_1(D_171,k1_zfmisc_1(A_168))
      | v1_xboole_0(D_171)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(A_168))
      | v1_xboole_0(C_170)
      | v1_xboole_0(B_169)
      | v1_xboole_0(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_114,plain,(
    ! [C_239,A_240,B_241] :
      ( v1_relat_1(C_239)
      | ~ m1_subset_1(C_239,k1_zfmisc_1(k2_zfmisc_1(A_240,B_241))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_121,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_114])).

tff(c_122,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_114])).

tff(c_4911,plain,(
    ! [C_562,A_563,B_564] :
      ( v4_relat_1(C_562,A_563)
      | ~ m1_subset_1(C_562,k1_zfmisc_1(k2_zfmisc_1(A_563,B_564))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_4919,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_4911])).

tff(c_5043,plain,(
    ! [B_585,A_586] :
      ( k1_relat_1(B_585) = A_586
      | ~ v1_partfun1(B_585,A_586)
      | ~ v4_relat_1(B_585,A_586)
      | ~ v1_relat_1(B_585) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_5046,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_4919,c_5043])).

tff(c_5052,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_5046])).

tff(c_5056,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_5052])).

tff(c_5708,plain,(
    ! [C_635,A_636,B_637] :
      ( v1_partfun1(C_635,A_636)
      | ~ v1_funct_2(C_635,A_636,B_637)
      | ~ v1_funct_1(C_635)
      | ~ m1_subset_1(C_635,k1_zfmisc_1(k2_zfmisc_1(A_636,B_637)))
      | v1_xboole_0(B_637) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_5714,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_5708])).

tff(c_5721,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_5714])).

tff(c_5723,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_5056,c_5721])).

tff(c_5724,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5052])).

tff(c_22,plain,(
    ! [B_19,A_18] :
      ( r1_xboole_0(k1_relat_1(B_19),A_18)
      | k9_relat_1(B_19,A_18) != k1_xboole_0
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_5735,plain,(
    ! [A_18] :
      ( r1_xboole_0('#skF_3',A_18)
      | k9_relat_1('#skF_5',A_18) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5724,c_22])).

tff(c_6233,plain,(
    ! [A_671] :
      ( r1_xboole_0('#skF_3',A_671)
      | k9_relat_1('#skF_5',A_671) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_5735])).

tff(c_4918,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_4911])).

tff(c_5049,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_4918,c_5043])).

tff(c_5055,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_5049])).

tff(c_5755,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5055])).

tff(c_6080,plain,(
    ! [C_660,A_661,B_662] :
      ( v1_partfun1(C_660,A_661)
      | ~ v1_funct_2(C_660,A_661,B_662)
      | ~ v1_funct_1(C_660)
      | ~ m1_subset_1(C_660,k1_zfmisc_1(k2_zfmisc_1(A_661,B_662)))
      | v1_xboole_0(B_662) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_6083,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_6080])).

tff(c_6089,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_6083])).

tff(c_6091,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_5755,c_6089])).

tff(c_6092,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5055])).

tff(c_24,plain,(
    ! [A_20,B_22] :
      ( k7_relat_1(A_20,B_22) = k1_xboole_0
      | ~ r1_xboole_0(B_22,k1_relat_1(A_20))
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6097,plain,(
    ! [B_22] :
      ( k7_relat_1('#skF_6',B_22) = k1_xboole_0
      | ~ r1_xboole_0(B_22,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6092,c_24])).

tff(c_6110,plain,(
    ! [B_22] :
      ( k7_relat_1('#skF_6',B_22) = k1_xboole_0
      | ~ r1_xboole_0(B_22,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_6097])).

tff(c_6256,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | k9_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6233,c_6110])).

tff(c_6353,plain,(
    k9_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_6256])).

tff(c_72,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_28,plain,(
    ! [A_23,B_24] :
      ( r1_xboole_0(A_23,B_24)
      | ~ r1_subset_1(A_23,B_24)
      | v1_xboole_0(B_24)
      | v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_20,plain,(
    ! [B_19,A_18] :
      ( k9_relat_1(B_19,A_18) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_19),A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_5738,plain,(
    ! [A_18] :
      ( k9_relat_1('#skF_5',A_18) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_18)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5724,c_20])).

tff(c_6119,plain,(
    ! [A_663] :
      ( k9_relat_1('#skF_5',A_663) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_663) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_5738])).

tff(c_6123,plain,(
    ! [B_24] :
      ( k9_relat_1('#skF_5',B_24) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_24)
      | v1_xboole_0(B_24)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_28,c_6119])).

tff(c_6392,plain,(
    ! [B_689] :
      ( k9_relat_1('#skF_5',B_689) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_689)
      | v1_xboole_0(B_689) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_6123])).

tff(c_6395,plain,
    ( k9_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_6392])).

tff(c_6399,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_6353,c_6395])).

tff(c_6400,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_6256])).

tff(c_18,plain,(
    ! [B_17,A_16] :
      ( k2_relat_1(k7_relat_1(B_17,A_16)) = k9_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6411,plain,
    ( k9_relat_1('#skF_6','#skF_3') = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_6400,c_18])).

tff(c_6421,plain,(
    k9_relat_1('#skF_6','#skF_3') = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_6411])).

tff(c_6103,plain,(
    ! [A_18] :
      ( r1_xboole_0('#skF_4',A_18)
      | k9_relat_1('#skF_6',A_18) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6092,c_22])).

tff(c_6132,plain,(
    ! [A_664] :
      ( r1_xboole_0('#skF_4',A_664)
      | k9_relat_1('#skF_6',A_664) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_6103])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6147,plain,(
    ! [A_664] :
      ( k3_xboole_0('#skF_4',A_664) = k1_xboole_0
      | k9_relat_1('#skF_6',A_664) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6132,c_2])).

tff(c_6447,plain,
    ( k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0
    | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6421,c_6147])).

tff(c_6563,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_6447])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6106,plain,(
    ! [A_18] :
      ( k9_relat_1('#skF_6',A_18) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_18)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6092,c_20])).

tff(c_6171,plain,(
    ! [A_666] :
      ( k9_relat_1('#skF_6',A_666) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_666) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_6106])).

tff(c_6621,plain,(
    ! [B_705] :
      ( k9_relat_1('#skF_6',B_705) = k1_xboole_0
      | k3_xboole_0('#skF_4',B_705) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_6171])).

tff(c_6401,plain,(
    k9_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_6256])).

tff(c_6262,plain,(
    ! [A_671] :
      ( k3_xboole_0('#skF_3',A_671) = k1_xboole_0
      | k9_relat_1('#skF_5',A_671) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6233,c_2])).

tff(c_6436,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6401,c_6262])).

tff(c_16,plain,(
    ! [A_15] : k7_relat_1(k1_xboole_0,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    ! [C_14,A_12,B_13] :
      ( k7_relat_1(k7_relat_1(C_14,A_12),B_13) = k7_relat_1(C_14,k3_xboole_0(A_12,B_13))
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6408,plain,(
    ! [B_13] :
      ( k7_relat_1('#skF_6',k3_xboole_0('#skF_3',B_13)) = k7_relat_1(k1_xboole_0,B_13)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6400,c_14])).

tff(c_6451,plain,(
    ! [B_690] : k7_relat_1('#skF_6',k3_xboole_0('#skF_3',B_690)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_16,c_6408])).

tff(c_6466,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6436,c_6451])).

tff(c_6505,plain,
    ( k9_relat_1('#skF_6',k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_6466,c_18])).

tff(c_6515,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_6505])).

tff(c_6636,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | k3_xboole_0('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6621,c_6515])).

tff(c_6663,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6636])).

tff(c_6665,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6563,c_6663])).

tff(c_6667,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_6447])).

tff(c_6462,plain,(
    ! [B_690] :
      ( k9_relat_1('#skF_6',k3_xboole_0('#skF_3',B_690)) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6451,c_18])).

tff(c_6478,plain,(
    ! [B_690] : k9_relat_1('#skF_6',k3_xboole_0('#skF_3',B_690)) = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_6462])).

tff(c_6710,plain,(
    ! [B_712] : k9_relat_1('#skF_6',k3_xboole_0('#skF_3',B_712)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6667,c_6478])).

tff(c_6724,plain,(
    ! [B_712] : k3_xboole_0('#skF_4',k3_xboole_0('#skF_3',B_712)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6710,c_6147])).

tff(c_6669,plain,(
    k9_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6667,c_6421])).

tff(c_6114,plain,(
    ! [A_18] :
      ( r1_xboole_0('#skF_4',A_18)
      | k9_relat_1('#skF_6',A_18) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_6103])).

tff(c_5729,plain,(
    ! [B_22] :
      ( k7_relat_1('#skF_5',B_22) = k1_xboole_0
      | ~ r1_xboole_0(B_22,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5724,c_24])).

tff(c_6188,plain,(
    ! [B_667] :
      ( k7_relat_1('#skF_5',B_667) = k1_xboole_0
      | ~ r1_xboole_0(B_667,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_5729])).

tff(c_6205,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | k9_relat_1('#skF_6','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6114,c_6188])).

tff(c_6782,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6669,c_6205])).

tff(c_6789,plain,(
    ! [B_13] :
      ( k7_relat_1('#skF_5',k3_xboole_0('#skF_4',B_13)) = k7_relat_1(k1_xboole_0,B_13)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6782,c_14])).

tff(c_6809,plain,(
    ! [B_717] : k7_relat_1('#skF_5',k3_xboole_0('#skF_4',B_717)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_16,c_6789])).

tff(c_6826,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6724,c_6809])).

tff(c_6419,plain,(
    ! [B_13] : k7_relat_1('#skF_6',k3_xboole_0('#skF_3',B_13)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_16,c_6408])).

tff(c_4993,plain,(
    ! [A_578,B_579,C_580] :
      ( k9_subset_1(A_578,B_579,C_580) = k3_xboole_0(B_579,C_580)
      | ~ m1_subset_1(C_580,k1_zfmisc_1(A_578)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_5004,plain,(
    ! [B_579] : k9_subset_1('#skF_1',B_579,'#skF_4') = k3_xboole_0(B_579,'#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_4993])).

tff(c_6696,plain,(
    ! [F_708,E_706,A_711,C_707,B_710,D_709] :
      ( v1_funct_1(k1_tmap_1(A_711,B_710,C_707,D_709,E_706,F_708))
      | ~ m1_subset_1(F_708,k1_zfmisc_1(k2_zfmisc_1(D_709,B_710)))
      | ~ v1_funct_2(F_708,D_709,B_710)
      | ~ v1_funct_1(F_708)
      | ~ m1_subset_1(E_706,k1_zfmisc_1(k2_zfmisc_1(C_707,B_710)))
      | ~ v1_funct_2(E_706,C_707,B_710)
      | ~ v1_funct_1(E_706)
      | ~ m1_subset_1(D_709,k1_zfmisc_1(A_711))
      | v1_xboole_0(D_709)
      | ~ m1_subset_1(C_707,k1_zfmisc_1(A_711))
      | v1_xboole_0(C_707)
      | v1_xboole_0(B_710)
      | v1_xboole_0(A_711) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_6698,plain,(
    ! [A_711,C_707,E_706] :
      ( v1_funct_1(k1_tmap_1(A_711,'#skF_2',C_707,'#skF_4',E_706,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_706,k1_zfmisc_1(k2_zfmisc_1(C_707,'#skF_2')))
      | ~ v1_funct_2(E_706,C_707,'#skF_2')
      | ~ v1_funct_1(E_706)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_711))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_707,k1_zfmisc_1(A_711))
      | v1_xboole_0(C_707)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_711) ) ),
    inference(resolution,[status(thm)],[c_60,c_6696])).

tff(c_6703,plain,(
    ! [A_711,C_707,E_706] :
      ( v1_funct_1(k1_tmap_1(A_711,'#skF_2',C_707,'#skF_4',E_706,'#skF_6'))
      | ~ m1_subset_1(E_706,k1_zfmisc_1(k2_zfmisc_1(C_707,'#skF_2')))
      | ~ v1_funct_2(E_706,C_707,'#skF_2')
      | ~ v1_funct_1(E_706)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_711))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_707,k1_zfmisc_1(A_711))
      | v1_xboole_0(C_707)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_711) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_6698])).

tff(c_9025,plain,(
    ! [A_823,C_824,E_825] :
      ( v1_funct_1(k1_tmap_1(A_823,'#skF_2',C_824,'#skF_4',E_825,'#skF_6'))
      | ~ m1_subset_1(E_825,k1_zfmisc_1(k2_zfmisc_1(C_824,'#skF_2')))
      | ~ v1_funct_2(E_825,C_824,'#skF_2')
      | ~ v1_funct_1(E_825)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_823))
      | ~ m1_subset_1(C_824,k1_zfmisc_1(A_823))
      | v1_xboole_0(C_824)
      | v1_xboole_0(A_823) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_6703])).

tff(c_9032,plain,(
    ! [A_823] :
      ( v1_funct_1(k1_tmap_1(A_823,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_823))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_823))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_823) ) ),
    inference(resolution,[status(thm)],[c_66,c_9025])).

tff(c_9042,plain,(
    ! [A_823] :
      ( v1_funct_1(k1_tmap_1(A_823,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_823))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_823))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_823) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_9032])).

tff(c_9709,plain,(
    ! [A_857] :
      ( v1_funct_1(k1_tmap_1(A_857,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_857))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_857))
      | v1_xboole_0(A_857) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_9042])).

tff(c_9712,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_78,c_9709])).

tff(c_9715,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_9712])).

tff(c_9716,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_9715])).

tff(c_6321,plain,(
    ! [A_677,B_678,C_679,D_680] :
      ( k2_partfun1(A_677,B_678,C_679,D_680) = k7_relat_1(C_679,D_680)
      | ~ m1_subset_1(C_679,k1_zfmisc_1(k2_zfmisc_1(A_677,B_678)))
      | ~ v1_funct_1(C_679) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_6325,plain,(
    ! [D_680] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_680) = k7_relat_1('#skF_5',D_680)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_66,c_6321])).

tff(c_6331,plain,(
    ! [D_680] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_680) = k7_relat_1('#skF_5',D_680) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_6325])).

tff(c_6323,plain,(
    ! [D_680] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_680) = k7_relat_1('#skF_6',D_680)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_60,c_6321])).

tff(c_6328,plain,(
    ! [D_680] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_680) = k7_relat_1('#skF_6',D_680) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_6323])).

tff(c_52,plain,(
    ! [F_173,C_170,D_171,A_168,B_169,E_172] :
      ( m1_subset_1(k1_tmap_1(A_168,B_169,C_170,D_171,E_172,F_173),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_168,C_170,D_171),B_169)))
      | ~ m1_subset_1(F_173,k1_zfmisc_1(k2_zfmisc_1(D_171,B_169)))
      | ~ v1_funct_2(F_173,D_171,B_169)
      | ~ v1_funct_1(F_173)
      | ~ m1_subset_1(E_172,k1_zfmisc_1(k2_zfmisc_1(C_170,B_169)))
      | ~ v1_funct_2(E_172,C_170,B_169)
      | ~ v1_funct_1(E_172)
      | ~ m1_subset_1(D_171,k1_zfmisc_1(A_168))
      | v1_xboole_0(D_171)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(A_168))
      | v1_xboole_0(C_170)
      | v1_xboole_0(B_169)
      | v1_xboole_0(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_7305,plain,(
    ! [E_750,C_748,B_749,A_746,F_751,D_747] :
      ( k2_partfun1(k4_subset_1(A_746,C_748,D_747),B_749,k1_tmap_1(A_746,B_749,C_748,D_747,E_750,F_751),D_747) = F_751
      | ~ m1_subset_1(k1_tmap_1(A_746,B_749,C_748,D_747,E_750,F_751),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_746,C_748,D_747),B_749)))
      | ~ v1_funct_2(k1_tmap_1(A_746,B_749,C_748,D_747,E_750,F_751),k4_subset_1(A_746,C_748,D_747),B_749)
      | ~ v1_funct_1(k1_tmap_1(A_746,B_749,C_748,D_747,E_750,F_751))
      | k2_partfun1(D_747,B_749,F_751,k9_subset_1(A_746,C_748,D_747)) != k2_partfun1(C_748,B_749,E_750,k9_subset_1(A_746,C_748,D_747))
      | ~ m1_subset_1(F_751,k1_zfmisc_1(k2_zfmisc_1(D_747,B_749)))
      | ~ v1_funct_2(F_751,D_747,B_749)
      | ~ v1_funct_1(F_751)
      | ~ m1_subset_1(E_750,k1_zfmisc_1(k2_zfmisc_1(C_748,B_749)))
      | ~ v1_funct_2(E_750,C_748,B_749)
      | ~ v1_funct_1(E_750)
      | ~ m1_subset_1(D_747,k1_zfmisc_1(A_746))
      | v1_xboole_0(D_747)
      | ~ m1_subset_1(C_748,k1_zfmisc_1(A_746))
      | v1_xboole_0(C_748)
      | v1_xboole_0(B_749)
      | v1_xboole_0(A_746) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_18341,plain,(
    ! [F_1148,B_1150,E_1146,A_1151,C_1147,D_1149] :
      ( k2_partfun1(k4_subset_1(A_1151,C_1147,D_1149),B_1150,k1_tmap_1(A_1151,B_1150,C_1147,D_1149,E_1146,F_1148),D_1149) = F_1148
      | ~ v1_funct_2(k1_tmap_1(A_1151,B_1150,C_1147,D_1149,E_1146,F_1148),k4_subset_1(A_1151,C_1147,D_1149),B_1150)
      | ~ v1_funct_1(k1_tmap_1(A_1151,B_1150,C_1147,D_1149,E_1146,F_1148))
      | k2_partfun1(D_1149,B_1150,F_1148,k9_subset_1(A_1151,C_1147,D_1149)) != k2_partfun1(C_1147,B_1150,E_1146,k9_subset_1(A_1151,C_1147,D_1149))
      | ~ m1_subset_1(F_1148,k1_zfmisc_1(k2_zfmisc_1(D_1149,B_1150)))
      | ~ v1_funct_2(F_1148,D_1149,B_1150)
      | ~ v1_funct_1(F_1148)
      | ~ m1_subset_1(E_1146,k1_zfmisc_1(k2_zfmisc_1(C_1147,B_1150)))
      | ~ v1_funct_2(E_1146,C_1147,B_1150)
      | ~ v1_funct_1(E_1146)
      | ~ m1_subset_1(D_1149,k1_zfmisc_1(A_1151))
      | v1_xboole_0(D_1149)
      | ~ m1_subset_1(C_1147,k1_zfmisc_1(A_1151))
      | v1_xboole_0(C_1147)
      | v1_xboole_0(B_1150)
      | v1_xboole_0(A_1151) ) ),
    inference(resolution,[status(thm)],[c_52,c_7305])).

tff(c_40591,plain,(
    ! [B_1555,F_1553,C_1552,E_1551,A_1556,D_1554] :
      ( k2_partfun1(k4_subset_1(A_1556,C_1552,D_1554),B_1555,k1_tmap_1(A_1556,B_1555,C_1552,D_1554,E_1551,F_1553),D_1554) = F_1553
      | ~ v1_funct_1(k1_tmap_1(A_1556,B_1555,C_1552,D_1554,E_1551,F_1553))
      | k2_partfun1(D_1554,B_1555,F_1553,k9_subset_1(A_1556,C_1552,D_1554)) != k2_partfun1(C_1552,B_1555,E_1551,k9_subset_1(A_1556,C_1552,D_1554))
      | ~ m1_subset_1(F_1553,k1_zfmisc_1(k2_zfmisc_1(D_1554,B_1555)))
      | ~ v1_funct_2(F_1553,D_1554,B_1555)
      | ~ v1_funct_1(F_1553)
      | ~ m1_subset_1(E_1551,k1_zfmisc_1(k2_zfmisc_1(C_1552,B_1555)))
      | ~ v1_funct_2(E_1551,C_1552,B_1555)
      | ~ v1_funct_1(E_1551)
      | ~ m1_subset_1(D_1554,k1_zfmisc_1(A_1556))
      | v1_xboole_0(D_1554)
      | ~ m1_subset_1(C_1552,k1_zfmisc_1(A_1556))
      | v1_xboole_0(C_1552)
      | v1_xboole_0(B_1555)
      | v1_xboole_0(A_1556) ) ),
    inference(resolution,[status(thm)],[c_54,c_18341])).

tff(c_40595,plain,(
    ! [A_1556,C_1552,E_1551] :
      ( k2_partfun1(k4_subset_1(A_1556,C_1552,'#skF_4'),'#skF_2',k1_tmap_1(A_1556,'#skF_2',C_1552,'#skF_4',E_1551,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1556,'#skF_2',C_1552,'#skF_4',E_1551,'#skF_6'))
      | k2_partfun1(C_1552,'#skF_2',E_1551,k9_subset_1(A_1556,C_1552,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_1556,C_1552,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1551,k1_zfmisc_1(k2_zfmisc_1(C_1552,'#skF_2')))
      | ~ v1_funct_2(E_1551,C_1552,'#skF_2')
      | ~ v1_funct_1(E_1551)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1556))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1552,k1_zfmisc_1(A_1556))
      | v1_xboole_0(C_1552)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1556) ) ),
    inference(resolution,[status(thm)],[c_60,c_40591])).

tff(c_40601,plain,(
    ! [A_1556,C_1552,E_1551] :
      ( k2_partfun1(k4_subset_1(A_1556,C_1552,'#skF_4'),'#skF_2',k1_tmap_1(A_1556,'#skF_2',C_1552,'#skF_4',E_1551,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1556,'#skF_2',C_1552,'#skF_4',E_1551,'#skF_6'))
      | k2_partfun1(C_1552,'#skF_2',E_1551,k9_subset_1(A_1556,C_1552,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1556,C_1552,'#skF_4'))
      | ~ m1_subset_1(E_1551,k1_zfmisc_1(k2_zfmisc_1(C_1552,'#skF_2')))
      | ~ v1_funct_2(E_1551,C_1552,'#skF_2')
      | ~ v1_funct_1(E_1551)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1556))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1552,k1_zfmisc_1(A_1556))
      | v1_xboole_0(C_1552)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1556) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_6328,c_40595])).

tff(c_41468,plain,(
    ! [A_1578,C_1579,E_1580] :
      ( k2_partfun1(k4_subset_1(A_1578,C_1579,'#skF_4'),'#skF_2',k1_tmap_1(A_1578,'#skF_2',C_1579,'#skF_4',E_1580,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1578,'#skF_2',C_1579,'#skF_4',E_1580,'#skF_6'))
      | k2_partfun1(C_1579,'#skF_2',E_1580,k9_subset_1(A_1578,C_1579,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1578,C_1579,'#skF_4'))
      | ~ m1_subset_1(E_1580,k1_zfmisc_1(k2_zfmisc_1(C_1579,'#skF_2')))
      | ~ v1_funct_2(E_1580,C_1579,'#skF_2')
      | ~ v1_funct_1(E_1580)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1578))
      | ~ m1_subset_1(C_1579,k1_zfmisc_1(A_1578))
      | v1_xboole_0(C_1579)
      | v1_xboole_0(A_1578) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_40601])).

tff(c_41475,plain,(
    ! [A_1578] :
      ( k2_partfun1(k4_subset_1(A_1578,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1578,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1578,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1578,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1578,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1578))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1578))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1578) ) ),
    inference(resolution,[status(thm)],[c_66,c_41468])).

tff(c_41485,plain,(
    ! [A_1578] :
      ( k2_partfun1(k4_subset_1(A_1578,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1578,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1578,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1578,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1578,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1578))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1578))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1578) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_6331,c_41475])).

tff(c_45115,plain,(
    ! [A_1679] :
      ( k2_partfun1(k4_subset_1(A_1679,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1679,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1679,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1679,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1679,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1679))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1679))
      | v1_xboole_0(A_1679) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_41485])).

tff(c_167,plain,(
    ! [C_249,A_250,B_251] :
      ( v4_relat_1(C_249,A_250)
      | ~ m1_subset_1(C_249,k1_zfmisc_1(k2_zfmisc_1(A_250,B_251))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_175,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_167])).

tff(c_231,plain,(
    ! [B_263,A_264] :
      ( k1_relat_1(B_263) = A_264
      | ~ v1_partfun1(B_263,A_264)
      | ~ v4_relat_1(B_263,A_264)
      | ~ v1_relat_1(B_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_234,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_175,c_231])).

tff(c_240,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_234])).

tff(c_244,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_240])).

tff(c_710,plain,(
    ! [C_317,A_318,B_319] :
      ( v1_partfun1(C_317,A_318)
      | ~ v1_funct_2(C_317,A_318,B_319)
      | ~ v1_funct_1(C_317)
      | ~ m1_subset_1(C_317,k1_zfmisc_1(k2_zfmisc_1(A_318,B_319)))
      | v1_xboole_0(B_319) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_716,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_710])).

tff(c_723,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_716])).

tff(c_725,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_244,c_723])).

tff(c_726,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_240])).

tff(c_740,plain,(
    ! [A_18] :
      ( r1_xboole_0('#skF_3',A_18)
      | k9_relat_1('#skF_5',A_18) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_726,c_22])).

tff(c_750,plain,(
    ! [A_18] :
      ( r1_xboole_0('#skF_3',A_18)
      | k9_relat_1('#skF_5',A_18) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_740])).

tff(c_174,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_167])).

tff(c_237,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_174,c_231])).

tff(c_243,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_237])).

tff(c_753,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_243])).

tff(c_1075,plain,(
    ! [C_352,A_353,B_354] :
      ( v1_partfun1(C_352,A_353)
      | ~ v1_funct_2(C_352,A_353,B_354)
      | ~ v1_funct_1(C_352)
      | ~ m1_subset_1(C_352,k1_zfmisc_1(k2_zfmisc_1(A_353,B_354)))
      | v1_xboole_0(B_354) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1078,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_1075])).

tff(c_1084,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_1078])).

tff(c_1086,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_753,c_1084])).

tff(c_1087,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_243])).

tff(c_1092,plain,(
    ! [B_22] :
      ( k7_relat_1('#skF_6',B_22) = k1_xboole_0
      | ~ r1_xboole_0(B_22,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1087,c_24])).

tff(c_1143,plain,(
    ! [B_357] :
      ( k7_relat_1('#skF_6',B_357) = k1_xboole_0
      | ~ r1_xboole_0(B_357,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_1092])).

tff(c_1160,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | k9_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_750,c_1143])).

tff(c_1346,plain,(
    k9_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1160])).

tff(c_737,plain,(
    ! [A_18] :
      ( k9_relat_1('#skF_5',A_18) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_18)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_726,c_20])).

tff(c_1219,plain,(
    ! [A_360] :
      ( k9_relat_1('#skF_5',A_360) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_360) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_737])).

tff(c_1226,plain,(
    ! [B_24] :
      ( k9_relat_1('#skF_5',B_24) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_24)
      | v1_xboole_0(B_24)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_28,c_1219])).

tff(c_1418,plain,(
    ! [B_383] :
      ( k9_relat_1('#skF_5',B_383) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_383)
      | v1_xboole_0(B_383) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1226])).

tff(c_1421,plain,
    ( k9_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_1418])).

tff(c_1425,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1346,c_1421])).

tff(c_1427,plain,(
    k9_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1160])).

tff(c_1114,plain,(
    ! [A_355] :
      ( r1_xboole_0('#skF_3',A_355)
      | k9_relat_1('#skF_5',A_355) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_740])).

tff(c_1129,plain,(
    ! [A_355] :
      ( k3_xboole_0('#skF_3',A_355) = k1_xboole_0
      | k9_relat_1('#skF_5',A_355) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1114,c_2])).

tff(c_1463,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1427,c_1129])).

tff(c_1426,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1160])).

tff(c_1431,plain,(
    ! [B_13] :
      ( k7_relat_1('#skF_6',k3_xboole_0('#skF_3',B_13)) = k7_relat_1(k1_xboole_0,B_13)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1426,c_14])).

tff(c_1480,plain,(
    ! [B_384] : k7_relat_1('#skF_6',k3_xboole_0('#skF_3',B_384)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_16,c_1431])).

tff(c_1495,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1463,c_1480])).

tff(c_1530,plain,
    ( k9_relat_1('#skF_6',k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1495,c_18])).

tff(c_1540,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_1530])).

tff(c_1098,plain,(
    ! [A_18] :
      ( k9_relat_1('#skF_6',A_18) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_18)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1087,c_20])).

tff(c_1130,plain,(
    ! [A_356] :
      ( k9_relat_1('#skF_6',A_356) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_356) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_1098])).

tff(c_1142,plain,(
    ! [B_2] :
      ( k9_relat_1('#skF_6',B_2) = k1_xboole_0
      | k3_xboole_0('#skF_4',B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_1130])).

tff(c_1547,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | k3_xboole_0('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1540,c_1142])).

tff(c_1554,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1547])).

tff(c_1524,plain,(
    ! [B_13] :
      ( k7_relat_1('#skF_6',k3_xboole_0(k1_xboole_0,B_13)) = k7_relat_1(k1_xboole_0,B_13)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1495,c_14])).

tff(c_1602,plain,(
    ! [B_390] : k7_relat_1('#skF_6',k3_xboole_0(k1_xboole_0,B_390)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_16,c_1524])).

tff(c_1613,plain,(
    ! [B_390] :
      ( k9_relat_1('#skF_6',k3_xboole_0(k1_xboole_0,B_390)) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1602,c_18])).

tff(c_1627,plain,(
    ! [B_390] : k9_relat_1('#skF_6',k3_xboole_0(k1_xboole_0,B_390)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_1554,c_1613])).

tff(c_1101,plain,(
    ! [A_18] :
      ( r1_xboole_0('#skF_4',A_18)
      | k9_relat_1('#skF_6',A_18) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1087,c_22])).

tff(c_1166,plain,(
    ! [A_358] :
      ( r1_xboole_0('#skF_4',A_358)
      | k9_relat_1('#skF_6',A_358) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_1101])).

tff(c_1709,plain,(
    ! [A_399] :
      ( k3_xboole_0('#skF_4',A_399) = k1_xboole_0
      | k9_relat_1('#skF_6',A_399) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1166,c_2])).

tff(c_1726,plain,(
    ! [B_390] : k3_xboole_0('#skF_4',k3_xboole_0(k1_xboole_0,B_390)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1627,c_1709])).

tff(c_1437,plain,
    ( k9_relat_1('#skF_6','#skF_3') = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1426,c_18])).

tff(c_1447,plain,(
    k9_relat_1('#skF_6','#skF_3') = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_1437])).

tff(c_1568,plain,(
    k9_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1554,c_1447])).

tff(c_1111,plain,(
    ! [A_18] :
      ( r1_xboole_0('#skF_4',A_18)
      | k9_relat_1('#skF_6',A_18) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_1101])).

tff(c_731,plain,(
    ! [B_22] :
      ( k7_relat_1('#skF_5',B_22) = k1_xboole_0
      | ~ r1_xboole_0(B_22,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_726,c_24])).

tff(c_1191,plain,(
    ! [B_359] :
      ( k7_relat_1('#skF_5',B_359) = k1_xboole_0
      | ~ r1_xboole_0(B_359,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_731])).

tff(c_1212,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | k9_relat_1('#skF_6','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1111,c_1191])).

tff(c_1774,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1568,c_1212])).

tff(c_1778,plain,(
    ! [B_13] :
      ( k7_relat_1('#skF_5',k3_xboole_0('#skF_4',B_13)) = k7_relat_1(k1_xboole_0,B_13)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1774,c_14])).

tff(c_1798,plain,(
    ! [B_409] : k7_relat_1('#skF_5',k3_xboole_0('#skF_4',B_409)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_16,c_1778])).

tff(c_1810,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1726,c_1798])).

tff(c_1510,plain,(
    ! [A_385,B_386,C_387,D_388] :
      ( k2_partfun1(A_385,B_386,C_387,D_388) = k7_relat_1(C_387,D_388)
      | ~ m1_subset_1(C_387,k1_zfmisc_1(k2_zfmisc_1(A_385,B_386)))
      | ~ v1_funct_1(C_387) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1514,plain,(
    ! [D_388] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_388) = k7_relat_1('#skF_5',D_388)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_66,c_1510])).

tff(c_1520,plain,(
    ! [D_388] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_388) = k7_relat_1('#skF_5',D_388) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1514])).

tff(c_1512,plain,(
    ! [D_388] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_388) = k7_relat_1('#skF_6',D_388)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_60,c_1510])).

tff(c_1517,plain,(
    ! [D_388] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_388) = k7_relat_1('#skF_6',D_388) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1512])).

tff(c_1236,plain,(
    ! [A_361,B_362,C_363] :
      ( k9_subset_1(A_361,B_362,C_363) = k3_xboole_0(B_362,C_363)
      | ~ m1_subset_1(C_363,k1_zfmisc_1(A_361)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1247,plain,(
    ! [B_362] : k9_subset_1('#skF_1',B_362,'#skF_4') = k3_xboole_0(B_362,'#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_1236])).

tff(c_58,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_123,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_1249,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1247,c_1247,c_123])).

tff(c_4878,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1810,c_1520,c_1495,c_1517,c_1463,c_1463,c_1249])).

tff(c_4879,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_4992,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_4879])).

tff(c_45126,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_45115,c_4992])).

tff(c_45140,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_6826,c_6419,c_5004,c_6436,c_5004,c_9716,c_45126])).

tff(c_45142,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_45140])).

tff(c_45143,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_4879])).

tff(c_45195,plain,(
    ! [B_1687,A_1688] :
      ( k1_relat_1(B_1687) = A_1688
      | ~ v1_partfun1(B_1687,A_1688)
      | ~ v4_relat_1(B_1687,A_1688)
      | ~ v1_relat_1(B_1687) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_45198,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_4919,c_45195])).

tff(c_45204,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_45198])).

tff(c_45208,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_45204])).

tff(c_46025,plain,(
    ! [C_1751,A_1752,B_1753] :
      ( v1_partfun1(C_1751,A_1752)
      | ~ v1_funct_2(C_1751,A_1752,B_1753)
      | ~ v1_funct_1(C_1751)
      | ~ m1_subset_1(C_1751,k1_zfmisc_1(k2_zfmisc_1(A_1752,B_1753)))
      | v1_xboole_0(B_1753) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_46031,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_46025])).

tff(c_46038,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_46031])).

tff(c_46040,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_45208,c_46038])).

tff(c_46041,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_45204])).

tff(c_46052,plain,(
    ! [A_18] :
      ( r1_xboole_0('#skF_3',A_18)
      | k9_relat_1('#skF_5',A_18) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46041,c_22])).

tff(c_46624,plain,(
    ! [A_1795] :
      ( r1_xboole_0('#skF_3',A_1795)
      | k9_relat_1('#skF_5',A_1795) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_46052])).

tff(c_45201,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_4918,c_45195])).

tff(c_45207,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_45201])).

tff(c_46072,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_45207])).

tff(c_46512,plain,(
    ! [C_1788,A_1789,B_1790] :
      ( v1_partfun1(C_1788,A_1789)
      | ~ v1_funct_2(C_1788,A_1789,B_1790)
      | ~ v1_funct_1(C_1788)
      | ~ m1_subset_1(C_1788,k1_zfmisc_1(k2_zfmisc_1(A_1789,B_1790)))
      | v1_xboole_0(B_1790) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_46515,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_46512])).

tff(c_46521,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_46515])).

tff(c_46523,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_46072,c_46521])).

tff(c_46524,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_45207])).

tff(c_46529,plain,(
    ! [B_22] :
      ( k7_relat_1('#skF_6',B_22) = k1_xboole_0
      | ~ r1_xboole_0(B_22,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46524,c_24])).

tff(c_46542,plain,(
    ! [B_22] :
      ( k7_relat_1('#skF_6',B_22) = k1_xboole_0
      | ~ r1_xboole_0(B_22,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_46529])).

tff(c_46642,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | k9_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46624,c_46542])).

tff(c_46700,plain,(
    k9_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_46642])).

tff(c_46055,plain,(
    ! [A_18] :
      ( k9_relat_1('#skF_5',A_18) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_18)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46041,c_20])).

tff(c_46588,plain,(
    ! [A_1793] :
      ( k9_relat_1('#skF_5',A_1793) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_1793) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_46055])).

tff(c_46592,plain,(
    ! [B_24] :
      ( k9_relat_1('#skF_5',B_24) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_24)
      | v1_xboole_0(B_24)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_28,c_46588])).

tff(c_46907,plain,(
    ! [B_1815] :
      ( k9_relat_1('#skF_5',B_1815) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_1815)
      | v1_xboole_0(B_1815) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_46592])).

tff(c_46910,plain,
    ( k9_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_46907])).

tff(c_46914,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_46700,c_46910])).

tff(c_46915,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_46642])).

tff(c_46920,plain,(
    ! [B_13] :
      ( k7_relat_1('#skF_6',k3_xboole_0('#skF_3',B_13)) = k7_relat_1(k1_xboole_0,B_13)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46915,c_14])).

tff(c_46927,plain,(
    ! [B_13] : k7_relat_1('#skF_6',k3_xboole_0('#skF_3',B_13)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_16,c_46920])).

tff(c_45145,plain,(
    ! [A_1680,B_1681,C_1682] :
      ( k9_subset_1(A_1680,B_1681,C_1682) = k3_xboole_0(B_1681,C_1682)
      | ~ m1_subset_1(C_1682,k1_zfmisc_1(A_1680)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_45156,plain,(
    ! [B_1681] : k9_subset_1('#skF_1',B_1681,'#skF_4') = k3_xboole_0(B_1681,'#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_45145])).

tff(c_46923,plain,
    ( k9_relat_1('#skF_6','#skF_3') = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_46915,c_18])).

tff(c_46929,plain,(
    k9_relat_1('#skF_6','#skF_3') = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_46923])).

tff(c_46535,plain,(
    ! [A_18] :
      ( r1_xboole_0('#skF_4',A_18)
      | k9_relat_1('#skF_6',A_18) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46524,c_22])).

tff(c_46555,plain,(
    ! [A_1791] :
      ( r1_xboole_0('#skF_4',A_1791)
      | k9_relat_1('#skF_6',A_1791) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_46535])).

tff(c_47042,plain,(
    ! [A_1821] :
      ( k3_xboole_0('#skF_4',A_1821) = k1_xboole_0
      | k9_relat_1('#skF_6',A_1821) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_46555,c_2])).

tff(c_47054,plain,
    ( k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0
    | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_46929,c_47042])).

tff(c_47056,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_47054])).

tff(c_46538,plain,(
    ! [A_18] :
      ( k9_relat_1('#skF_6',A_18) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_18)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46524,c_20])).

tff(c_46571,plain,(
    ! [A_1792] :
      ( k9_relat_1('#skF_6',A_1792) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_1792) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_46538])).

tff(c_47185,plain,(
    ! [B_1834] :
      ( k9_relat_1('#skF_6',B_1834) = k1_xboole_0
      | k3_xboole_0('#skF_4',B_1834) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_46571])).

tff(c_46916,plain,(
    k9_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_46642])).

tff(c_46648,plain,(
    ! [A_1795] :
      ( k3_xboole_0('#skF_3',A_1795) = k1_xboole_0
      | k9_relat_1('#skF_5',A_1795) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_46624,c_2])).

tff(c_46937,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_46916,c_46648])).

tff(c_46948,plain,(
    ! [B_1816] : k7_relat_1('#skF_6',k3_xboole_0('#skF_3',B_1816)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_16,c_46920])).

tff(c_46960,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_46937,c_46948])).

tff(c_46976,plain,
    ( k9_relat_1('#skF_6',k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_46960,c_18])).

tff(c_46982,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_46976])).

tff(c_47203,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | k3_xboole_0('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_47185,c_46982])).

tff(c_47228,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_47203])).

tff(c_47230,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47056,c_47228])).

tff(c_47232,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_47054])).

tff(c_46956,plain,(
    ! [B_1816] :
      ( k9_relat_1('#skF_6',k3_xboole_0('#skF_3',B_1816)) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46948,c_18])).

tff(c_46968,plain,(
    ! [B_1816] : k9_relat_1('#skF_6',k3_xboole_0('#skF_3',B_1816)) = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_46956])).

tff(c_47270,plain,(
    ! [B_1836] : k9_relat_1('#skF_6',k3_xboole_0('#skF_3',B_1836)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_47232,c_46968])).

tff(c_46570,plain,(
    ! [A_1791] :
      ( k3_xboole_0('#skF_4',A_1791) = k1_xboole_0
      | k9_relat_1('#skF_6',A_1791) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_46555,c_2])).

tff(c_47284,plain,(
    ! [B_1836] : k3_xboole_0('#skF_4',k3_xboole_0('#skF_3',B_1836)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_47270,c_46570])).

tff(c_47243,plain,(
    k9_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_47232,c_46929])).

tff(c_46546,plain,(
    ! [A_18] :
      ( r1_xboole_0('#skF_4',A_18)
      | k9_relat_1('#skF_6',A_18) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_46535])).

tff(c_46046,plain,(
    ! [B_22] :
      ( k7_relat_1('#skF_5',B_22) = k1_xboole_0
      | ~ r1_xboole_0(B_22,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46041,c_24])).

tff(c_46671,plain,(
    ! [B_1799] :
      ( k7_relat_1('#skF_5',B_1799) = k1_xboole_0
      | ~ r1_xboole_0(B_1799,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_46046])).

tff(c_46693,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | k9_relat_1('#skF_6','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46546,c_46671])).

tff(c_47430,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_47243,c_46693])).

tff(c_47434,plain,(
    ! [B_13] :
      ( k7_relat_1('#skF_5',k3_xboole_0('#skF_4',B_13)) = k7_relat_1(k1_xboole_0,B_13)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47430,c_14])).

tff(c_47445,plain,(
    ! [B_1851] : k7_relat_1('#skF_5',k3_xboole_0('#skF_4',B_1851)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_16,c_47434])).

tff(c_47459,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_47284,c_47445])).

tff(c_47288,plain,(
    ! [A_1837,B_1838,C_1839,D_1840] :
      ( k2_partfun1(A_1837,B_1838,C_1839,D_1840) = k7_relat_1(C_1839,D_1840)
      | ~ m1_subset_1(C_1839,k1_zfmisc_1(k2_zfmisc_1(A_1837,B_1838)))
      | ~ v1_funct_1(C_1839) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_47290,plain,(
    ! [D_1840] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_1840) = k7_relat_1('#skF_6',D_1840)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_60,c_47288])).

tff(c_47295,plain,(
    ! [D_1840] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_1840) = k7_relat_1('#skF_6',D_1840) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_47290])).

tff(c_47292,plain,(
    ! [D_1840] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_1840) = k7_relat_1('#skF_5',D_1840)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_66,c_47288])).

tff(c_47298,plain,(
    ! [D_1840] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_1840) = k7_relat_1('#skF_5',D_1840) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_47292])).

tff(c_47540,plain,(
    ! [B_1858,D_1857,E_1854,A_1859,F_1856,C_1855] :
      ( v1_funct_1(k1_tmap_1(A_1859,B_1858,C_1855,D_1857,E_1854,F_1856))
      | ~ m1_subset_1(F_1856,k1_zfmisc_1(k2_zfmisc_1(D_1857,B_1858)))
      | ~ v1_funct_2(F_1856,D_1857,B_1858)
      | ~ v1_funct_1(F_1856)
      | ~ m1_subset_1(E_1854,k1_zfmisc_1(k2_zfmisc_1(C_1855,B_1858)))
      | ~ v1_funct_2(E_1854,C_1855,B_1858)
      | ~ v1_funct_1(E_1854)
      | ~ m1_subset_1(D_1857,k1_zfmisc_1(A_1859))
      | v1_xboole_0(D_1857)
      | ~ m1_subset_1(C_1855,k1_zfmisc_1(A_1859))
      | v1_xboole_0(C_1855)
      | v1_xboole_0(B_1858)
      | v1_xboole_0(A_1859) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_47542,plain,(
    ! [A_1859,C_1855,E_1854] :
      ( v1_funct_1(k1_tmap_1(A_1859,'#skF_2',C_1855,'#skF_4',E_1854,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1854,k1_zfmisc_1(k2_zfmisc_1(C_1855,'#skF_2')))
      | ~ v1_funct_2(E_1854,C_1855,'#skF_2')
      | ~ v1_funct_1(E_1854)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1859))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1855,k1_zfmisc_1(A_1859))
      | v1_xboole_0(C_1855)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1859) ) ),
    inference(resolution,[status(thm)],[c_60,c_47540])).

tff(c_47547,plain,(
    ! [A_1859,C_1855,E_1854] :
      ( v1_funct_1(k1_tmap_1(A_1859,'#skF_2',C_1855,'#skF_4',E_1854,'#skF_6'))
      | ~ m1_subset_1(E_1854,k1_zfmisc_1(k2_zfmisc_1(C_1855,'#skF_2')))
      | ~ v1_funct_2(E_1854,C_1855,'#skF_2')
      | ~ v1_funct_1(E_1854)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1859))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1855,k1_zfmisc_1(A_1859))
      | v1_xboole_0(C_1855)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1859) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_47542])).

tff(c_48470,plain,(
    ! [A_1915,C_1916,E_1917] :
      ( v1_funct_1(k1_tmap_1(A_1915,'#skF_2',C_1916,'#skF_4',E_1917,'#skF_6'))
      | ~ m1_subset_1(E_1917,k1_zfmisc_1(k2_zfmisc_1(C_1916,'#skF_2')))
      | ~ v1_funct_2(E_1917,C_1916,'#skF_2')
      | ~ v1_funct_1(E_1917)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1915))
      | ~ m1_subset_1(C_1916,k1_zfmisc_1(A_1915))
      | v1_xboole_0(C_1916)
      | v1_xboole_0(A_1915) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_47547])).

tff(c_48477,plain,(
    ! [A_1915] :
      ( v1_funct_1(k1_tmap_1(A_1915,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1915))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1915))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1915) ) ),
    inference(resolution,[status(thm)],[c_66,c_48470])).

tff(c_48487,plain,(
    ! [A_1915] :
      ( v1_funct_1(k1_tmap_1(A_1915,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1915))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1915))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1915) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_48477])).

tff(c_49676,plain,(
    ! [A_1960] :
      ( v1_funct_1(k1_tmap_1(A_1960,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1960))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1960))
      | v1_xboole_0(A_1960) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_48487])).

tff(c_49679,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_78,c_49676])).

tff(c_49682,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_49679])).

tff(c_49683,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_49682])).

tff(c_48726,plain,(
    ! [B_1925,E_1926,C_1924,A_1922,D_1923,F_1927] :
      ( k2_partfun1(k4_subset_1(A_1922,C_1924,D_1923),B_1925,k1_tmap_1(A_1922,B_1925,C_1924,D_1923,E_1926,F_1927),C_1924) = E_1926
      | ~ m1_subset_1(k1_tmap_1(A_1922,B_1925,C_1924,D_1923,E_1926,F_1927),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1922,C_1924,D_1923),B_1925)))
      | ~ v1_funct_2(k1_tmap_1(A_1922,B_1925,C_1924,D_1923,E_1926,F_1927),k4_subset_1(A_1922,C_1924,D_1923),B_1925)
      | ~ v1_funct_1(k1_tmap_1(A_1922,B_1925,C_1924,D_1923,E_1926,F_1927))
      | k2_partfun1(D_1923,B_1925,F_1927,k9_subset_1(A_1922,C_1924,D_1923)) != k2_partfun1(C_1924,B_1925,E_1926,k9_subset_1(A_1922,C_1924,D_1923))
      | ~ m1_subset_1(F_1927,k1_zfmisc_1(k2_zfmisc_1(D_1923,B_1925)))
      | ~ v1_funct_2(F_1927,D_1923,B_1925)
      | ~ v1_funct_1(F_1927)
      | ~ m1_subset_1(E_1926,k1_zfmisc_1(k2_zfmisc_1(C_1924,B_1925)))
      | ~ v1_funct_2(E_1926,C_1924,B_1925)
      | ~ v1_funct_1(E_1926)
      | ~ m1_subset_1(D_1923,k1_zfmisc_1(A_1922))
      | v1_xboole_0(D_1923)
      | ~ m1_subset_1(C_1924,k1_zfmisc_1(A_1922))
      | v1_xboole_0(C_1924)
      | v1_xboole_0(B_1925)
      | v1_xboole_0(A_1922) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_59149,plain,(
    ! [D_2303,E_2300,C_2301,F_2302,A_2305,B_2304] :
      ( k2_partfun1(k4_subset_1(A_2305,C_2301,D_2303),B_2304,k1_tmap_1(A_2305,B_2304,C_2301,D_2303,E_2300,F_2302),C_2301) = E_2300
      | ~ v1_funct_2(k1_tmap_1(A_2305,B_2304,C_2301,D_2303,E_2300,F_2302),k4_subset_1(A_2305,C_2301,D_2303),B_2304)
      | ~ v1_funct_1(k1_tmap_1(A_2305,B_2304,C_2301,D_2303,E_2300,F_2302))
      | k2_partfun1(D_2303,B_2304,F_2302,k9_subset_1(A_2305,C_2301,D_2303)) != k2_partfun1(C_2301,B_2304,E_2300,k9_subset_1(A_2305,C_2301,D_2303))
      | ~ m1_subset_1(F_2302,k1_zfmisc_1(k2_zfmisc_1(D_2303,B_2304)))
      | ~ v1_funct_2(F_2302,D_2303,B_2304)
      | ~ v1_funct_1(F_2302)
      | ~ m1_subset_1(E_2300,k1_zfmisc_1(k2_zfmisc_1(C_2301,B_2304)))
      | ~ v1_funct_2(E_2300,C_2301,B_2304)
      | ~ v1_funct_1(E_2300)
      | ~ m1_subset_1(D_2303,k1_zfmisc_1(A_2305))
      | v1_xboole_0(D_2303)
      | ~ m1_subset_1(C_2301,k1_zfmisc_1(A_2305))
      | v1_xboole_0(C_2301)
      | v1_xboole_0(B_2304)
      | v1_xboole_0(A_2305) ) ),
    inference(resolution,[status(thm)],[c_52,c_48726])).

tff(c_81369,plain,(
    ! [B_2690,D_2689,A_2691,C_2687,F_2688,E_2686] :
      ( k2_partfun1(k4_subset_1(A_2691,C_2687,D_2689),B_2690,k1_tmap_1(A_2691,B_2690,C_2687,D_2689,E_2686,F_2688),C_2687) = E_2686
      | ~ v1_funct_1(k1_tmap_1(A_2691,B_2690,C_2687,D_2689,E_2686,F_2688))
      | k2_partfun1(D_2689,B_2690,F_2688,k9_subset_1(A_2691,C_2687,D_2689)) != k2_partfun1(C_2687,B_2690,E_2686,k9_subset_1(A_2691,C_2687,D_2689))
      | ~ m1_subset_1(F_2688,k1_zfmisc_1(k2_zfmisc_1(D_2689,B_2690)))
      | ~ v1_funct_2(F_2688,D_2689,B_2690)
      | ~ v1_funct_1(F_2688)
      | ~ m1_subset_1(E_2686,k1_zfmisc_1(k2_zfmisc_1(C_2687,B_2690)))
      | ~ v1_funct_2(E_2686,C_2687,B_2690)
      | ~ v1_funct_1(E_2686)
      | ~ m1_subset_1(D_2689,k1_zfmisc_1(A_2691))
      | v1_xboole_0(D_2689)
      | ~ m1_subset_1(C_2687,k1_zfmisc_1(A_2691))
      | v1_xboole_0(C_2687)
      | v1_xboole_0(B_2690)
      | v1_xboole_0(A_2691) ) ),
    inference(resolution,[status(thm)],[c_54,c_59149])).

tff(c_81373,plain,(
    ! [A_2691,C_2687,E_2686] :
      ( k2_partfun1(k4_subset_1(A_2691,C_2687,'#skF_4'),'#skF_2',k1_tmap_1(A_2691,'#skF_2',C_2687,'#skF_4',E_2686,'#skF_6'),C_2687) = E_2686
      | ~ v1_funct_1(k1_tmap_1(A_2691,'#skF_2',C_2687,'#skF_4',E_2686,'#skF_6'))
      | k2_partfun1(C_2687,'#skF_2',E_2686,k9_subset_1(A_2691,C_2687,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_2691,C_2687,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_2686,k1_zfmisc_1(k2_zfmisc_1(C_2687,'#skF_2')))
      | ~ v1_funct_2(E_2686,C_2687,'#skF_2')
      | ~ v1_funct_1(E_2686)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2691))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_2687,k1_zfmisc_1(A_2691))
      | v1_xboole_0(C_2687)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_2691) ) ),
    inference(resolution,[status(thm)],[c_60,c_81369])).

tff(c_81379,plain,(
    ! [A_2691,C_2687,E_2686] :
      ( k2_partfun1(k4_subset_1(A_2691,C_2687,'#skF_4'),'#skF_2',k1_tmap_1(A_2691,'#skF_2',C_2687,'#skF_4',E_2686,'#skF_6'),C_2687) = E_2686
      | ~ v1_funct_1(k1_tmap_1(A_2691,'#skF_2',C_2687,'#skF_4',E_2686,'#skF_6'))
      | k2_partfun1(C_2687,'#skF_2',E_2686,k9_subset_1(A_2691,C_2687,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2691,C_2687,'#skF_4'))
      | ~ m1_subset_1(E_2686,k1_zfmisc_1(k2_zfmisc_1(C_2687,'#skF_2')))
      | ~ v1_funct_2(E_2686,C_2687,'#skF_2')
      | ~ v1_funct_1(E_2686)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2691))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_2687,k1_zfmisc_1(A_2691))
      | v1_xboole_0(C_2687)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_2691) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_47295,c_81373])).

tff(c_81423,plain,(
    ! [A_2694,C_2695,E_2696] :
      ( k2_partfun1(k4_subset_1(A_2694,C_2695,'#skF_4'),'#skF_2',k1_tmap_1(A_2694,'#skF_2',C_2695,'#skF_4',E_2696,'#skF_6'),C_2695) = E_2696
      | ~ v1_funct_1(k1_tmap_1(A_2694,'#skF_2',C_2695,'#skF_4',E_2696,'#skF_6'))
      | k2_partfun1(C_2695,'#skF_2',E_2696,k9_subset_1(A_2694,C_2695,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2694,C_2695,'#skF_4'))
      | ~ m1_subset_1(E_2696,k1_zfmisc_1(k2_zfmisc_1(C_2695,'#skF_2')))
      | ~ v1_funct_2(E_2696,C_2695,'#skF_2')
      | ~ v1_funct_1(E_2696)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2694))
      | ~ m1_subset_1(C_2695,k1_zfmisc_1(A_2694))
      | v1_xboole_0(C_2695)
      | v1_xboole_0(A_2694) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_81379])).

tff(c_81430,plain,(
    ! [A_2694] :
      ( k2_partfun1(k4_subset_1(A_2694,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_2694,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_2694,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_2694,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2694,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2694))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_2694))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2694) ) ),
    inference(resolution,[status(thm)],[c_66,c_81423])).

tff(c_81440,plain,(
    ! [A_2694] :
      ( k2_partfun1(k4_subset_1(A_2694,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_2694,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_2694,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_2694,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2694,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2694))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_2694))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2694) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_47298,c_81430])).

tff(c_84732,plain,(
    ! [A_2736] :
      ( k2_partfun1(k4_subset_1(A_2736,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_2736,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_2736,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_2736,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2736,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2736))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_2736))
      | v1_xboole_0(A_2736) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_81440])).

tff(c_45144,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_4879])).

tff(c_49461,plain,(
    ! [A_1946,C_1948,G_1950,D_1947,B_1949] :
      ( k1_tmap_1(A_1946,B_1949,C_1948,D_1947,k2_partfun1(k4_subset_1(A_1946,C_1948,D_1947),B_1949,G_1950,C_1948),k2_partfun1(k4_subset_1(A_1946,C_1948,D_1947),B_1949,G_1950,D_1947)) = G_1950
      | ~ m1_subset_1(G_1950,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1946,C_1948,D_1947),B_1949)))
      | ~ v1_funct_2(G_1950,k4_subset_1(A_1946,C_1948,D_1947),B_1949)
      | ~ v1_funct_1(G_1950)
      | k2_partfun1(D_1947,B_1949,k2_partfun1(k4_subset_1(A_1946,C_1948,D_1947),B_1949,G_1950,D_1947),k9_subset_1(A_1946,C_1948,D_1947)) != k2_partfun1(C_1948,B_1949,k2_partfun1(k4_subset_1(A_1946,C_1948,D_1947),B_1949,G_1950,C_1948),k9_subset_1(A_1946,C_1948,D_1947))
      | ~ m1_subset_1(k2_partfun1(k4_subset_1(A_1946,C_1948,D_1947),B_1949,G_1950,D_1947),k1_zfmisc_1(k2_zfmisc_1(D_1947,B_1949)))
      | ~ v1_funct_2(k2_partfun1(k4_subset_1(A_1946,C_1948,D_1947),B_1949,G_1950,D_1947),D_1947,B_1949)
      | ~ v1_funct_1(k2_partfun1(k4_subset_1(A_1946,C_1948,D_1947),B_1949,G_1950,D_1947))
      | ~ m1_subset_1(k2_partfun1(k4_subset_1(A_1946,C_1948,D_1947),B_1949,G_1950,C_1948),k1_zfmisc_1(k2_zfmisc_1(C_1948,B_1949)))
      | ~ v1_funct_2(k2_partfun1(k4_subset_1(A_1946,C_1948,D_1947),B_1949,G_1950,C_1948),C_1948,B_1949)
      | ~ v1_funct_1(k2_partfun1(k4_subset_1(A_1946,C_1948,D_1947),B_1949,G_1950,C_1948))
      | ~ m1_subset_1(D_1947,k1_zfmisc_1(A_1946))
      | v1_xboole_0(D_1947)
      | ~ m1_subset_1(C_1948,k1_zfmisc_1(A_1946))
      | v1_xboole_0(C_1948)
      | v1_xboole_0(B_1949)
      | v1_xboole_0(A_1946) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_49463,plain,
    ( k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4')) = k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')))
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k2_partfun1('#skF_3','#skF_2',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4'),k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4'),'#skF_4','#skF_2')
    | ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4'))
    | ~ m1_subset_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_45144,c_49461])).

tff(c_49465,plain,
    ( k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_6') = k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')))
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k2_partfun1('#skF_3','#skF_2',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_xboole_0) != k1_xboole_0
    | ~ m1_subset_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'))
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_64,c_45144,c_62,c_45144,c_60,c_46960,c_47295,c_46937,c_45156,c_46937,c_45156,c_45144,c_45144,c_49463])).

tff(c_49466,plain,
    ( k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_6') = k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')))
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k2_partfun1('#skF_3','#skF_2',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_xboole_0) != k1_xboole_0
    | ~ m1_subset_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_82,c_80,c_76,c_49465])).

tff(c_53017,plain,
    ( k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_6') = k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')))
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | k2_partfun1('#skF_3','#skF_2',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_xboole_0) != k1_xboole_0
    | ~ m1_subset_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49683,c_49466])).

tff(c_53018,plain,(
    ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_53017])).

tff(c_84741,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_84732,c_53018])).

tff(c_84754,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_47459,c_46927,c_45156,c_46937,c_45156,c_49683,c_70,c_84741])).

tff(c_84756,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_84754])).

tff(c_84757,plain,
    ( ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | k2_partfun1('#skF_3','#skF_2',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_xboole_0) != k1_xboole_0
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')))
    | k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_6') = k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_53017])).

tff(c_86845,plain,(
    ~ m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_84757])).

tff(c_89738,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_86845])).

tff(c_89741,plain,
    ( v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_70,c_68,c_66,c_64,c_62,c_60,c_89738])).

tff(c_89743,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_82,c_80,c_76,c_89741])).

tff(c_89745,plain,(
    m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_84757])).

tff(c_50,plain,(
    ! [C_137,A_41,D_153,B_105,F_165,E_161] :
      ( k2_partfun1(k4_subset_1(A_41,C_137,D_153),B_105,k1_tmap_1(A_41,B_105,C_137,D_153,E_161,F_165),C_137) = E_161
      | ~ m1_subset_1(k1_tmap_1(A_41,B_105,C_137,D_153,E_161,F_165),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_41,C_137,D_153),B_105)))
      | ~ v1_funct_2(k1_tmap_1(A_41,B_105,C_137,D_153,E_161,F_165),k4_subset_1(A_41,C_137,D_153),B_105)
      | ~ v1_funct_1(k1_tmap_1(A_41,B_105,C_137,D_153,E_161,F_165))
      | k2_partfun1(D_153,B_105,F_165,k9_subset_1(A_41,C_137,D_153)) != k2_partfun1(C_137,B_105,E_161,k9_subset_1(A_41,C_137,D_153))
      | ~ m1_subset_1(F_165,k1_zfmisc_1(k2_zfmisc_1(D_153,B_105)))
      | ~ v1_funct_2(F_165,D_153,B_105)
      | ~ v1_funct_1(F_165)
      | ~ m1_subset_1(E_161,k1_zfmisc_1(k2_zfmisc_1(C_137,B_105)))
      | ~ v1_funct_2(E_161,C_137,B_105)
      | ~ v1_funct_1(E_161)
      | ~ m1_subset_1(D_153,k1_zfmisc_1(A_41))
      | v1_xboole_0(D_153)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(A_41))
      | v1_xboole_0(C_137)
      | v1_xboole_0(B_105)
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_92463,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_89745,c_50])).

tff(c_92508,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_70,c_68,c_66,c_64,c_62,c_60,c_46927,c_45156,c_47459,c_46937,c_45156,c_47295,c_47298,c_49683,c_92463])).

tff(c_92509,plain,(
    ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_82,c_80,c_76,c_45143,c_92508])).

tff(c_92543,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_92509])).

tff(c_92546,plain,
    ( v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_70,c_68,c_66,c_64,c_62,c_60,c_92543])).

tff(c_92548,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_82,c_80,c_76,c_92546])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:36:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 25.02/16.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 25.07/16.12  
% 25.07/16.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 25.07/16.12  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 25.07/16.12  
% 25.07/16.12  %Foreground sorts:
% 25.07/16.12  
% 25.07/16.12  
% 25.07/16.12  %Background operators:
% 25.07/16.12  
% 25.07/16.12  
% 25.07/16.12  %Foreground operators:
% 25.07/16.12  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 25.07/16.12  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 25.07/16.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 25.07/16.12  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 25.07/16.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 25.07/16.12  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 25.07/16.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 25.07/16.12  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 25.07/16.12  tff('#skF_5', type, '#skF_5': $i).
% 25.07/16.12  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 25.07/16.12  tff('#skF_6', type, '#skF_6': $i).
% 25.07/16.12  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 25.07/16.12  tff('#skF_2', type, '#skF_2': $i).
% 25.07/16.12  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 25.07/16.12  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 25.07/16.12  tff('#skF_3', type, '#skF_3': $i).
% 25.07/16.12  tff('#skF_1', type, '#skF_1': $i).
% 25.07/16.12  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 25.07/16.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 25.07/16.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 25.07/16.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 25.07/16.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 25.07/16.12  tff('#skF_4', type, '#skF_4': $i).
% 25.07/16.12  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 25.07/16.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 25.07/16.12  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 25.07/16.12  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 25.07/16.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 25.07/16.12  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 25.07/16.12  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 25.07/16.12  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 25.07/16.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 25.07/16.12  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 25.07/16.12  
% 25.45/16.17  tff(f_239, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 25.45/16.17  tff(f_197, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 25.45/16.17  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 25.45/16.17  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 25.45/16.17  tff(f_109, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 25.45/16.17  tff(f_101, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 25.45/16.17  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 25.45/16.17  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 25.45/16.17  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 25.45/16.17  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 25.45/16.17  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 25.45/16.17  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 25.45/16.17  tff(f_50, axiom, (![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_relat_1)).
% 25.45/16.17  tff(f_48, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 25.45/16.17  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 25.45/16.17  tff(f_115, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 25.45/16.17  tff(f_163, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 25.45/16.17  tff(c_84, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_239])).
% 25.45/16.17  tff(c_82, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_239])).
% 25.45/16.17  tff(c_80, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_239])).
% 25.45/16.17  tff(c_76, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_239])).
% 25.45/16.17  tff(c_78, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_239])).
% 25.45/16.17  tff(c_74, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_239])).
% 25.45/16.17  tff(c_70, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_239])).
% 25.45/16.17  tff(c_68, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_239])).
% 25.45/16.17  tff(c_66, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_239])).
% 25.45/16.17  tff(c_64, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_239])).
% 25.45/16.17  tff(c_62, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_239])).
% 25.45/16.17  tff(c_60, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_239])).
% 25.45/16.17  tff(c_54, plain, (![F_173, C_170, D_171, A_168, B_169, E_172]: (v1_funct_2(k1_tmap_1(A_168, B_169, C_170, D_171, E_172, F_173), k4_subset_1(A_168, C_170, D_171), B_169) | ~m1_subset_1(F_173, k1_zfmisc_1(k2_zfmisc_1(D_171, B_169))) | ~v1_funct_2(F_173, D_171, B_169) | ~v1_funct_1(F_173) | ~m1_subset_1(E_172, k1_zfmisc_1(k2_zfmisc_1(C_170, B_169))) | ~v1_funct_2(E_172, C_170, B_169) | ~v1_funct_1(E_172) | ~m1_subset_1(D_171, k1_zfmisc_1(A_168)) | v1_xboole_0(D_171) | ~m1_subset_1(C_170, k1_zfmisc_1(A_168)) | v1_xboole_0(C_170) | v1_xboole_0(B_169) | v1_xboole_0(A_168))), inference(cnfTransformation, [status(thm)], [f_197])).
% 25.45/16.17  tff(c_114, plain, (![C_239, A_240, B_241]: (v1_relat_1(C_239) | ~m1_subset_1(C_239, k1_zfmisc_1(k2_zfmisc_1(A_240, B_241))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 25.45/16.17  tff(c_121, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_60, c_114])).
% 25.45/16.17  tff(c_122, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_114])).
% 25.45/16.17  tff(c_4911, plain, (![C_562, A_563, B_564]: (v4_relat_1(C_562, A_563) | ~m1_subset_1(C_562, k1_zfmisc_1(k2_zfmisc_1(A_563, B_564))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 25.45/16.17  tff(c_4919, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_4911])).
% 25.45/16.17  tff(c_5043, plain, (![B_585, A_586]: (k1_relat_1(B_585)=A_586 | ~v1_partfun1(B_585, A_586) | ~v4_relat_1(B_585, A_586) | ~v1_relat_1(B_585))), inference(cnfTransformation, [status(thm)], [f_109])).
% 25.45/16.17  tff(c_5046, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_4919, c_5043])).
% 25.45/16.17  tff(c_5052, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_5046])).
% 25.45/16.17  tff(c_5056, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_5052])).
% 25.45/16.17  tff(c_5708, plain, (![C_635, A_636, B_637]: (v1_partfun1(C_635, A_636) | ~v1_funct_2(C_635, A_636, B_637) | ~v1_funct_1(C_635) | ~m1_subset_1(C_635, k1_zfmisc_1(k2_zfmisc_1(A_636, B_637))) | v1_xboole_0(B_637))), inference(cnfTransformation, [status(thm)], [f_101])).
% 25.45/16.17  tff(c_5714, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_66, c_5708])).
% 25.45/16.17  tff(c_5721, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_5714])).
% 25.45/16.17  tff(c_5723, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_5056, c_5721])).
% 25.45/16.17  tff(c_5724, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_5052])).
% 25.45/16.17  tff(c_22, plain, (![B_19, A_18]: (r1_xboole_0(k1_relat_1(B_19), A_18) | k9_relat_1(B_19, A_18)!=k1_xboole_0 | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_60])).
% 25.45/16.17  tff(c_5735, plain, (![A_18]: (r1_xboole_0('#skF_3', A_18) | k9_relat_1('#skF_5', A_18)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5724, c_22])).
% 25.45/16.17  tff(c_6233, plain, (![A_671]: (r1_xboole_0('#skF_3', A_671) | k9_relat_1('#skF_5', A_671)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_122, c_5735])).
% 25.45/16.17  tff(c_4918, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_60, c_4911])).
% 25.45/16.17  tff(c_5049, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_4918, c_5043])).
% 25.45/16.17  tff(c_5055, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_5049])).
% 25.45/16.17  tff(c_5755, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_5055])).
% 25.45/16.17  tff(c_6080, plain, (![C_660, A_661, B_662]: (v1_partfun1(C_660, A_661) | ~v1_funct_2(C_660, A_661, B_662) | ~v1_funct_1(C_660) | ~m1_subset_1(C_660, k1_zfmisc_1(k2_zfmisc_1(A_661, B_662))) | v1_xboole_0(B_662))), inference(cnfTransformation, [status(thm)], [f_101])).
% 25.45/16.17  tff(c_6083, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_6080])).
% 25.45/16.17  tff(c_6089, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_6083])).
% 25.45/16.17  tff(c_6091, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_5755, c_6089])).
% 25.45/16.17  tff(c_6092, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_5055])).
% 25.45/16.17  tff(c_24, plain, (![A_20, B_22]: (k7_relat_1(A_20, B_22)=k1_xboole_0 | ~r1_xboole_0(B_22, k1_relat_1(A_20)) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_67])).
% 25.45/16.17  tff(c_6097, plain, (![B_22]: (k7_relat_1('#skF_6', B_22)=k1_xboole_0 | ~r1_xboole_0(B_22, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_6092, c_24])).
% 25.45/16.17  tff(c_6110, plain, (![B_22]: (k7_relat_1('#skF_6', B_22)=k1_xboole_0 | ~r1_xboole_0(B_22, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_6097])).
% 25.45/16.17  tff(c_6256, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | k9_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6233, c_6110])).
% 25.45/16.17  tff(c_6353, plain, (k9_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_6256])).
% 25.45/16.17  tff(c_72, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_239])).
% 25.45/16.17  tff(c_28, plain, (![A_23, B_24]: (r1_xboole_0(A_23, B_24) | ~r1_subset_1(A_23, B_24) | v1_xboole_0(B_24) | v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_77])).
% 25.45/16.17  tff(c_20, plain, (![B_19, A_18]: (k9_relat_1(B_19, A_18)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_19), A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_60])).
% 25.45/16.17  tff(c_5738, plain, (![A_18]: (k9_relat_1('#skF_5', A_18)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_18) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5724, c_20])).
% 25.45/16.17  tff(c_6119, plain, (![A_663]: (k9_relat_1('#skF_5', A_663)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_663))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_5738])).
% 25.45/16.17  tff(c_6123, plain, (![B_24]: (k9_relat_1('#skF_5', B_24)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_24) | v1_xboole_0(B_24) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_6119])).
% 25.45/16.17  tff(c_6392, plain, (![B_689]: (k9_relat_1('#skF_5', B_689)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_689) | v1_xboole_0(B_689))), inference(negUnitSimplification, [status(thm)], [c_80, c_6123])).
% 25.45/16.17  tff(c_6395, plain, (k9_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_72, c_6392])).
% 25.45/16.17  tff(c_6399, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_6353, c_6395])).
% 25.45/16.17  tff(c_6400, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_6256])).
% 25.45/16.17  tff(c_18, plain, (![B_17, A_16]: (k2_relat_1(k7_relat_1(B_17, A_16))=k9_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_54])).
% 25.45/16.17  tff(c_6411, plain, (k9_relat_1('#skF_6', '#skF_3')=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_6400, c_18])).
% 25.45/16.17  tff(c_6421, plain, (k9_relat_1('#skF_6', '#skF_3')=k2_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_121, c_6411])).
% 25.45/16.17  tff(c_6103, plain, (![A_18]: (r1_xboole_0('#skF_4', A_18) | k9_relat_1('#skF_6', A_18)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_6092, c_22])).
% 25.45/16.17  tff(c_6132, plain, (![A_664]: (r1_xboole_0('#skF_4', A_664) | k9_relat_1('#skF_6', A_664)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_121, c_6103])).
% 25.45/16.17  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 25.45/16.17  tff(c_6147, plain, (![A_664]: (k3_xboole_0('#skF_4', A_664)=k1_xboole_0 | k9_relat_1('#skF_6', A_664)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6132, c_2])).
% 25.45/16.17  tff(c_6447, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0 | k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6421, c_6147])).
% 25.45/16.17  tff(c_6563, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_6447])).
% 25.45/16.17  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 25.45/16.17  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 25.45/16.17  tff(c_6106, plain, (![A_18]: (k9_relat_1('#skF_6', A_18)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_18) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_6092, c_20])).
% 25.45/16.17  tff(c_6171, plain, (![A_666]: (k9_relat_1('#skF_6', A_666)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_666))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_6106])).
% 25.45/16.17  tff(c_6621, plain, (![B_705]: (k9_relat_1('#skF_6', B_705)=k1_xboole_0 | k3_xboole_0('#skF_4', B_705)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_6171])).
% 25.45/16.17  tff(c_6401, plain, (k9_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_6256])).
% 25.45/16.17  tff(c_6262, plain, (![A_671]: (k3_xboole_0('#skF_3', A_671)=k1_xboole_0 | k9_relat_1('#skF_5', A_671)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6233, c_2])).
% 25.45/16.17  tff(c_6436, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6401, c_6262])).
% 25.45/16.17  tff(c_16, plain, (![A_15]: (k7_relat_1(k1_xboole_0, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 25.45/16.17  tff(c_14, plain, (![C_14, A_12, B_13]: (k7_relat_1(k7_relat_1(C_14, A_12), B_13)=k7_relat_1(C_14, k3_xboole_0(A_12, B_13)) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_48])).
% 25.45/16.17  tff(c_6408, plain, (![B_13]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_3', B_13))=k7_relat_1(k1_xboole_0, B_13) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_6400, c_14])).
% 25.45/16.17  tff(c_6451, plain, (![B_690]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_3', B_690))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_121, c_16, c_6408])).
% 25.45/16.17  tff(c_6466, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6436, c_6451])).
% 25.45/16.17  tff(c_6505, plain, (k9_relat_1('#skF_6', k1_xboole_0)=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_6466, c_18])).
% 25.45/16.17  tff(c_6515, plain, (k9_relat_1('#skF_6', k1_xboole_0)=k2_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_121, c_6505])).
% 25.45/16.17  tff(c_6636, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | k3_xboole_0('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6621, c_6515])).
% 25.45/16.17  tff(c_6663, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6636])).
% 25.45/16.17  tff(c_6665, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6563, c_6663])).
% 25.45/16.17  tff(c_6667, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_6447])).
% 25.45/16.17  tff(c_6462, plain, (![B_690]: (k9_relat_1('#skF_6', k3_xboole_0('#skF_3', B_690))=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_6451, c_18])).
% 25.45/16.17  tff(c_6478, plain, (![B_690]: (k9_relat_1('#skF_6', k3_xboole_0('#skF_3', B_690))=k2_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_6462])).
% 25.45/16.17  tff(c_6710, plain, (![B_712]: (k9_relat_1('#skF_6', k3_xboole_0('#skF_3', B_712))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6667, c_6478])).
% 25.45/16.17  tff(c_6724, plain, (![B_712]: (k3_xboole_0('#skF_4', k3_xboole_0('#skF_3', B_712))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6710, c_6147])).
% 25.45/16.17  tff(c_6669, plain, (k9_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6667, c_6421])).
% 25.45/16.17  tff(c_6114, plain, (![A_18]: (r1_xboole_0('#skF_4', A_18) | k9_relat_1('#skF_6', A_18)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_121, c_6103])).
% 25.45/16.17  tff(c_5729, plain, (![B_22]: (k7_relat_1('#skF_5', B_22)=k1_xboole_0 | ~r1_xboole_0(B_22, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5724, c_24])).
% 25.45/16.17  tff(c_6188, plain, (![B_667]: (k7_relat_1('#skF_5', B_667)=k1_xboole_0 | ~r1_xboole_0(B_667, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_5729])).
% 25.45/16.17  tff(c_6205, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | k9_relat_1('#skF_6', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6114, c_6188])).
% 25.45/16.17  tff(c_6782, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6669, c_6205])).
% 25.45/16.17  tff(c_6789, plain, (![B_13]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_4', B_13))=k7_relat_1(k1_xboole_0, B_13) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_6782, c_14])).
% 25.45/16.17  tff(c_6809, plain, (![B_717]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_4', B_717))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_122, c_16, c_6789])).
% 25.45/16.17  tff(c_6826, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6724, c_6809])).
% 25.45/16.17  tff(c_6419, plain, (![B_13]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_3', B_13))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_121, c_16, c_6408])).
% 25.45/16.17  tff(c_4993, plain, (![A_578, B_579, C_580]: (k9_subset_1(A_578, B_579, C_580)=k3_xboole_0(B_579, C_580) | ~m1_subset_1(C_580, k1_zfmisc_1(A_578)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 25.45/16.17  tff(c_5004, plain, (![B_579]: (k9_subset_1('#skF_1', B_579, '#skF_4')=k3_xboole_0(B_579, '#skF_4'))), inference(resolution, [status(thm)], [c_74, c_4993])).
% 25.45/16.17  tff(c_6696, plain, (![F_708, E_706, A_711, C_707, B_710, D_709]: (v1_funct_1(k1_tmap_1(A_711, B_710, C_707, D_709, E_706, F_708)) | ~m1_subset_1(F_708, k1_zfmisc_1(k2_zfmisc_1(D_709, B_710))) | ~v1_funct_2(F_708, D_709, B_710) | ~v1_funct_1(F_708) | ~m1_subset_1(E_706, k1_zfmisc_1(k2_zfmisc_1(C_707, B_710))) | ~v1_funct_2(E_706, C_707, B_710) | ~v1_funct_1(E_706) | ~m1_subset_1(D_709, k1_zfmisc_1(A_711)) | v1_xboole_0(D_709) | ~m1_subset_1(C_707, k1_zfmisc_1(A_711)) | v1_xboole_0(C_707) | v1_xboole_0(B_710) | v1_xboole_0(A_711))), inference(cnfTransformation, [status(thm)], [f_197])).
% 25.45/16.17  tff(c_6698, plain, (![A_711, C_707, E_706]: (v1_funct_1(k1_tmap_1(A_711, '#skF_2', C_707, '#skF_4', E_706, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_706, k1_zfmisc_1(k2_zfmisc_1(C_707, '#skF_2'))) | ~v1_funct_2(E_706, C_707, '#skF_2') | ~v1_funct_1(E_706) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_711)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_707, k1_zfmisc_1(A_711)) | v1_xboole_0(C_707) | v1_xboole_0('#skF_2') | v1_xboole_0(A_711))), inference(resolution, [status(thm)], [c_60, c_6696])).
% 25.45/16.17  tff(c_6703, plain, (![A_711, C_707, E_706]: (v1_funct_1(k1_tmap_1(A_711, '#skF_2', C_707, '#skF_4', E_706, '#skF_6')) | ~m1_subset_1(E_706, k1_zfmisc_1(k2_zfmisc_1(C_707, '#skF_2'))) | ~v1_funct_2(E_706, C_707, '#skF_2') | ~v1_funct_1(E_706) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_711)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_707, k1_zfmisc_1(A_711)) | v1_xboole_0(C_707) | v1_xboole_0('#skF_2') | v1_xboole_0(A_711))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_6698])).
% 25.45/16.17  tff(c_9025, plain, (![A_823, C_824, E_825]: (v1_funct_1(k1_tmap_1(A_823, '#skF_2', C_824, '#skF_4', E_825, '#skF_6')) | ~m1_subset_1(E_825, k1_zfmisc_1(k2_zfmisc_1(C_824, '#skF_2'))) | ~v1_funct_2(E_825, C_824, '#skF_2') | ~v1_funct_1(E_825) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_823)) | ~m1_subset_1(C_824, k1_zfmisc_1(A_823)) | v1_xboole_0(C_824) | v1_xboole_0(A_823))), inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_6703])).
% 25.45/16.17  tff(c_9032, plain, (![A_823]: (v1_funct_1(k1_tmap_1(A_823, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_823)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_823)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_823))), inference(resolution, [status(thm)], [c_66, c_9025])).
% 25.45/16.17  tff(c_9042, plain, (![A_823]: (v1_funct_1(k1_tmap_1(A_823, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_823)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_823)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_823))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_9032])).
% 25.45/16.17  tff(c_9709, plain, (![A_857]: (v1_funct_1(k1_tmap_1(A_857, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_857)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_857)) | v1_xboole_0(A_857))), inference(negUnitSimplification, [status(thm)], [c_80, c_9042])).
% 25.45/16.17  tff(c_9712, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_78, c_9709])).
% 25.45/16.17  tff(c_9715, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_9712])).
% 25.45/16.17  tff(c_9716, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_84, c_9715])).
% 25.45/16.17  tff(c_6321, plain, (![A_677, B_678, C_679, D_680]: (k2_partfun1(A_677, B_678, C_679, D_680)=k7_relat_1(C_679, D_680) | ~m1_subset_1(C_679, k1_zfmisc_1(k2_zfmisc_1(A_677, B_678))) | ~v1_funct_1(C_679))), inference(cnfTransformation, [status(thm)], [f_115])).
% 25.45/16.17  tff(c_6325, plain, (![D_680]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_680)=k7_relat_1('#skF_5', D_680) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_66, c_6321])).
% 25.45/16.17  tff(c_6331, plain, (![D_680]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_680)=k7_relat_1('#skF_5', D_680))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_6325])).
% 25.45/16.17  tff(c_6323, plain, (![D_680]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_680)=k7_relat_1('#skF_6', D_680) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_60, c_6321])).
% 25.45/16.17  tff(c_6328, plain, (![D_680]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_680)=k7_relat_1('#skF_6', D_680))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_6323])).
% 25.45/16.17  tff(c_52, plain, (![F_173, C_170, D_171, A_168, B_169, E_172]: (m1_subset_1(k1_tmap_1(A_168, B_169, C_170, D_171, E_172, F_173), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_168, C_170, D_171), B_169))) | ~m1_subset_1(F_173, k1_zfmisc_1(k2_zfmisc_1(D_171, B_169))) | ~v1_funct_2(F_173, D_171, B_169) | ~v1_funct_1(F_173) | ~m1_subset_1(E_172, k1_zfmisc_1(k2_zfmisc_1(C_170, B_169))) | ~v1_funct_2(E_172, C_170, B_169) | ~v1_funct_1(E_172) | ~m1_subset_1(D_171, k1_zfmisc_1(A_168)) | v1_xboole_0(D_171) | ~m1_subset_1(C_170, k1_zfmisc_1(A_168)) | v1_xboole_0(C_170) | v1_xboole_0(B_169) | v1_xboole_0(A_168))), inference(cnfTransformation, [status(thm)], [f_197])).
% 25.45/16.17  tff(c_7305, plain, (![E_750, C_748, B_749, A_746, F_751, D_747]: (k2_partfun1(k4_subset_1(A_746, C_748, D_747), B_749, k1_tmap_1(A_746, B_749, C_748, D_747, E_750, F_751), D_747)=F_751 | ~m1_subset_1(k1_tmap_1(A_746, B_749, C_748, D_747, E_750, F_751), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_746, C_748, D_747), B_749))) | ~v1_funct_2(k1_tmap_1(A_746, B_749, C_748, D_747, E_750, F_751), k4_subset_1(A_746, C_748, D_747), B_749) | ~v1_funct_1(k1_tmap_1(A_746, B_749, C_748, D_747, E_750, F_751)) | k2_partfun1(D_747, B_749, F_751, k9_subset_1(A_746, C_748, D_747))!=k2_partfun1(C_748, B_749, E_750, k9_subset_1(A_746, C_748, D_747)) | ~m1_subset_1(F_751, k1_zfmisc_1(k2_zfmisc_1(D_747, B_749))) | ~v1_funct_2(F_751, D_747, B_749) | ~v1_funct_1(F_751) | ~m1_subset_1(E_750, k1_zfmisc_1(k2_zfmisc_1(C_748, B_749))) | ~v1_funct_2(E_750, C_748, B_749) | ~v1_funct_1(E_750) | ~m1_subset_1(D_747, k1_zfmisc_1(A_746)) | v1_xboole_0(D_747) | ~m1_subset_1(C_748, k1_zfmisc_1(A_746)) | v1_xboole_0(C_748) | v1_xboole_0(B_749) | v1_xboole_0(A_746))), inference(cnfTransformation, [status(thm)], [f_163])).
% 25.45/16.17  tff(c_18341, plain, (![F_1148, B_1150, E_1146, A_1151, C_1147, D_1149]: (k2_partfun1(k4_subset_1(A_1151, C_1147, D_1149), B_1150, k1_tmap_1(A_1151, B_1150, C_1147, D_1149, E_1146, F_1148), D_1149)=F_1148 | ~v1_funct_2(k1_tmap_1(A_1151, B_1150, C_1147, D_1149, E_1146, F_1148), k4_subset_1(A_1151, C_1147, D_1149), B_1150) | ~v1_funct_1(k1_tmap_1(A_1151, B_1150, C_1147, D_1149, E_1146, F_1148)) | k2_partfun1(D_1149, B_1150, F_1148, k9_subset_1(A_1151, C_1147, D_1149))!=k2_partfun1(C_1147, B_1150, E_1146, k9_subset_1(A_1151, C_1147, D_1149)) | ~m1_subset_1(F_1148, k1_zfmisc_1(k2_zfmisc_1(D_1149, B_1150))) | ~v1_funct_2(F_1148, D_1149, B_1150) | ~v1_funct_1(F_1148) | ~m1_subset_1(E_1146, k1_zfmisc_1(k2_zfmisc_1(C_1147, B_1150))) | ~v1_funct_2(E_1146, C_1147, B_1150) | ~v1_funct_1(E_1146) | ~m1_subset_1(D_1149, k1_zfmisc_1(A_1151)) | v1_xboole_0(D_1149) | ~m1_subset_1(C_1147, k1_zfmisc_1(A_1151)) | v1_xboole_0(C_1147) | v1_xboole_0(B_1150) | v1_xboole_0(A_1151))), inference(resolution, [status(thm)], [c_52, c_7305])).
% 25.45/16.17  tff(c_40591, plain, (![B_1555, F_1553, C_1552, E_1551, A_1556, D_1554]: (k2_partfun1(k4_subset_1(A_1556, C_1552, D_1554), B_1555, k1_tmap_1(A_1556, B_1555, C_1552, D_1554, E_1551, F_1553), D_1554)=F_1553 | ~v1_funct_1(k1_tmap_1(A_1556, B_1555, C_1552, D_1554, E_1551, F_1553)) | k2_partfun1(D_1554, B_1555, F_1553, k9_subset_1(A_1556, C_1552, D_1554))!=k2_partfun1(C_1552, B_1555, E_1551, k9_subset_1(A_1556, C_1552, D_1554)) | ~m1_subset_1(F_1553, k1_zfmisc_1(k2_zfmisc_1(D_1554, B_1555))) | ~v1_funct_2(F_1553, D_1554, B_1555) | ~v1_funct_1(F_1553) | ~m1_subset_1(E_1551, k1_zfmisc_1(k2_zfmisc_1(C_1552, B_1555))) | ~v1_funct_2(E_1551, C_1552, B_1555) | ~v1_funct_1(E_1551) | ~m1_subset_1(D_1554, k1_zfmisc_1(A_1556)) | v1_xboole_0(D_1554) | ~m1_subset_1(C_1552, k1_zfmisc_1(A_1556)) | v1_xboole_0(C_1552) | v1_xboole_0(B_1555) | v1_xboole_0(A_1556))), inference(resolution, [status(thm)], [c_54, c_18341])).
% 25.45/16.17  tff(c_40595, plain, (![A_1556, C_1552, E_1551]: (k2_partfun1(k4_subset_1(A_1556, C_1552, '#skF_4'), '#skF_2', k1_tmap_1(A_1556, '#skF_2', C_1552, '#skF_4', E_1551, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1556, '#skF_2', C_1552, '#skF_4', E_1551, '#skF_6')) | k2_partfun1(C_1552, '#skF_2', E_1551, k9_subset_1(A_1556, C_1552, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_1556, C_1552, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1551, k1_zfmisc_1(k2_zfmisc_1(C_1552, '#skF_2'))) | ~v1_funct_2(E_1551, C_1552, '#skF_2') | ~v1_funct_1(E_1551) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1556)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1552, k1_zfmisc_1(A_1556)) | v1_xboole_0(C_1552) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1556))), inference(resolution, [status(thm)], [c_60, c_40591])).
% 25.45/16.17  tff(c_40601, plain, (![A_1556, C_1552, E_1551]: (k2_partfun1(k4_subset_1(A_1556, C_1552, '#skF_4'), '#skF_2', k1_tmap_1(A_1556, '#skF_2', C_1552, '#skF_4', E_1551, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1556, '#skF_2', C_1552, '#skF_4', E_1551, '#skF_6')) | k2_partfun1(C_1552, '#skF_2', E_1551, k9_subset_1(A_1556, C_1552, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1556, C_1552, '#skF_4')) | ~m1_subset_1(E_1551, k1_zfmisc_1(k2_zfmisc_1(C_1552, '#skF_2'))) | ~v1_funct_2(E_1551, C_1552, '#skF_2') | ~v1_funct_1(E_1551) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1556)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1552, k1_zfmisc_1(A_1556)) | v1_xboole_0(C_1552) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1556))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_6328, c_40595])).
% 25.45/16.17  tff(c_41468, plain, (![A_1578, C_1579, E_1580]: (k2_partfun1(k4_subset_1(A_1578, C_1579, '#skF_4'), '#skF_2', k1_tmap_1(A_1578, '#skF_2', C_1579, '#skF_4', E_1580, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1578, '#skF_2', C_1579, '#skF_4', E_1580, '#skF_6')) | k2_partfun1(C_1579, '#skF_2', E_1580, k9_subset_1(A_1578, C_1579, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1578, C_1579, '#skF_4')) | ~m1_subset_1(E_1580, k1_zfmisc_1(k2_zfmisc_1(C_1579, '#skF_2'))) | ~v1_funct_2(E_1580, C_1579, '#skF_2') | ~v1_funct_1(E_1580) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1578)) | ~m1_subset_1(C_1579, k1_zfmisc_1(A_1578)) | v1_xboole_0(C_1579) | v1_xboole_0(A_1578))), inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_40601])).
% 25.45/16.17  tff(c_41475, plain, (![A_1578]: (k2_partfun1(k4_subset_1(A_1578, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1578, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1578, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_1578, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1578, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1578)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1578)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1578))), inference(resolution, [status(thm)], [c_66, c_41468])).
% 25.45/16.17  tff(c_41485, plain, (![A_1578]: (k2_partfun1(k4_subset_1(A_1578, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1578, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1578, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1578, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1578, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1578)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1578)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1578))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_6331, c_41475])).
% 25.45/16.17  tff(c_45115, plain, (![A_1679]: (k2_partfun1(k4_subset_1(A_1679, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1679, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1679, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1679, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1679, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1679)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1679)) | v1_xboole_0(A_1679))), inference(negUnitSimplification, [status(thm)], [c_80, c_41485])).
% 25.45/16.17  tff(c_167, plain, (![C_249, A_250, B_251]: (v4_relat_1(C_249, A_250) | ~m1_subset_1(C_249, k1_zfmisc_1(k2_zfmisc_1(A_250, B_251))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 25.45/16.17  tff(c_175, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_167])).
% 25.45/16.17  tff(c_231, plain, (![B_263, A_264]: (k1_relat_1(B_263)=A_264 | ~v1_partfun1(B_263, A_264) | ~v4_relat_1(B_263, A_264) | ~v1_relat_1(B_263))), inference(cnfTransformation, [status(thm)], [f_109])).
% 25.45/16.17  tff(c_234, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_175, c_231])).
% 25.45/16.17  tff(c_240, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_234])).
% 25.45/16.17  tff(c_244, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_240])).
% 25.45/16.17  tff(c_710, plain, (![C_317, A_318, B_319]: (v1_partfun1(C_317, A_318) | ~v1_funct_2(C_317, A_318, B_319) | ~v1_funct_1(C_317) | ~m1_subset_1(C_317, k1_zfmisc_1(k2_zfmisc_1(A_318, B_319))) | v1_xboole_0(B_319))), inference(cnfTransformation, [status(thm)], [f_101])).
% 25.45/16.17  tff(c_716, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_66, c_710])).
% 25.45/16.17  tff(c_723, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_716])).
% 25.45/16.17  tff(c_725, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_244, c_723])).
% 25.45/16.17  tff(c_726, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_240])).
% 25.45/16.17  tff(c_740, plain, (![A_18]: (r1_xboole_0('#skF_3', A_18) | k9_relat_1('#skF_5', A_18)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_726, c_22])).
% 25.45/16.17  tff(c_750, plain, (![A_18]: (r1_xboole_0('#skF_3', A_18) | k9_relat_1('#skF_5', A_18)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_122, c_740])).
% 25.45/16.17  tff(c_174, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_60, c_167])).
% 25.45/16.17  tff(c_237, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_174, c_231])).
% 25.45/16.17  tff(c_243, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_237])).
% 25.45/16.17  tff(c_753, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_243])).
% 25.45/16.17  tff(c_1075, plain, (![C_352, A_353, B_354]: (v1_partfun1(C_352, A_353) | ~v1_funct_2(C_352, A_353, B_354) | ~v1_funct_1(C_352) | ~m1_subset_1(C_352, k1_zfmisc_1(k2_zfmisc_1(A_353, B_354))) | v1_xboole_0(B_354))), inference(cnfTransformation, [status(thm)], [f_101])).
% 25.45/16.17  tff(c_1078, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_1075])).
% 25.45/16.17  tff(c_1084, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_1078])).
% 25.45/16.17  tff(c_1086, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_753, c_1084])).
% 25.45/16.17  tff(c_1087, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_243])).
% 25.45/16.17  tff(c_1092, plain, (![B_22]: (k7_relat_1('#skF_6', B_22)=k1_xboole_0 | ~r1_xboole_0(B_22, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1087, c_24])).
% 25.45/16.17  tff(c_1143, plain, (![B_357]: (k7_relat_1('#skF_6', B_357)=k1_xboole_0 | ~r1_xboole_0(B_357, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_1092])).
% 25.45/16.17  tff(c_1160, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | k9_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_750, c_1143])).
% 25.45/16.17  tff(c_1346, plain, (k9_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1160])).
% 25.45/16.17  tff(c_737, plain, (![A_18]: (k9_relat_1('#skF_5', A_18)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_18) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_726, c_20])).
% 25.45/16.17  tff(c_1219, plain, (![A_360]: (k9_relat_1('#skF_5', A_360)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_360))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_737])).
% 25.45/16.17  tff(c_1226, plain, (![B_24]: (k9_relat_1('#skF_5', B_24)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_24) | v1_xboole_0(B_24) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_1219])).
% 25.45/16.17  tff(c_1418, plain, (![B_383]: (k9_relat_1('#skF_5', B_383)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_383) | v1_xboole_0(B_383))), inference(negUnitSimplification, [status(thm)], [c_80, c_1226])).
% 25.45/16.17  tff(c_1421, plain, (k9_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_72, c_1418])).
% 25.45/16.17  tff(c_1425, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_1346, c_1421])).
% 25.45/16.17  tff(c_1427, plain, (k9_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1160])).
% 25.45/16.17  tff(c_1114, plain, (![A_355]: (r1_xboole_0('#skF_3', A_355) | k9_relat_1('#skF_5', A_355)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_122, c_740])).
% 25.45/16.17  tff(c_1129, plain, (![A_355]: (k3_xboole_0('#skF_3', A_355)=k1_xboole_0 | k9_relat_1('#skF_5', A_355)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_1114, c_2])).
% 25.45/16.17  tff(c_1463, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1427, c_1129])).
% 25.45/16.17  tff(c_1426, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1160])).
% 25.45/16.17  tff(c_1431, plain, (![B_13]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_3', B_13))=k7_relat_1(k1_xboole_0, B_13) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1426, c_14])).
% 25.45/16.17  tff(c_1480, plain, (![B_384]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_3', B_384))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_121, c_16, c_1431])).
% 25.45/16.17  tff(c_1495, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1463, c_1480])).
% 25.45/16.17  tff(c_1530, plain, (k9_relat_1('#skF_6', k1_xboole_0)=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1495, c_18])).
% 25.45/16.17  tff(c_1540, plain, (k9_relat_1('#skF_6', k1_xboole_0)=k2_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_121, c_1530])).
% 25.45/16.17  tff(c_1098, plain, (![A_18]: (k9_relat_1('#skF_6', A_18)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_18) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1087, c_20])).
% 25.45/16.17  tff(c_1130, plain, (![A_356]: (k9_relat_1('#skF_6', A_356)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_356))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_1098])).
% 25.45/16.17  tff(c_1142, plain, (![B_2]: (k9_relat_1('#skF_6', B_2)=k1_xboole_0 | k3_xboole_0('#skF_4', B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_1130])).
% 25.45/16.17  tff(c_1547, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | k3_xboole_0('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1540, c_1142])).
% 25.45/16.17  tff(c_1554, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1547])).
% 25.45/16.17  tff(c_1524, plain, (![B_13]: (k7_relat_1('#skF_6', k3_xboole_0(k1_xboole_0, B_13))=k7_relat_1(k1_xboole_0, B_13) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1495, c_14])).
% 25.45/16.17  tff(c_1602, plain, (![B_390]: (k7_relat_1('#skF_6', k3_xboole_0(k1_xboole_0, B_390))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_121, c_16, c_1524])).
% 25.45/16.17  tff(c_1613, plain, (![B_390]: (k9_relat_1('#skF_6', k3_xboole_0(k1_xboole_0, B_390))=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1602, c_18])).
% 25.45/16.17  tff(c_1627, plain, (![B_390]: (k9_relat_1('#skF_6', k3_xboole_0(k1_xboole_0, B_390))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_121, c_1554, c_1613])).
% 25.45/16.17  tff(c_1101, plain, (![A_18]: (r1_xboole_0('#skF_4', A_18) | k9_relat_1('#skF_6', A_18)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1087, c_22])).
% 25.45/16.17  tff(c_1166, plain, (![A_358]: (r1_xboole_0('#skF_4', A_358) | k9_relat_1('#skF_6', A_358)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_121, c_1101])).
% 25.45/16.17  tff(c_1709, plain, (![A_399]: (k3_xboole_0('#skF_4', A_399)=k1_xboole_0 | k9_relat_1('#skF_6', A_399)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_1166, c_2])).
% 25.45/16.17  tff(c_1726, plain, (![B_390]: (k3_xboole_0('#skF_4', k3_xboole_0(k1_xboole_0, B_390))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1627, c_1709])).
% 25.45/16.17  tff(c_1437, plain, (k9_relat_1('#skF_6', '#skF_3')=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1426, c_18])).
% 25.45/16.17  tff(c_1447, plain, (k9_relat_1('#skF_6', '#skF_3')=k2_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_121, c_1437])).
% 25.45/16.17  tff(c_1568, plain, (k9_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1554, c_1447])).
% 25.45/16.17  tff(c_1111, plain, (![A_18]: (r1_xboole_0('#skF_4', A_18) | k9_relat_1('#skF_6', A_18)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_121, c_1101])).
% 25.45/16.17  tff(c_731, plain, (![B_22]: (k7_relat_1('#skF_5', B_22)=k1_xboole_0 | ~r1_xboole_0(B_22, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_726, c_24])).
% 25.45/16.17  tff(c_1191, plain, (![B_359]: (k7_relat_1('#skF_5', B_359)=k1_xboole_0 | ~r1_xboole_0(B_359, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_731])).
% 25.45/16.17  tff(c_1212, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | k9_relat_1('#skF_6', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_1111, c_1191])).
% 25.45/16.17  tff(c_1774, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1568, c_1212])).
% 25.45/16.17  tff(c_1778, plain, (![B_13]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_4', B_13))=k7_relat_1(k1_xboole_0, B_13) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1774, c_14])).
% 25.45/16.17  tff(c_1798, plain, (![B_409]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_4', B_409))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_122, c_16, c_1778])).
% 25.45/16.17  tff(c_1810, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1726, c_1798])).
% 25.45/16.17  tff(c_1510, plain, (![A_385, B_386, C_387, D_388]: (k2_partfun1(A_385, B_386, C_387, D_388)=k7_relat_1(C_387, D_388) | ~m1_subset_1(C_387, k1_zfmisc_1(k2_zfmisc_1(A_385, B_386))) | ~v1_funct_1(C_387))), inference(cnfTransformation, [status(thm)], [f_115])).
% 25.45/16.17  tff(c_1514, plain, (![D_388]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_388)=k7_relat_1('#skF_5', D_388) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_66, c_1510])).
% 25.45/16.17  tff(c_1520, plain, (![D_388]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_388)=k7_relat_1('#skF_5', D_388))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1514])).
% 25.45/16.17  tff(c_1512, plain, (![D_388]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_388)=k7_relat_1('#skF_6', D_388) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_60, c_1510])).
% 25.45/16.17  tff(c_1517, plain, (![D_388]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_388)=k7_relat_1('#skF_6', D_388))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1512])).
% 25.45/16.17  tff(c_1236, plain, (![A_361, B_362, C_363]: (k9_subset_1(A_361, B_362, C_363)=k3_xboole_0(B_362, C_363) | ~m1_subset_1(C_363, k1_zfmisc_1(A_361)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 25.45/16.17  tff(c_1247, plain, (![B_362]: (k9_subset_1('#skF_1', B_362, '#skF_4')=k3_xboole_0(B_362, '#skF_4'))), inference(resolution, [status(thm)], [c_74, c_1236])).
% 25.45/16.17  tff(c_58, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_239])).
% 25.45/16.17  tff(c_123, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_58])).
% 25.45/16.17  tff(c_1249, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1247, c_1247, c_123])).
% 25.45/16.17  tff(c_4878, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1810, c_1520, c_1495, c_1517, c_1463, c_1463, c_1249])).
% 25.45/16.17  tff(c_4879, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_58])).
% 25.45/16.17  tff(c_4992, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_4879])).
% 25.45/16.17  tff(c_45126, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_45115, c_4992])).
% 25.45/16.17  tff(c_45140, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_6826, c_6419, c_5004, c_6436, c_5004, c_9716, c_45126])).
% 25.45/16.17  tff(c_45142, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_45140])).
% 25.45/16.17  tff(c_45143, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_4879])).
% 25.45/16.17  tff(c_45195, plain, (![B_1687, A_1688]: (k1_relat_1(B_1687)=A_1688 | ~v1_partfun1(B_1687, A_1688) | ~v4_relat_1(B_1687, A_1688) | ~v1_relat_1(B_1687))), inference(cnfTransformation, [status(thm)], [f_109])).
% 25.45/16.17  tff(c_45198, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_4919, c_45195])).
% 25.45/16.17  tff(c_45204, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_45198])).
% 25.45/16.17  tff(c_45208, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_45204])).
% 25.45/16.17  tff(c_46025, plain, (![C_1751, A_1752, B_1753]: (v1_partfun1(C_1751, A_1752) | ~v1_funct_2(C_1751, A_1752, B_1753) | ~v1_funct_1(C_1751) | ~m1_subset_1(C_1751, k1_zfmisc_1(k2_zfmisc_1(A_1752, B_1753))) | v1_xboole_0(B_1753))), inference(cnfTransformation, [status(thm)], [f_101])).
% 25.45/16.17  tff(c_46031, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_66, c_46025])).
% 25.45/16.17  tff(c_46038, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_46031])).
% 25.45/16.17  tff(c_46040, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_45208, c_46038])).
% 25.45/16.17  tff(c_46041, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_45204])).
% 25.45/16.17  tff(c_46052, plain, (![A_18]: (r1_xboole_0('#skF_3', A_18) | k9_relat_1('#skF_5', A_18)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_46041, c_22])).
% 25.45/16.17  tff(c_46624, plain, (![A_1795]: (r1_xboole_0('#skF_3', A_1795) | k9_relat_1('#skF_5', A_1795)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_122, c_46052])).
% 25.45/16.17  tff(c_45201, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_4918, c_45195])).
% 25.45/16.17  tff(c_45207, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_45201])).
% 25.45/16.17  tff(c_46072, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_45207])).
% 25.45/16.17  tff(c_46512, plain, (![C_1788, A_1789, B_1790]: (v1_partfun1(C_1788, A_1789) | ~v1_funct_2(C_1788, A_1789, B_1790) | ~v1_funct_1(C_1788) | ~m1_subset_1(C_1788, k1_zfmisc_1(k2_zfmisc_1(A_1789, B_1790))) | v1_xboole_0(B_1790))), inference(cnfTransformation, [status(thm)], [f_101])).
% 25.45/16.17  tff(c_46515, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_46512])).
% 25.45/16.17  tff(c_46521, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_46515])).
% 25.45/16.17  tff(c_46523, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_46072, c_46521])).
% 25.45/16.17  tff(c_46524, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_45207])).
% 25.45/16.17  tff(c_46529, plain, (![B_22]: (k7_relat_1('#skF_6', B_22)=k1_xboole_0 | ~r1_xboole_0(B_22, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_46524, c_24])).
% 25.45/16.17  tff(c_46542, plain, (![B_22]: (k7_relat_1('#skF_6', B_22)=k1_xboole_0 | ~r1_xboole_0(B_22, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_46529])).
% 25.45/16.17  tff(c_46642, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | k9_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_46624, c_46542])).
% 25.45/16.17  tff(c_46700, plain, (k9_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_46642])).
% 25.45/16.17  tff(c_46055, plain, (![A_18]: (k9_relat_1('#skF_5', A_18)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_18) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_46041, c_20])).
% 25.45/16.17  tff(c_46588, plain, (![A_1793]: (k9_relat_1('#skF_5', A_1793)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_1793))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_46055])).
% 25.45/16.17  tff(c_46592, plain, (![B_24]: (k9_relat_1('#skF_5', B_24)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_24) | v1_xboole_0(B_24) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_46588])).
% 25.45/16.17  tff(c_46907, plain, (![B_1815]: (k9_relat_1('#skF_5', B_1815)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_1815) | v1_xboole_0(B_1815))), inference(negUnitSimplification, [status(thm)], [c_80, c_46592])).
% 25.45/16.17  tff(c_46910, plain, (k9_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_72, c_46907])).
% 25.45/16.17  tff(c_46914, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_46700, c_46910])).
% 25.45/16.17  tff(c_46915, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_46642])).
% 25.45/16.17  tff(c_46920, plain, (![B_13]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_3', B_13))=k7_relat_1(k1_xboole_0, B_13) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_46915, c_14])).
% 25.45/16.17  tff(c_46927, plain, (![B_13]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_3', B_13))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_121, c_16, c_46920])).
% 25.45/16.17  tff(c_45145, plain, (![A_1680, B_1681, C_1682]: (k9_subset_1(A_1680, B_1681, C_1682)=k3_xboole_0(B_1681, C_1682) | ~m1_subset_1(C_1682, k1_zfmisc_1(A_1680)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 25.45/16.17  tff(c_45156, plain, (![B_1681]: (k9_subset_1('#skF_1', B_1681, '#skF_4')=k3_xboole_0(B_1681, '#skF_4'))), inference(resolution, [status(thm)], [c_74, c_45145])).
% 25.45/16.17  tff(c_46923, plain, (k9_relat_1('#skF_6', '#skF_3')=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_46915, c_18])).
% 25.45/16.17  tff(c_46929, plain, (k9_relat_1('#skF_6', '#skF_3')=k2_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_121, c_46923])).
% 25.45/16.17  tff(c_46535, plain, (![A_18]: (r1_xboole_0('#skF_4', A_18) | k9_relat_1('#skF_6', A_18)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_46524, c_22])).
% 25.45/16.17  tff(c_46555, plain, (![A_1791]: (r1_xboole_0('#skF_4', A_1791) | k9_relat_1('#skF_6', A_1791)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_121, c_46535])).
% 25.45/16.17  tff(c_47042, plain, (![A_1821]: (k3_xboole_0('#skF_4', A_1821)=k1_xboole_0 | k9_relat_1('#skF_6', A_1821)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_46555, c_2])).
% 25.45/16.17  tff(c_47054, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0 | k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_46929, c_47042])).
% 25.45/16.17  tff(c_47056, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_47054])).
% 25.45/16.17  tff(c_46538, plain, (![A_18]: (k9_relat_1('#skF_6', A_18)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_18) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_46524, c_20])).
% 25.45/16.17  tff(c_46571, plain, (![A_1792]: (k9_relat_1('#skF_6', A_1792)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_1792))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_46538])).
% 25.45/16.17  tff(c_47185, plain, (![B_1834]: (k9_relat_1('#skF_6', B_1834)=k1_xboole_0 | k3_xboole_0('#skF_4', B_1834)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_46571])).
% 25.45/16.17  tff(c_46916, plain, (k9_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_46642])).
% 25.45/16.17  tff(c_46648, plain, (![A_1795]: (k3_xboole_0('#skF_3', A_1795)=k1_xboole_0 | k9_relat_1('#skF_5', A_1795)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_46624, c_2])).
% 25.45/16.17  tff(c_46937, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_46916, c_46648])).
% 25.45/16.17  tff(c_46948, plain, (![B_1816]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_3', B_1816))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_121, c_16, c_46920])).
% 25.45/16.17  tff(c_46960, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_46937, c_46948])).
% 25.45/16.17  tff(c_46976, plain, (k9_relat_1('#skF_6', k1_xboole_0)=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_46960, c_18])).
% 25.45/16.17  tff(c_46982, plain, (k9_relat_1('#skF_6', k1_xboole_0)=k2_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_121, c_46976])).
% 25.45/16.17  tff(c_47203, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | k3_xboole_0('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_47185, c_46982])).
% 25.45/16.17  tff(c_47228, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6, c_47203])).
% 25.45/16.17  tff(c_47230, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47056, c_47228])).
% 25.45/16.17  tff(c_47232, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_47054])).
% 25.45/16.17  tff(c_46956, plain, (![B_1816]: (k9_relat_1('#skF_6', k3_xboole_0('#skF_3', B_1816))=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_46948, c_18])).
% 25.45/16.17  tff(c_46968, plain, (![B_1816]: (k9_relat_1('#skF_6', k3_xboole_0('#skF_3', B_1816))=k2_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_46956])).
% 25.45/16.17  tff(c_47270, plain, (![B_1836]: (k9_relat_1('#skF_6', k3_xboole_0('#skF_3', B_1836))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_47232, c_46968])).
% 25.45/16.17  tff(c_46570, plain, (![A_1791]: (k3_xboole_0('#skF_4', A_1791)=k1_xboole_0 | k9_relat_1('#skF_6', A_1791)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_46555, c_2])).
% 25.45/16.17  tff(c_47284, plain, (![B_1836]: (k3_xboole_0('#skF_4', k3_xboole_0('#skF_3', B_1836))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_47270, c_46570])).
% 25.45/16.17  tff(c_47243, plain, (k9_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_47232, c_46929])).
% 25.45/16.17  tff(c_46546, plain, (![A_18]: (r1_xboole_0('#skF_4', A_18) | k9_relat_1('#skF_6', A_18)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_121, c_46535])).
% 25.45/16.17  tff(c_46046, plain, (![B_22]: (k7_relat_1('#skF_5', B_22)=k1_xboole_0 | ~r1_xboole_0(B_22, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_46041, c_24])).
% 25.45/16.17  tff(c_46671, plain, (![B_1799]: (k7_relat_1('#skF_5', B_1799)=k1_xboole_0 | ~r1_xboole_0(B_1799, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_46046])).
% 25.45/16.17  tff(c_46693, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | k9_relat_1('#skF_6', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_46546, c_46671])).
% 25.45/16.17  tff(c_47430, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_47243, c_46693])).
% 25.45/16.17  tff(c_47434, plain, (![B_13]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_4', B_13))=k7_relat_1(k1_xboole_0, B_13) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_47430, c_14])).
% 25.45/16.17  tff(c_47445, plain, (![B_1851]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_4', B_1851))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_122, c_16, c_47434])).
% 25.45/16.17  tff(c_47459, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_47284, c_47445])).
% 25.45/16.17  tff(c_47288, plain, (![A_1837, B_1838, C_1839, D_1840]: (k2_partfun1(A_1837, B_1838, C_1839, D_1840)=k7_relat_1(C_1839, D_1840) | ~m1_subset_1(C_1839, k1_zfmisc_1(k2_zfmisc_1(A_1837, B_1838))) | ~v1_funct_1(C_1839))), inference(cnfTransformation, [status(thm)], [f_115])).
% 25.45/16.17  tff(c_47290, plain, (![D_1840]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_1840)=k7_relat_1('#skF_6', D_1840) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_60, c_47288])).
% 25.45/16.17  tff(c_47295, plain, (![D_1840]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_1840)=k7_relat_1('#skF_6', D_1840))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_47290])).
% 25.45/16.17  tff(c_47292, plain, (![D_1840]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_1840)=k7_relat_1('#skF_5', D_1840) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_66, c_47288])).
% 25.45/16.17  tff(c_47298, plain, (![D_1840]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_1840)=k7_relat_1('#skF_5', D_1840))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_47292])).
% 25.45/16.17  tff(c_47540, plain, (![B_1858, D_1857, E_1854, A_1859, F_1856, C_1855]: (v1_funct_1(k1_tmap_1(A_1859, B_1858, C_1855, D_1857, E_1854, F_1856)) | ~m1_subset_1(F_1856, k1_zfmisc_1(k2_zfmisc_1(D_1857, B_1858))) | ~v1_funct_2(F_1856, D_1857, B_1858) | ~v1_funct_1(F_1856) | ~m1_subset_1(E_1854, k1_zfmisc_1(k2_zfmisc_1(C_1855, B_1858))) | ~v1_funct_2(E_1854, C_1855, B_1858) | ~v1_funct_1(E_1854) | ~m1_subset_1(D_1857, k1_zfmisc_1(A_1859)) | v1_xboole_0(D_1857) | ~m1_subset_1(C_1855, k1_zfmisc_1(A_1859)) | v1_xboole_0(C_1855) | v1_xboole_0(B_1858) | v1_xboole_0(A_1859))), inference(cnfTransformation, [status(thm)], [f_197])).
% 25.45/16.17  tff(c_47542, plain, (![A_1859, C_1855, E_1854]: (v1_funct_1(k1_tmap_1(A_1859, '#skF_2', C_1855, '#skF_4', E_1854, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1854, k1_zfmisc_1(k2_zfmisc_1(C_1855, '#skF_2'))) | ~v1_funct_2(E_1854, C_1855, '#skF_2') | ~v1_funct_1(E_1854) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1859)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1855, k1_zfmisc_1(A_1859)) | v1_xboole_0(C_1855) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1859))), inference(resolution, [status(thm)], [c_60, c_47540])).
% 25.45/16.17  tff(c_47547, plain, (![A_1859, C_1855, E_1854]: (v1_funct_1(k1_tmap_1(A_1859, '#skF_2', C_1855, '#skF_4', E_1854, '#skF_6')) | ~m1_subset_1(E_1854, k1_zfmisc_1(k2_zfmisc_1(C_1855, '#skF_2'))) | ~v1_funct_2(E_1854, C_1855, '#skF_2') | ~v1_funct_1(E_1854) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1859)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1855, k1_zfmisc_1(A_1859)) | v1_xboole_0(C_1855) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1859))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_47542])).
% 25.45/16.17  tff(c_48470, plain, (![A_1915, C_1916, E_1917]: (v1_funct_1(k1_tmap_1(A_1915, '#skF_2', C_1916, '#skF_4', E_1917, '#skF_6')) | ~m1_subset_1(E_1917, k1_zfmisc_1(k2_zfmisc_1(C_1916, '#skF_2'))) | ~v1_funct_2(E_1917, C_1916, '#skF_2') | ~v1_funct_1(E_1917) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1915)) | ~m1_subset_1(C_1916, k1_zfmisc_1(A_1915)) | v1_xboole_0(C_1916) | v1_xboole_0(A_1915))), inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_47547])).
% 25.45/16.17  tff(c_48477, plain, (![A_1915]: (v1_funct_1(k1_tmap_1(A_1915, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1915)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1915)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1915))), inference(resolution, [status(thm)], [c_66, c_48470])).
% 25.45/16.17  tff(c_48487, plain, (![A_1915]: (v1_funct_1(k1_tmap_1(A_1915, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1915)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1915)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1915))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_48477])).
% 25.45/16.17  tff(c_49676, plain, (![A_1960]: (v1_funct_1(k1_tmap_1(A_1960, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1960)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1960)) | v1_xboole_0(A_1960))), inference(negUnitSimplification, [status(thm)], [c_80, c_48487])).
% 25.45/16.17  tff(c_49679, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_78, c_49676])).
% 25.45/16.17  tff(c_49682, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_49679])).
% 25.45/16.17  tff(c_49683, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_84, c_49682])).
% 25.45/16.17  tff(c_48726, plain, (![B_1925, E_1926, C_1924, A_1922, D_1923, F_1927]: (k2_partfun1(k4_subset_1(A_1922, C_1924, D_1923), B_1925, k1_tmap_1(A_1922, B_1925, C_1924, D_1923, E_1926, F_1927), C_1924)=E_1926 | ~m1_subset_1(k1_tmap_1(A_1922, B_1925, C_1924, D_1923, E_1926, F_1927), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1922, C_1924, D_1923), B_1925))) | ~v1_funct_2(k1_tmap_1(A_1922, B_1925, C_1924, D_1923, E_1926, F_1927), k4_subset_1(A_1922, C_1924, D_1923), B_1925) | ~v1_funct_1(k1_tmap_1(A_1922, B_1925, C_1924, D_1923, E_1926, F_1927)) | k2_partfun1(D_1923, B_1925, F_1927, k9_subset_1(A_1922, C_1924, D_1923))!=k2_partfun1(C_1924, B_1925, E_1926, k9_subset_1(A_1922, C_1924, D_1923)) | ~m1_subset_1(F_1927, k1_zfmisc_1(k2_zfmisc_1(D_1923, B_1925))) | ~v1_funct_2(F_1927, D_1923, B_1925) | ~v1_funct_1(F_1927) | ~m1_subset_1(E_1926, k1_zfmisc_1(k2_zfmisc_1(C_1924, B_1925))) | ~v1_funct_2(E_1926, C_1924, B_1925) | ~v1_funct_1(E_1926) | ~m1_subset_1(D_1923, k1_zfmisc_1(A_1922)) | v1_xboole_0(D_1923) | ~m1_subset_1(C_1924, k1_zfmisc_1(A_1922)) | v1_xboole_0(C_1924) | v1_xboole_0(B_1925) | v1_xboole_0(A_1922))), inference(cnfTransformation, [status(thm)], [f_163])).
% 25.45/16.17  tff(c_59149, plain, (![D_2303, E_2300, C_2301, F_2302, A_2305, B_2304]: (k2_partfun1(k4_subset_1(A_2305, C_2301, D_2303), B_2304, k1_tmap_1(A_2305, B_2304, C_2301, D_2303, E_2300, F_2302), C_2301)=E_2300 | ~v1_funct_2(k1_tmap_1(A_2305, B_2304, C_2301, D_2303, E_2300, F_2302), k4_subset_1(A_2305, C_2301, D_2303), B_2304) | ~v1_funct_1(k1_tmap_1(A_2305, B_2304, C_2301, D_2303, E_2300, F_2302)) | k2_partfun1(D_2303, B_2304, F_2302, k9_subset_1(A_2305, C_2301, D_2303))!=k2_partfun1(C_2301, B_2304, E_2300, k9_subset_1(A_2305, C_2301, D_2303)) | ~m1_subset_1(F_2302, k1_zfmisc_1(k2_zfmisc_1(D_2303, B_2304))) | ~v1_funct_2(F_2302, D_2303, B_2304) | ~v1_funct_1(F_2302) | ~m1_subset_1(E_2300, k1_zfmisc_1(k2_zfmisc_1(C_2301, B_2304))) | ~v1_funct_2(E_2300, C_2301, B_2304) | ~v1_funct_1(E_2300) | ~m1_subset_1(D_2303, k1_zfmisc_1(A_2305)) | v1_xboole_0(D_2303) | ~m1_subset_1(C_2301, k1_zfmisc_1(A_2305)) | v1_xboole_0(C_2301) | v1_xboole_0(B_2304) | v1_xboole_0(A_2305))), inference(resolution, [status(thm)], [c_52, c_48726])).
% 25.45/16.17  tff(c_81369, plain, (![B_2690, D_2689, A_2691, C_2687, F_2688, E_2686]: (k2_partfun1(k4_subset_1(A_2691, C_2687, D_2689), B_2690, k1_tmap_1(A_2691, B_2690, C_2687, D_2689, E_2686, F_2688), C_2687)=E_2686 | ~v1_funct_1(k1_tmap_1(A_2691, B_2690, C_2687, D_2689, E_2686, F_2688)) | k2_partfun1(D_2689, B_2690, F_2688, k9_subset_1(A_2691, C_2687, D_2689))!=k2_partfun1(C_2687, B_2690, E_2686, k9_subset_1(A_2691, C_2687, D_2689)) | ~m1_subset_1(F_2688, k1_zfmisc_1(k2_zfmisc_1(D_2689, B_2690))) | ~v1_funct_2(F_2688, D_2689, B_2690) | ~v1_funct_1(F_2688) | ~m1_subset_1(E_2686, k1_zfmisc_1(k2_zfmisc_1(C_2687, B_2690))) | ~v1_funct_2(E_2686, C_2687, B_2690) | ~v1_funct_1(E_2686) | ~m1_subset_1(D_2689, k1_zfmisc_1(A_2691)) | v1_xboole_0(D_2689) | ~m1_subset_1(C_2687, k1_zfmisc_1(A_2691)) | v1_xboole_0(C_2687) | v1_xboole_0(B_2690) | v1_xboole_0(A_2691))), inference(resolution, [status(thm)], [c_54, c_59149])).
% 25.45/16.17  tff(c_81373, plain, (![A_2691, C_2687, E_2686]: (k2_partfun1(k4_subset_1(A_2691, C_2687, '#skF_4'), '#skF_2', k1_tmap_1(A_2691, '#skF_2', C_2687, '#skF_4', E_2686, '#skF_6'), C_2687)=E_2686 | ~v1_funct_1(k1_tmap_1(A_2691, '#skF_2', C_2687, '#skF_4', E_2686, '#skF_6')) | k2_partfun1(C_2687, '#skF_2', E_2686, k9_subset_1(A_2691, C_2687, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_2691, C_2687, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_2686, k1_zfmisc_1(k2_zfmisc_1(C_2687, '#skF_2'))) | ~v1_funct_2(E_2686, C_2687, '#skF_2') | ~v1_funct_1(E_2686) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2691)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_2687, k1_zfmisc_1(A_2691)) | v1_xboole_0(C_2687) | v1_xboole_0('#skF_2') | v1_xboole_0(A_2691))), inference(resolution, [status(thm)], [c_60, c_81369])).
% 25.45/16.17  tff(c_81379, plain, (![A_2691, C_2687, E_2686]: (k2_partfun1(k4_subset_1(A_2691, C_2687, '#skF_4'), '#skF_2', k1_tmap_1(A_2691, '#skF_2', C_2687, '#skF_4', E_2686, '#skF_6'), C_2687)=E_2686 | ~v1_funct_1(k1_tmap_1(A_2691, '#skF_2', C_2687, '#skF_4', E_2686, '#skF_6')) | k2_partfun1(C_2687, '#skF_2', E_2686, k9_subset_1(A_2691, C_2687, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2691, C_2687, '#skF_4')) | ~m1_subset_1(E_2686, k1_zfmisc_1(k2_zfmisc_1(C_2687, '#skF_2'))) | ~v1_funct_2(E_2686, C_2687, '#skF_2') | ~v1_funct_1(E_2686) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2691)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_2687, k1_zfmisc_1(A_2691)) | v1_xboole_0(C_2687) | v1_xboole_0('#skF_2') | v1_xboole_0(A_2691))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_47295, c_81373])).
% 25.45/16.17  tff(c_81423, plain, (![A_2694, C_2695, E_2696]: (k2_partfun1(k4_subset_1(A_2694, C_2695, '#skF_4'), '#skF_2', k1_tmap_1(A_2694, '#skF_2', C_2695, '#skF_4', E_2696, '#skF_6'), C_2695)=E_2696 | ~v1_funct_1(k1_tmap_1(A_2694, '#skF_2', C_2695, '#skF_4', E_2696, '#skF_6')) | k2_partfun1(C_2695, '#skF_2', E_2696, k9_subset_1(A_2694, C_2695, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2694, C_2695, '#skF_4')) | ~m1_subset_1(E_2696, k1_zfmisc_1(k2_zfmisc_1(C_2695, '#skF_2'))) | ~v1_funct_2(E_2696, C_2695, '#skF_2') | ~v1_funct_1(E_2696) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2694)) | ~m1_subset_1(C_2695, k1_zfmisc_1(A_2694)) | v1_xboole_0(C_2695) | v1_xboole_0(A_2694))), inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_81379])).
% 25.45/16.17  tff(c_81430, plain, (![A_2694]: (k2_partfun1(k4_subset_1(A_2694, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_2694, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_2694, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_2694, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2694, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2694)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_2694)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2694))), inference(resolution, [status(thm)], [c_66, c_81423])).
% 25.45/16.17  tff(c_81440, plain, (![A_2694]: (k2_partfun1(k4_subset_1(A_2694, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_2694, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_2694, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_2694, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2694, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2694)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_2694)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2694))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_47298, c_81430])).
% 25.45/16.17  tff(c_84732, plain, (![A_2736]: (k2_partfun1(k4_subset_1(A_2736, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_2736, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_2736, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_2736, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2736, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2736)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_2736)) | v1_xboole_0(A_2736))), inference(negUnitSimplification, [status(thm)], [c_80, c_81440])).
% 25.45/16.17  tff(c_45144, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6'), inference(splitRight, [status(thm)], [c_4879])).
% 25.45/16.17  tff(c_49461, plain, (![A_1946, C_1948, G_1950, D_1947, B_1949]: (k1_tmap_1(A_1946, B_1949, C_1948, D_1947, k2_partfun1(k4_subset_1(A_1946, C_1948, D_1947), B_1949, G_1950, C_1948), k2_partfun1(k4_subset_1(A_1946, C_1948, D_1947), B_1949, G_1950, D_1947))=G_1950 | ~m1_subset_1(G_1950, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1946, C_1948, D_1947), B_1949))) | ~v1_funct_2(G_1950, k4_subset_1(A_1946, C_1948, D_1947), B_1949) | ~v1_funct_1(G_1950) | k2_partfun1(D_1947, B_1949, k2_partfun1(k4_subset_1(A_1946, C_1948, D_1947), B_1949, G_1950, D_1947), k9_subset_1(A_1946, C_1948, D_1947))!=k2_partfun1(C_1948, B_1949, k2_partfun1(k4_subset_1(A_1946, C_1948, D_1947), B_1949, G_1950, C_1948), k9_subset_1(A_1946, C_1948, D_1947)) | ~m1_subset_1(k2_partfun1(k4_subset_1(A_1946, C_1948, D_1947), B_1949, G_1950, D_1947), k1_zfmisc_1(k2_zfmisc_1(D_1947, B_1949))) | ~v1_funct_2(k2_partfun1(k4_subset_1(A_1946, C_1948, D_1947), B_1949, G_1950, D_1947), D_1947, B_1949) | ~v1_funct_1(k2_partfun1(k4_subset_1(A_1946, C_1948, D_1947), B_1949, G_1950, D_1947)) | ~m1_subset_1(k2_partfun1(k4_subset_1(A_1946, C_1948, D_1947), B_1949, G_1950, C_1948), k1_zfmisc_1(k2_zfmisc_1(C_1948, B_1949))) | ~v1_funct_2(k2_partfun1(k4_subset_1(A_1946, C_1948, D_1947), B_1949, G_1950, C_1948), C_1948, B_1949) | ~v1_funct_1(k2_partfun1(k4_subset_1(A_1946, C_1948, D_1947), B_1949, G_1950, C_1948)) | ~m1_subset_1(D_1947, k1_zfmisc_1(A_1946)) | v1_xboole_0(D_1947) | ~m1_subset_1(C_1948, k1_zfmisc_1(A_1946)) | v1_xboole_0(C_1948) | v1_xboole_0(B_1949) | v1_xboole_0(A_1946))), inference(cnfTransformation, [status(thm)], [f_163])).
% 25.45/16.17  tff(c_49463, plain, (k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4'))=k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6') | ~m1_subset_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2'))) | ~v1_funct_2(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4'), k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_2(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')) | ~m1_subset_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_45144, c_49461])).
% 25.45/16.17  tff(c_49465, plain, (k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_6')=k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6') | ~m1_subset_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2'))) | ~v1_funct_2(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k1_xboole_0)!=k1_xboole_0 | ~m1_subset_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')) | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_64, c_45144, c_62, c_45144, c_60, c_46960, c_47295, c_46937, c_45156, c_46937, c_45156, c_45144, c_45144, c_49463])).
% 25.45/16.17  tff(c_49466, plain, (k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_6')=k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6') | ~m1_subset_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2'))) | ~v1_funct_2(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k1_xboole_0)!=k1_xboole_0 | ~m1_subset_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_84, c_82, c_80, c_76, c_49465])).
% 25.45/16.17  tff(c_53017, plain, (k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_6')=k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6') | ~m1_subset_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2'))) | ~v1_funct_2(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | k2_partfun1('#skF_3', '#skF_2', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k1_xboole_0)!=k1_xboole_0 | ~m1_subset_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_49683, c_49466])).
% 25.45/16.17  tff(c_53018, plain, (~v1_funct_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_53017])).
% 25.45/16.17  tff(c_84741, plain, (~v1_funct_1('#skF_5') | ~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_84732, c_53018])).
% 25.45/16.17  tff(c_84754, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_47459, c_46927, c_45156, c_46937, c_45156, c_49683, c_70, c_84741])).
% 25.45/16.17  tff(c_84756, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_84754])).
% 25.45/16.17  tff(c_84757, plain, (~v1_funct_2(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | k2_partfun1('#skF_3', '#skF_2', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k1_xboole_0)!=k1_xboole_0 | ~v1_funct_2(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2'))) | k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_6')=k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_53017])).
% 25.45/16.17  tff(c_86845, plain, (~m1_subset_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2')))), inference(splitLeft, [status(thm)], [c_84757])).
% 25.45/16.17  tff(c_89738, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_52, c_86845])).
% 25.45/16.17  tff(c_89741, plain, (v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_70, c_68, c_66, c_64, c_62, c_60, c_89738])).
% 25.45/16.17  tff(c_89743, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_82, c_80, c_76, c_89741])).
% 25.45/16.17  tff(c_89745, plain, (m1_subset_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2')))), inference(splitRight, [status(thm)], [c_84757])).
% 25.45/16.17  tff(c_50, plain, (![C_137, A_41, D_153, B_105, F_165, E_161]: (k2_partfun1(k4_subset_1(A_41, C_137, D_153), B_105, k1_tmap_1(A_41, B_105, C_137, D_153, E_161, F_165), C_137)=E_161 | ~m1_subset_1(k1_tmap_1(A_41, B_105, C_137, D_153, E_161, F_165), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_41, C_137, D_153), B_105))) | ~v1_funct_2(k1_tmap_1(A_41, B_105, C_137, D_153, E_161, F_165), k4_subset_1(A_41, C_137, D_153), B_105) | ~v1_funct_1(k1_tmap_1(A_41, B_105, C_137, D_153, E_161, F_165)) | k2_partfun1(D_153, B_105, F_165, k9_subset_1(A_41, C_137, D_153))!=k2_partfun1(C_137, B_105, E_161, k9_subset_1(A_41, C_137, D_153)) | ~m1_subset_1(F_165, k1_zfmisc_1(k2_zfmisc_1(D_153, B_105))) | ~v1_funct_2(F_165, D_153, B_105) | ~v1_funct_1(F_165) | ~m1_subset_1(E_161, k1_zfmisc_1(k2_zfmisc_1(C_137, B_105))) | ~v1_funct_2(E_161, C_137, B_105) | ~v1_funct_1(E_161) | ~m1_subset_1(D_153, k1_zfmisc_1(A_41)) | v1_xboole_0(D_153) | ~m1_subset_1(C_137, k1_zfmisc_1(A_41)) | v1_xboole_0(C_137) | v1_xboole_0(B_105) | v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_163])).
% 25.45/16.17  tff(c_92463, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_2(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_89745, c_50])).
% 25.45/16.17  tff(c_92508, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_2(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_70, c_68, c_66, c_64, c_62, c_60, c_46927, c_45156, c_47459, c_46937, c_45156, c_47295, c_47298, c_49683, c_92463])).
% 25.45/16.17  tff(c_92509, plain, (~v1_funct_2(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_84, c_82, c_80, c_76, c_45143, c_92508])).
% 25.45/16.17  tff(c_92543, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_54, c_92509])).
% 25.45/16.17  tff(c_92546, plain, (v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_70, c_68, c_66, c_64, c_62, c_60, c_92543])).
% 25.45/16.17  tff(c_92548, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_82, c_80, c_76, c_92546])).
% 25.45/16.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 25.45/16.17  
% 25.45/16.17  Inference rules
% 25.45/16.17  ----------------------
% 25.45/16.17  #Ref     : 0
% 25.45/16.17  #Sup     : 22609
% 25.45/16.17  #Fact    : 0
% 25.45/16.17  #Define  : 0
% 25.45/16.17  #Split   : 55
% 25.45/16.17  #Chain   : 0
% 25.45/16.17  #Close   : 0
% 25.45/16.17  
% 25.45/16.17  Ordering : KBO
% 25.45/16.17  
% 25.45/16.17  Simplification rules
% 25.45/16.17  ----------------------
% 25.45/16.17  #Subsume      : 6655
% 25.45/16.17  #Demod        : 25826
% 25.45/16.17  #Tautology    : 11451
% 25.45/16.17  #SimpNegUnit  : 407
% 25.45/16.17  #BackRed      : 40
% 25.45/16.17  
% 25.45/16.17  #Partial instantiations: 0
% 25.45/16.17  #Strategies tried      : 1
% 25.45/16.17  
% 25.45/16.17  Timing (in seconds)
% 25.45/16.17  ----------------------
% 25.45/16.17  Preprocessing        : 0.43
% 25.45/16.17  Parsing              : 0.21
% 25.45/16.18  CNF conversion       : 0.06
% 25.45/16.18  Main loop            : 14.88
% 25.45/16.18  Inferencing          : 2.81
% 25.45/16.18  Reduction            : 8.31
% 25.45/16.18  Demodulation         : 7.31
% 25.45/16.18  BG Simplification    : 0.26
% 25.45/16.18  Subsumption          : 3.10
% 25.45/16.18  Abstraction          : 0.45
% 25.45/16.18  MUC search           : 0.00
% 25.45/16.18  Cooper               : 0.00
% 25.45/16.18  Total                : 15.43
% 25.45/16.18  Index Insertion      : 0.00
% 25.45/16.18  Index Deletion       : 0.00
% 25.45/16.18  Index Matching       : 0.00
% 25.45/16.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
