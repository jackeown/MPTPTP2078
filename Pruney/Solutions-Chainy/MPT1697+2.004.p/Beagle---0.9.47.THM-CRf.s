%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:08 EST 2020

% Result     : Theorem 8.23s
% Output     : CNFRefutation 8.44s
% Verified   : 
% Statistics : Number of formulae       :  191 ( 752 expanded)
%              Number of leaves         :   43 ( 291 expanded)
%              Depth                    :   13
%              Number of atoms          :  646 (3736 expanded)
%              Number of equality atoms :  132 ( 816 expanded)
%              Maximal formula depth    :   23 (   5 average)
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

tff(f_223,negated_conjecture,(
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

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_181,axiom,(
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

tff(f_99,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_147,axiom,(
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

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_397,plain,(
    ! [C_275,A_276,B_277] :
      ( v1_relat_1(C_275)
      | ~ m1_subset_1(C_275,k1_zfmisc_1(k2_zfmisc_1(A_276,B_277))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_405,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_397])).

tff(c_82,plain,(
    ! [B_224,A_225] : k3_xboole_0(B_224,A_225) = k3_xboole_0(A_225,B_224) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_98,plain,(
    ! [A_225] : k3_xboole_0(k1_xboole_0,A_225) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_8])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_445,plain,(
    ! [A_286,B_287] :
      ( k7_relat_1(A_286,B_287) = k1_xboole_0
      | ~ r1_xboole_0(B_287,k1_relat_1(A_286))
      | ~ v1_relat_1(A_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3170,plain,(
    ! [A_705,A_706] :
      ( k7_relat_1(A_705,A_706) = k1_xboole_0
      | ~ v1_relat_1(A_705)
      | k3_xboole_0(A_706,k1_relat_1(A_705)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_445])).

tff(c_3194,plain,(
    ! [A_707] :
      ( k7_relat_1(A_707,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_707) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_3170])).

tff(c_3201,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_405,c_3194])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_62,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_455,plain,(
    ! [A_288,B_289] :
      ( r1_xboole_0(A_288,B_289)
      | ~ r1_subset_1(A_288,B_289)
      | v1_xboole_0(B_289)
      | v1_xboole_0(A_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3235,plain,(
    ! [A_708,B_709] :
      ( k3_xboole_0(A_708,B_709) = k1_xboole_0
      | ~ r1_subset_1(A_708,B_709)
      | v1_xboole_0(B_709)
      | v1_xboole_0(A_708) ) ),
    inference(resolution,[status(thm)],[c_455,c_4])).

tff(c_3238,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_3235])).

tff(c_3240,plain,
    ( k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3238])).

tff(c_3241,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_66,c_3240])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_404,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_397])).

tff(c_3202,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_404,c_3194])).

tff(c_3079,plain,(
    ! [A_694,B_695,C_696] :
      ( k9_subset_1(A_694,B_695,C_696) = k3_xboole_0(B_695,C_696)
      | ~ m1_subset_1(C_696,k1_zfmisc_1(A_694)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3091,plain,(
    ! [B_695] : k9_subset_1('#skF_1',B_695,'#skF_4') = k3_xboole_0(B_695,'#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_3079])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_58,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_72,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_54,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_52,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_3442,plain,(
    ! [C_727,E_730,B_728,D_729,F_732,A_731] :
      ( v1_funct_1(k1_tmap_1(A_731,B_728,C_727,D_729,E_730,F_732))
      | ~ m1_subset_1(F_732,k1_zfmisc_1(k2_zfmisc_1(D_729,B_728)))
      | ~ v1_funct_2(F_732,D_729,B_728)
      | ~ v1_funct_1(F_732)
      | ~ m1_subset_1(E_730,k1_zfmisc_1(k2_zfmisc_1(C_727,B_728)))
      | ~ v1_funct_2(E_730,C_727,B_728)
      | ~ v1_funct_1(E_730)
      | ~ m1_subset_1(D_729,k1_zfmisc_1(A_731))
      | v1_xboole_0(D_729)
      | ~ m1_subset_1(C_727,k1_zfmisc_1(A_731))
      | v1_xboole_0(C_727)
      | v1_xboole_0(B_728)
      | v1_xboole_0(A_731) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_3446,plain,(
    ! [A_731,C_727,E_730] :
      ( v1_funct_1(k1_tmap_1(A_731,'#skF_2',C_727,'#skF_4',E_730,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_730,k1_zfmisc_1(k2_zfmisc_1(C_727,'#skF_2')))
      | ~ v1_funct_2(E_730,C_727,'#skF_2')
      | ~ v1_funct_1(E_730)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_731))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_727,k1_zfmisc_1(A_731))
      | v1_xboole_0(C_727)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_731) ) ),
    inference(resolution,[status(thm)],[c_50,c_3442])).

tff(c_3453,plain,(
    ! [A_731,C_727,E_730] :
      ( v1_funct_1(k1_tmap_1(A_731,'#skF_2',C_727,'#skF_4',E_730,'#skF_6'))
      | ~ m1_subset_1(E_730,k1_zfmisc_1(k2_zfmisc_1(C_727,'#skF_2')))
      | ~ v1_funct_2(E_730,C_727,'#skF_2')
      | ~ v1_funct_1(E_730)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_731))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_727,k1_zfmisc_1(A_731))
      | v1_xboole_0(C_727)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_731) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_3446])).

tff(c_3483,plain,(
    ! [A_738,C_739,E_740] :
      ( v1_funct_1(k1_tmap_1(A_738,'#skF_2',C_739,'#skF_4',E_740,'#skF_6'))
      | ~ m1_subset_1(E_740,k1_zfmisc_1(k2_zfmisc_1(C_739,'#skF_2')))
      | ~ v1_funct_2(E_740,C_739,'#skF_2')
      | ~ v1_funct_1(E_740)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_738))
      | ~ m1_subset_1(C_739,k1_zfmisc_1(A_738))
      | v1_xboole_0(C_739)
      | v1_xboole_0(A_738) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_3453])).

tff(c_3485,plain,(
    ! [A_738] :
      ( v1_funct_1(k1_tmap_1(A_738,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_738))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_738))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_738) ) ),
    inference(resolution,[status(thm)],[c_56,c_3483])).

tff(c_3490,plain,(
    ! [A_738] :
      ( v1_funct_1(k1_tmap_1(A_738,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_738))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_738))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_738) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_3485])).

tff(c_3503,plain,(
    ! [A_742] :
      ( v1_funct_1(k1_tmap_1(A_742,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_742))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_742))
      | v1_xboole_0(A_742) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_3490])).

tff(c_3506,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_3503])).

tff(c_3509,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_3506])).

tff(c_3510,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_3509])).

tff(c_3366,plain,(
    ! [A_716,B_717,C_718,D_719] :
      ( k2_partfun1(A_716,B_717,C_718,D_719) = k7_relat_1(C_718,D_719)
      | ~ m1_subset_1(C_718,k1_zfmisc_1(k2_zfmisc_1(A_716,B_717)))
      | ~ v1_funct_1(C_718) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_3368,plain,(
    ! [D_719] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_719) = k7_relat_1('#skF_5',D_719)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_3366])).

tff(c_3373,plain,(
    ! [D_719] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_719) = k7_relat_1('#skF_5',D_719) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_3368])).

tff(c_3370,plain,(
    ! [D_719] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_719) = k7_relat_1('#skF_6',D_719)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_50,c_3366])).

tff(c_3376,plain,(
    ! [D_719] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_719) = k7_relat_1('#skF_6',D_719) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3370])).

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
    inference(cnfTransformation,[status(thm)],[f_181])).

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
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_3616,plain,(
    ! [D_771,F_769,E_767,B_768,A_766,C_770] :
      ( k2_partfun1(k4_subset_1(A_766,C_770,D_771),B_768,k1_tmap_1(A_766,B_768,C_770,D_771,E_767,F_769),C_770) = E_767
      | ~ m1_subset_1(k1_tmap_1(A_766,B_768,C_770,D_771,E_767,F_769),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_766,C_770,D_771),B_768)))
      | ~ v1_funct_2(k1_tmap_1(A_766,B_768,C_770,D_771,E_767,F_769),k4_subset_1(A_766,C_770,D_771),B_768)
      | ~ v1_funct_1(k1_tmap_1(A_766,B_768,C_770,D_771,E_767,F_769))
      | k2_partfun1(D_771,B_768,F_769,k9_subset_1(A_766,C_770,D_771)) != k2_partfun1(C_770,B_768,E_767,k9_subset_1(A_766,C_770,D_771))
      | ~ m1_subset_1(F_769,k1_zfmisc_1(k2_zfmisc_1(D_771,B_768)))
      | ~ v1_funct_2(F_769,D_771,B_768)
      | ~ v1_funct_1(F_769)
      | ~ m1_subset_1(E_767,k1_zfmisc_1(k2_zfmisc_1(C_770,B_768)))
      | ~ v1_funct_2(E_767,C_770,B_768)
      | ~ v1_funct_1(E_767)
      | ~ m1_subset_1(D_771,k1_zfmisc_1(A_766))
      | v1_xboole_0(D_771)
      | ~ m1_subset_1(C_770,k1_zfmisc_1(A_766))
      | v1_xboole_0(C_770)
      | v1_xboole_0(B_768)
      | v1_xboole_0(A_766) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_4043,plain,(
    ! [B_877,A_880,D_878,C_876,F_881,E_879] :
      ( k2_partfun1(k4_subset_1(A_880,C_876,D_878),B_877,k1_tmap_1(A_880,B_877,C_876,D_878,E_879,F_881),C_876) = E_879
      | ~ v1_funct_2(k1_tmap_1(A_880,B_877,C_876,D_878,E_879,F_881),k4_subset_1(A_880,C_876,D_878),B_877)
      | ~ v1_funct_1(k1_tmap_1(A_880,B_877,C_876,D_878,E_879,F_881))
      | k2_partfun1(D_878,B_877,F_881,k9_subset_1(A_880,C_876,D_878)) != k2_partfun1(C_876,B_877,E_879,k9_subset_1(A_880,C_876,D_878))
      | ~ m1_subset_1(F_881,k1_zfmisc_1(k2_zfmisc_1(D_878,B_877)))
      | ~ v1_funct_2(F_881,D_878,B_877)
      | ~ v1_funct_1(F_881)
      | ~ m1_subset_1(E_879,k1_zfmisc_1(k2_zfmisc_1(C_876,B_877)))
      | ~ v1_funct_2(E_879,C_876,B_877)
      | ~ v1_funct_1(E_879)
      | ~ m1_subset_1(D_878,k1_zfmisc_1(A_880))
      | v1_xboole_0(D_878)
      | ~ m1_subset_1(C_876,k1_zfmisc_1(A_880))
      | v1_xboole_0(C_876)
      | v1_xboole_0(B_877)
      | v1_xboole_0(A_880) ) ),
    inference(resolution,[status(thm)],[c_42,c_3616])).

tff(c_4384,plain,(
    ! [A_940,F_941,D_938,C_936,E_939,B_937] :
      ( k2_partfun1(k4_subset_1(A_940,C_936,D_938),B_937,k1_tmap_1(A_940,B_937,C_936,D_938,E_939,F_941),C_936) = E_939
      | ~ v1_funct_1(k1_tmap_1(A_940,B_937,C_936,D_938,E_939,F_941))
      | k2_partfun1(D_938,B_937,F_941,k9_subset_1(A_940,C_936,D_938)) != k2_partfun1(C_936,B_937,E_939,k9_subset_1(A_940,C_936,D_938))
      | ~ m1_subset_1(F_941,k1_zfmisc_1(k2_zfmisc_1(D_938,B_937)))
      | ~ v1_funct_2(F_941,D_938,B_937)
      | ~ v1_funct_1(F_941)
      | ~ m1_subset_1(E_939,k1_zfmisc_1(k2_zfmisc_1(C_936,B_937)))
      | ~ v1_funct_2(E_939,C_936,B_937)
      | ~ v1_funct_1(E_939)
      | ~ m1_subset_1(D_938,k1_zfmisc_1(A_940))
      | v1_xboole_0(D_938)
      | ~ m1_subset_1(C_936,k1_zfmisc_1(A_940))
      | v1_xboole_0(C_936)
      | v1_xboole_0(B_937)
      | v1_xboole_0(A_940) ) ),
    inference(resolution,[status(thm)],[c_44,c_4043])).

tff(c_4390,plain,(
    ! [A_940,C_936,E_939] :
      ( k2_partfun1(k4_subset_1(A_940,C_936,'#skF_4'),'#skF_2',k1_tmap_1(A_940,'#skF_2',C_936,'#skF_4',E_939,'#skF_6'),C_936) = E_939
      | ~ v1_funct_1(k1_tmap_1(A_940,'#skF_2',C_936,'#skF_4',E_939,'#skF_6'))
      | k2_partfun1(C_936,'#skF_2',E_939,k9_subset_1(A_940,C_936,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_940,C_936,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_939,k1_zfmisc_1(k2_zfmisc_1(C_936,'#skF_2')))
      | ~ v1_funct_2(E_939,C_936,'#skF_2')
      | ~ v1_funct_1(E_939)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_940))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_936,k1_zfmisc_1(A_940))
      | v1_xboole_0(C_936)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_940) ) ),
    inference(resolution,[status(thm)],[c_50,c_4384])).

tff(c_4398,plain,(
    ! [A_940,C_936,E_939] :
      ( k2_partfun1(k4_subset_1(A_940,C_936,'#skF_4'),'#skF_2',k1_tmap_1(A_940,'#skF_2',C_936,'#skF_4',E_939,'#skF_6'),C_936) = E_939
      | ~ v1_funct_1(k1_tmap_1(A_940,'#skF_2',C_936,'#skF_4',E_939,'#skF_6'))
      | k2_partfun1(C_936,'#skF_2',E_939,k9_subset_1(A_940,C_936,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_940,C_936,'#skF_4'))
      | ~ m1_subset_1(E_939,k1_zfmisc_1(k2_zfmisc_1(C_936,'#skF_2')))
      | ~ v1_funct_2(E_939,C_936,'#skF_2')
      | ~ v1_funct_1(E_939)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_940))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_936,k1_zfmisc_1(A_940))
      | v1_xboole_0(C_936)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_940) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_3376,c_4390])).

tff(c_4574,plain,(
    ! [A_963,C_964,E_965] :
      ( k2_partfun1(k4_subset_1(A_963,C_964,'#skF_4'),'#skF_2',k1_tmap_1(A_963,'#skF_2',C_964,'#skF_4',E_965,'#skF_6'),C_964) = E_965
      | ~ v1_funct_1(k1_tmap_1(A_963,'#skF_2',C_964,'#skF_4',E_965,'#skF_6'))
      | k2_partfun1(C_964,'#skF_2',E_965,k9_subset_1(A_963,C_964,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_963,C_964,'#skF_4'))
      | ~ m1_subset_1(E_965,k1_zfmisc_1(k2_zfmisc_1(C_964,'#skF_2')))
      | ~ v1_funct_2(E_965,C_964,'#skF_2')
      | ~ v1_funct_1(E_965)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_963))
      | ~ m1_subset_1(C_964,k1_zfmisc_1(A_963))
      | v1_xboole_0(C_964)
      | v1_xboole_0(A_963) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_4398])).

tff(c_4579,plain,(
    ! [A_963] :
      ( k2_partfun1(k4_subset_1(A_963,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_963,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_963,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_963,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_963,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_963))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_963))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_963) ) ),
    inference(resolution,[status(thm)],[c_56,c_4574])).

tff(c_4587,plain,(
    ! [A_963] :
      ( k2_partfun1(k4_subset_1(A_963,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_963,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_963,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_963,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_963,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_963))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_963))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_963) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_3373,c_4579])).

tff(c_4673,plain,(
    ! [A_981] :
      ( k2_partfun1(k4_subset_1(A_981,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_981,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_981,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_981,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_981,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_981))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_981))
      | v1_xboole_0(A_981) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_4587])).

tff(c_1230,plain,(
    ! [A_386,B_387,C_388,D_389] :
      ( k2_partfun1(A_386,B_387,C_388,D_389) = k7_relat_1(C_388,D_389)
      | ~ m1_subset_1(C_388,k1_zfmisc_1(k2_zfmisc_1(A_386,B_387)))
      | ~ v1_funct_1(C_388) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1234,plain,(
    ! [D_389] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_389) = k7_relat_1('#skF_6',D_389)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_50,c_1230])).

tff(c_1240,plain,(
    ! [D_389] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_389) = k7_relat_1('#skF_6',D_389) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1234])).

tff(c_1232,plain,(
    ! [D_389] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_389) = k7_relat_1('#skF_5',D_389)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_1230])).

tff(c_1237,plain,(
    ! [D_389] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_389) = k7_relat_1('#skF_5',D_389) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1232])).

tff(c_1215,plain,(
    ! [A_384,B_385] :
      ( k3_xboole_0(A_384,B_385) = k1_xboole_0
      | ~ r1_subset_1(A_384,B_385)
      | v1_xboole_0(B_385)
      | v1_xboole_0(A_384) ) ),
    inference(resolution,[status(thm)],[c_455,c_4])).

tff(c_1221,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_1215])).

tff(c_1224,plain,
    ( k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1221])).

tff(c_1225,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_66,c_1224])).

tff(c_1130,plain,(
    ! [A_374,B_375,C_376] :
      ( k9_subset_1(A_374,B_375,C_376) = k3_xboole_0(B_375,C_376)
      | ~ m1_subset_1(C_376,k1_zfmisc_1(A_374)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1142,plain,(
    ! [B_375] : k9_subset_1('#skF_1',B_375,'#skF_4') = k3_xboole_0(B_375,'#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_1130])).

tff(c_172,plain,(
    ! [C_231,A_232,B_233] :
      ( v1_relat_1(C_231)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(A_232,B_233))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_179,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_172])).

tff(c_220,plain,(
    ! [A_242,B_243] :
      ( k7_relat_1(A_242,B_243) = k1_xboole_0
      | ~ r1_xboole_0(B_243,k1_relat_1(A_242))
      | ~ v1_relat_1(A_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_312,plain,(
    ! [A_258,A_259] :
      ( k7_relat_1(A_258,A_259) = k1_xboole_0
      | ~ v1_relat_1(A_258)
      | k3_xboole_0(A_259,k1_relat_1(A_258)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_220])).

tff(c_326,plain,(
    ! [A_260] :
      ( k7_relat_1(A_260,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_260) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_312])).

tff(c_334,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_179,c_326])).

tff(c_180,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_172])).

tff(c_333,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_180,c_326])).

tff(c_232,plain,(
    ! [A_247,B_248] :
      ( r1_xboole_0(A_247,B_248)
      | ~ r1_subset_1(A_247,B_248)
      | v1_xboole_0(B_248)
      | v1_xboole_0(A_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_374,plain,(
    ! [A_269,B_270] :
      ( k3_xboole_0(A_269,B_270) = k1_xboole_0
      | ~ r1_subset_1(A_269,B_270)
      | v1_xboole_0(B_270)
      | v1_xboole_0(A_269) ) ),
    inference(resolution,[status(thm)],[c_232,c_4])).

tff(c_380,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_374])).

tff(c_383,plain,
    ( k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_380])).

tff(c_384,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_66,c_383])).

tff(c_343,plain,(
    ! [A_261,B_262,C_263,D_264] :
      ( k2_partfun1(A_261,B_262,C_263,D_264) = k7_relat_1(C_263,D_264)
      | ~ m1_subset_1(C_263,k1_zfmisc_1(k2_zfmisc_1(A_261,B_262)))
      | ~ v1_funct_1(C_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_347,plain,(
    ! [D_264] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_264) = k7_relat_1('#skF_6',D_264)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_50,c_343])).

tff(c_353,plain,(
    ! [D_264] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_264) = k7_relat_1('#skF_6',D_264) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_347])).

tff(c_345,plain,(
    ! [D_264] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_264) = k7_relat_1('#skF_5',D_264)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_343])).

tff(c_350,plain,(
    ! [D_264] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_264) = k7_relat_1('#skF_5',D_264) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_345])).

tff(c_246,plain,(
    ! [A_249,B_250,C_251] :
      ( k9_subset_1(A_249,B_250,C_251) = k3_xboole_0(B_250,C_251)
      | ~ m1_subset_1(C_251,k1_zfmisc_1(A_249)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_258,plain,(
    ! [B_250] : k9_subset_1('#skF_1',B_250,'#skF_4') = k3_xboole_0(B_250,'#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_246])).

tff(c_48,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_165,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_268,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_258,c_165])).

tff(c_269,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_4','#skF_3')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_268])).

tff(c_373,plain,(
    k7_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3')) != k7_relat_1('#skF_6',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_350,c_269])).

tff(c_385,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) != k7_relat_1('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_384,c_384,c_373])).

tff(c_388,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_333,c_385])).

tff(c_390,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1152,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1142,c_1142,c_390])).

tff(c_1153,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_4','#skF_3')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_1152])).

tff(c_1283,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k7_relat_1('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1240,c_1237,c_1225,c_1225,c_1153])).

tff(c_436,plain,(
    ! [C_283,A_284,B_285] :
      ( v4_relat_1(C_283,A_284)
      | ~ m1_subset_1(C_283,k1_zfmisc_1(k2_zfmisc_1(A_284,B_285))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_443,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_436])).

tff(c_475,plain,(
    ! [B_293,A_294] :
      ( k1_relat_1(B_293) = A_294
      | ~ v1_partfun1(B_293,A_294)
      | ~ v4_relat_1(B_293,A_294)
      | ~ v1_relat_1(B_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_481,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_443,c_475])).

tff(c_487,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_481])).

tff(c_803,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_487])).

tff(c_1056,plain,(
    ! [C_366,A_367,B_368] :
      ( v1_partfun1(C_366,A_367)
      | ~ v1_funct_2(C_366,A_367,B_368)
      | ~ v1_funct_1(C_366)
      | ~ m1_subset_1(C_366,k1_zfmisc_1(k2_zfmisc_1(A_367,B_368)))
      | v1_xboole_0(B_368) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1059,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_1056])).

tff(c_1065,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1059])).

tff(c_1067,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_803,c_1065])).

tff(c_1068,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_487])).

tff(c_14,plain,(
    ! [A_12,B_14] :
      ( k7_relat_1(A_12,B_14) = k1_xboole_0
      | ~ r1_xboole_0(B_14,k1_relat_1(A_12))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1076,plain,(
    ! [B_14] :
      ( k7_relat_1('#skF_5',B_14) = k1_xboole_0
      | ~ r1_xboole_0(B_14,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1068,c_14])).

tff(c_1098,plain,(
    ! [B_370] :
      ( k7_relat_1('#skF_5',B_370) = k1_xboole_0
      | ~ r1_xboole_0(B_370,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_1076])).

tff(c_1110,plain,(
    ! [A_3] :
      ( k7_relat_1('#skF_5',A_3) = k1_xboole_0
      | k3_xboole_0(A_3,'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_1098])).

tff(c_1287,plain,
    ( k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0
    | k3_xboole_0(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1283,c_1110])).

tff(c_1294,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_1287])).

tff(c_1298,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1294,c_1283])).

tff(c_1452,plain,(
    ! [F_407,C_402,D_404,B_403,A_406,E_405] :
      ( v1_funct_1(k1_tmap_1(A_406,B_403,C_402,D_404,E_405,F_407))
      | ~ m1_subset_1(F_407,k1_zfmisc_1(k2_zfmisc_1(D_404,B_403)))
      | ~ v1_funct_2(F_407,D_404,B_403)
      | ~ v1_funct_1(F_407)
      | ~ m1_subset_1(E_405,k1_zfmisc_1(k2_zfmisc_1(C_402,B_403)))
      | ~ v1_funct_2(E_405,C_402,B_403)
      | ~ v1_funct_1(E_405)
      | ~ m1_subset_1(D_404,k1_zfmisc_1(A_406))
      | v1_xboole_0(D_404)
      | ~ m1_subset_1(C_402,k1_zfmisc_1(A_406))
      | v1_xboole_0(C_402)
      | v1_xboole_0(B_403)
      | v1_xboole_0(A_406) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_1456,plain,(
    ! [A_406,C_402,E_405] :
      ( v1_funct_1(k1_tmap_1(A_406,'#skF_2',C_402,'#skF_4',E_405,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_405,k1_zfmisc_1(k2_zfmisc_1(C_402,'#skF_2')))
      | ~ v1_funct_2(E_405,C_402,'#skF_2')
      | ~ v1_funct_1(E_405)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_406))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_402,k1_zfmisc_1(A_406))
      | v1_xboole_0(C_402)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_406) ) ),
    inference(resolution,[status(thm)],[c_50,c_1452])).

tff(c_1463,plain,(
    ! [A_406,C_402,E_405] :
      ( v1_funct_1(k1_tmap_1(A_406,'#skF_2',C_402,'#skF_4',E_405,'#skF_6'))
      | ~ m1_subset_1(E_405,k1_zfmisc_1(k2_zfmisc_1(C_402,'#skF_2')))
      | ~ v1_funct_2(E_405,C_402,'#skF_2')
      | ~ v1_funct_1(E_405)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_406))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_402,k1_zfmisc_1(A_406))
      | v1_xboole_0(C_402)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_406) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1456])).

tff(c_1483,plain,(
    ! [A_410,C_411,E_412] :
      ( v1_funct_1(k1_tmap_1(A_410,'#skF_2',C_411,'#skF_4',E_412,'#skF_6'))
      | ~ m1_subset_1(E_412,k1_zfmisc_1(k2_zfmisc_1(C_411,'#skF_2')))
      | ~ v1_funct_2(E_412,C_411,'#skF_2')
      | ~ v1_funct_1(E_412)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_410))
      | ~ m1_subset_1(C_411,k1_zfmisc_1(A_410))
      | v1_xboole_0(C_411)
      | v1_xboole_0(A_410) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_1463])).

tff(c_1485,plain,(
    ! [A_410] :
      ( v1_funct_1(k1_tmap_1(A_410,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_410))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_410))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_410) ) ),
    inference(resolution,[status(thm)],[c_56,c_1483])).

tff(c_1490,plain,(
    ! [A_410] :
      ( v1_funct_1(k1_tmap_1(A_410,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_410))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_410))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_410) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1485])).

tff(c_1503,plain,(
    ! [A_414] :
      ( v1_funct_1(k1_tmap_1(A_414,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_414))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_414))
      | v1_xboole_0(A_414) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1490])).

tff(c_1506,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_1503])).

tff(c_1509,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1506])).

tff(c_1510,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1509])).

tff(c_1682,plain,(
    ! [C_457,E_454,F_456,D_458,B_455,A_453] :
      ( k2_partfun1(k4_subset_1(A_453,C_457,D_458),B_455,k1_tmap_1(A_453,B_455,C_457,D_458,E_454,F_456),D_458) = F_456
      | ~ m1_subset_1(k1_tmap_1(A_453,B_455,C_457,D_458,E_454,F_456),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_453,C_457,D_458),B_455)))
      | ~ v1_funct_2(k1_tmap_1(A_453,B_455,C_457,D_458,E_454,F_456),k4_subset_1(A_453,C_457,D_458),B_455)
      | ~ v1_funct_1(k1_tmap_1(A_453,B_455,C_457,D_458,E_454,F_456))
      | k2_partfun1(D_458,B_455,F_456,k9_subset_1(A_453,C_457,D_458)) != k2_partfun1(C_457,B_455,E_454,k9_subset_1(A_453,C_457,D_458))
      | ~ m1_subset_1(F_456,k1_zfmisc_1(k2_zfmisc_1(D_458,B_455)))
      | ~ v1_funct_2(F_456,D_458,B_455)
      | ~ v1_funct_1(F_456)
      | ~ m1_subset_1(E_454,k1_zfmisc_1(k2_zfmisc_1(C_457,B_455)))
      | ~ v1_funct_2(E_454,C_457,B_455)
      | ~ v1_funct_1(E_454)
      | ~ m1_subset_1(D_458,k1_zfmisc_1(A_453))
      | v1_xboole_0(D_458)
      | ~ m1_subset_1(C_457,k1_zfmisc_1(A_453))
      | v1_xboole_0(C_457)
      | v1_xboole_0(B_455)
      | v1_xboole_0(A_453) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_2119,plain,(
    ! [D_572,F_575,B_571,A_574,C_570,E_573] :
      ( k2_partfun1(k4_subset_1(A_574,C_570,D_572),B_571,k1_tmap_1(A_574,B_571,C_570,D_572,E_573,F_575),D_572) = F_575
      | ~ v1_funct_2(k1_tmap_1(A_574,B_571,C_570,D_572,E_573,F_575),k4_subset_1(A_574,C_570,D_572),B_571)
      | ~ v1_funct_1(k1_tmap_1(A_574,B_571,C_570,D_572,E_573,F_575))
      | k2_partfun1(D_572,B_571,F_575,k9_subset_1(A_574,C_570,D_572)) != k2_partfun1(C_570,B_571,E_573,k9_subset_1(A_574,C_570,D_572))
      | ~ m1_subset_1(F_575,k1_zfmisc_1(k2_zfmisc_1(D_572,B_571)))
      | ~ v1_funct_2(F_575,D_572,B_571)
      | ~ v1_funct_1(F_575)
      | ~ m1_subset_1(E_573,k1_zfmisc_1(k2_zfmisc_1(C_570,B_571)))
      | ~ v1_funct_2(E_573,C_570,B_571)
      | ~ v1_funct_1(E_573)
      | ~ m1_subset_1(D_572,k1_zfmisc_1(A_574))
      | v1_xboole_0(D_572)
      | ~ m1_subset_1(C_570,k1_zfmisc_1(A_574))
      | v1_xboole_0(C_570)
      | v1_xboole_0(B_571)
      | v1_xboole_0(A_574) ) ),
    inference(resolution,[status(thm)],[c_42,c_1682])).

tff(c_2335,plain,(
    ! [C_604,B_605,E_607,F_609,A_608,D_606] :
      ( k2_partfun1(k4_subset_1(A_608,C_604,D_606),B_605,k1_tmap_1(A_608,B_605,C_604,D_606,E_607,F_609),D_606) = F_609
      | ~ v1_funct_1(k1_tmap_1(A_608,B_605,C_604,D_606,E_607,F_609))
      | k2_partfun1(D_606,B_605,F_609,k9_subset_1(A_608,C_604,D_606)) != k2_partfun1(C_604,B_605,E_607,k9_subset_1(A_608,C_604,D_606))
      | ~ m1_subset_1(F_609,k1_zfmisc_1(k2_zfmisc_1(D_606,B_605)))
      | ~ v1_funct_2(F_609,D_606,B_605)
      | ~ v1_funct_1(F_609)
      | ~ m1_subset_1(E_607,k1_zfmisc_1(k2_zfmisc_1(C_604,B_605)))
      | ~ v1_funct_2(E_607,C_604,B_605)
      | ~ v1_funct_1(E_607)
      | ~ m1_subset_1(D_606,k1_zfmisc_1(A_608))
      | v1_xboole_0(D_606)
      | ~ m1_subset_1(C_604,k1_zfmisc_1(A_608))
      | v1_xboole_0(C_604)
      | v1_xboole_0(B_605)
      | v1_xboole_0(A_608) ) ),
    inference(resolution,[status(thm)],[c_44,c_2119])).

tff(c_2341,plain,(
    ! [A_608,C_604,E_607] :
      ( k2_partfun1(k4_subset_1(A_608,C_604,'#skF_4'),'#skF_2',k1_tmap_1(A_608,'#skF_2',C_604,'#skF_4',E_607,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_608,'#skF_2',C_604,'#skF_4',E_607,'#skF_6'))
      | k2_partfun1(C_604,'#skF_2',E_607,k9_subset_1(A_608,C_604,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_608,C_604,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_607,k1_zfmisc_1(k2_zfmisc_1(C_604,'#skF_2')))
      | ~ v1_funct_2(E_607,C_604,'#skF_2')
      | ~ v1_funct_1(E_607)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_608))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_604,k1_zfmisc_1(A_608))
      | v1_xboole_0(C_604)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_608) ) ),
    inference(resolution,[status(thm)],[c_50,c_2335])).

tff(c_2349,plain,(
    ! [A_608,C_604,E_607] :
      ( k2_partfun1(k4_subset_1(A_608,C_604,'#skF_4'),'#skF_2',k1_tmap_1(A_608,'#skF_2',C_604,'#skF_4',E_607,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_608,'#skF_2',C_604,'#skF_4',E_607,'#skF_6'))
      | k2_partfun1(C_604,'#skF_2',E_607,k9_subset_1(A_608,C_604,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_608,C_604,'#skF_4'))
      | ~ m1_subset_1(E_607,k1_zfmisc_1(k2_zfmisc_1(C_604,'#skF_2')))
      | ~ v1_funct_2(E_607,C_604,'#skF_2')
      | ~ v1_funct_1(E_607)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_608))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_604,k1_zfmisc_1(A_608))
      | v1_xboole_0(C_604)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_608) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1240,c_2341])).

tff(c_2639,plain,(
    ! [A_655,C_656,E_657] :
      ( k2_partfun1(k4_subset_1(A_655,C_656,'#skF_4'),'#skF_2',k1_tmap_1(A_655,'#skF_2',C_656,'#skF_4',E_657,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_655,'#skF_2',C_656,'#skF_4',E_657,'#skF_6'))
      | k2_partfun1(C_656,'#skF_2',E_657,k9_subset_1(A_655,C_656,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_655,C_656,'#skF_4'))
      | ~ m1_subset_1(E_657,k1_zfmisc_1(k2_zfmisc_1(C_656,'#skF_2')))
      | ~ v1_funct_2(E_657,C_656,'#skF_2')
      | ~ v1_funct_1(E_657)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_655))
      | ~ m1_subset_1(C_656,k1_zfmisc_1(A_655))
      | v1_xboole_0(C_656)
      | v1_xboole_0(A_655) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_2349])).

tff(c_2644,plain,(
    ! [A_655] :
      ( k2_partfun1(k4_subset_1(A_655,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_655,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_655,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_655,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_655,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_655))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_655))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_655) ) ),
    inference(resolution,[status(thm)],[c_56,c_2639])).

tff(c_2652,plain,(
    ! [A_655] :
      ( k2_partfun1(k4_subset_1(A_655,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_655,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_655,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_655,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_655,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_655))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_655))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_655) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1237,c_2644])).

tff(c_2705,plain,(
    ! [A_660] :
      ( k2_partfun1(k4_subset_1(A_660,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_660,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_660,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_660,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_660,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_660))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_660))
      | v1_xboole_0(A_660) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_2652])).

tff(c_389,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_802,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_389])).

tff(c_2716,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2705,c_802])).

tff(c_2730,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_1294,c_1225,c_2,c_1298,c_1225,c_2,c_1142,c_1142,c_1510,c_2716])).

tff(c_2732,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2730])).

tff(c_2733,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_389])).

tff(c_4682,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4673,c_2733])).

tff(c_4693,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_3201,c_3241,c_2,c_3202,c_3241,c_2,c_3091,c_3091,c_3510,c_4682])).

tff(c_4695,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_4693])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:09:10 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.23/2.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.23/2.68  
% 8.23/2.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.23/2.69  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.23/2.69  
% 8.23/2.69  %Foreground sorts:
% 8.23/2.69  
% 8.23/2.69  
% 8.23/2.69  %Background operators:
% 8.23/2.69  
% 8.23/2.69  
% 8.23/2.69  %Foreground operators:
% 8.23/2.69  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 8.23/2.69  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.23/2.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.23/2.69  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.23/2.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.23/2.69  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 8.23/2.69  tff('#skF_5', type, '#skF_5': $i).
% 8.23/2.69  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.23/2.69  tff('#skF_6', type, '#skF_6': $i).
% 8.23/2.69  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.23/2.69  tff('#skF_2', type, '#skF_2': $i).
% 8.23/2.69  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 8.23/2.69  tff('#skF_3', type, '#skF_3': $i).
% 8.23/2.69  tff('#skF_1', type, '#skF_1': $i).
% 8.23/2.69  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.23/2.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.23/2.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.23/2.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.23/2.69  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.23/2.69  tff('#skF_4', type, '#skF_4': $i).
% 8.23/2.69  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.23/2.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.23/2.69  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 8.23/2.69  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.23/2.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.23/2.69  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.23/2.69  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.23/2.69  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 8.23/2.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.23/2.69  
% 8.44/2.72  tff(f_223, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 8.44/2.72  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.44/2.72  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.44/2.72  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 8.44/2.72  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.44/2.72  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 8.44/2.72  tff(f_61, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 8.44/2.72  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 8.44/2.72  tff(f_181, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 8.44/2.72  tff(f_99, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 8.44/2.72  tff(f_147, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 8.44/2.72  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.44/2.72  tff(f_93, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 8.44/2.72  tff(f_85, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 8.44/2.72  tff(c_74, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_223])).
% 8.44/2.72  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_223])).
% 8.44/2.72  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_223])).
% 8.44/2.72  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_223])).
% 8.44/2.72  tff(c_397, plain, (![C_275, A_276, B_277]: (v1_relat_1(C_275) | ~m1_subset_1(C_275, k1_zfmisc_1(k2_zfmisc_1(A_276, B_277))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.44/2.72  tff(c_405, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_397])).
% 8.44/2.72  tff(c_82, plain, (![B_224, A_225]: (k3_xboole_0(B_224, A_225)=k3_xboole_0(A_225, B_224))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.44/2.72  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.44/2.72  tff(c_98, plain, (![A_225]: (k3_xboole_0(k1_xboole_0, A_225)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_82, c_8])).
% 8.44/2.72  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.44/2.72  tff(c_445, plain, (![A_286, B_287]: (k7_relat_1(A_286, B_287)=k1_xboole_0 | ~r1_xboole_0(B_287, k1_relat_1(A_286)) | ~v1_relat_1(A_286))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.44/2.72  tff(c_3170, plain, (![A_705, A_706]: (k7_relat_1(A_705, A_706)=k1_xboole_0 | ~v1_relat_1(A_705) | k3_xboole_0(A_706, k1_relat_1(A_705))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_445])).
% 8.44/2.72  tff(c_3194, plain, (![A_707]: (k7_relat_1(A_707, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_707))), inference(superposition, [status(thm), theory('equality')], [c_98, c_3170])).
% 8.44/2.72  tff(c_3201, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_405, c_3194])).
% 8.44/2.72  tff(c_70, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_223])).
% 8.44/2.72  tff(c_66, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_223])).
% 8.44/2.72  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.44/2.72  tff(c_62, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_223])).
% 8.44/2.72  tff(c_455, plain, (![A_288, B_289]: (r1_xboole_0(A_288, B_289) | ~r1_subset_1(A_288, B_289) | v1_xboole_0(B_289) | v1_xboole_0(A_288))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.44/2.72  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.44/2.72  tff(c_3235, plain, (![A_708, B_709]: (k3_xboole_0(A_708, B_709)=k1_xboole_0 | ~r1_subset_1(A_708, B_709) | v1_xboole_0(B_709) | v1_xboole_0(A_708))), inference(resolution, [status(thm)], [c_455, c_4])).
% 8.44/2.72  tff(c_3238, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_62, c_3235])).
% 8.44/2.72  tff(c_3240, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_3238])).
% 8.44/2.72  tff(c_3241, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_70, c_66, c_3240])).
% 8.44/2.72  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_223])).
% 8.44/2.72  tff(c_404, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_397])).
% 8.44/2.72  tff(c_3202, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_404, c_3194])).
% 8.44/2.72  tff(c_3079, plain, (![A_694, B_695, C_696]: (k9_subset_1(A_694, B_695, C_696)=k3_xboole_0(B_695, C_696) | ~m1_subset_1(C_696, k1_zfmisc_1(A_694)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.44/2.72  tff(c_3091, plain, (![B_695]: (k9_subset_1('#skF_1', B_695, '#skF_4')=k3_xboole_0(B_695, '#skF_4'))), inference(resolution, [status(thm)], [c_64, c_3079])).
% 8.44/2.72  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_223])).
% 8.44/2.72  tff(c_58, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_223])).
% 8.44/2.72  tff(c_72, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_223])).
% 8.44/2.72  tff(c_54, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_223])).
% 8.44/2.72  tff(c_52, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_223])).
% 8.44/2.72  tff(c_3442, plain, (![C_727, E_730, B_728, D_729, F_732, A_731]: (v1_funct_1(k1_tmap_1(A_731, B_728, C_727, D_729, E_730, F_732)) | ~m1_subset_1(F_732, k1_zfmisc_1(k2_zfmisc_1(D_729, B_728))) | ~v1_funct_2(F_732, D_729, B_728) | ~v1_funct_1(F_732) | ~m1_subset_1(E_730, k1_zfmisc_1(k2_zfmisc_1(C_727, B_728))) | ~v1_funct_2(E_730, C_727, B_728) | ~v1_funct_1(E_730) | ~m1_subset_1(D_729, k1_zfmisc_1(A_731)) | v1_xboole_0(D_729) | ~m1_subset_1(C_727, k1_zfmisc_1(A_731)) | v1_xboole_0(C_727) | v1_xboole_0(B_728) | v1_xboole_0(A_731))), inference(cnfTransformation, [status(thm)], [f_181])).
% 8.44/2.72  tff(c_3446, plain, (![A_731, C_727, E_730]: (v1_funct_1(k1_tmap_1(A_731, '#skF_2', C_727, '#skF_4', E_730, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_730, k1_zfmisc_1(k2_zfmisc_1(C_727, '#skF_2'))) | ~v1_funct_2(E_730, C_727, '#skF_2') | ~v1_funct_1(E_730) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_731)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_727, k1_zfmisc_1(A_731)) | v1_xboole_0(C_727) | v1_xboole_0('#skF_2') | v1_xboole_0(A_731))), inference(resolution, [status(thm)], [c_50, c_3442])).
% 8.44/2.72  tff(c_3453, plain, (![A_731, C_727, E_730]: (v1_funct_1(k1_tmap_1(A_731, '#skF_2', C_727, '#skF_4', E_730, '#skF_6')) | ~m1_subset_1(E_730, k1_zfmisc_1(k2_zfmisc_1(C_727, '#skF_2'))) | ~v1_funct_2(E_730, C_727, '#skF_2') | ~v1_funct_1(E_730) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_731)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_727, k1_zfmisc_1(A_731)) | v1_xboole_0(C_727) | v1_xboole_0('#skF_2') | v1_xboole_0(A_731))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_3446])).
% 8.44/2.72  tff(c_3483, plain, (![A_738, C_739, E_740]: (v1_funct_1(k1_tmap_1(A_738, '#skF_2', C_739, '#skF_4', E_740, '#skF_6')) | ~m1_subset_1(E_740, k1_zfmisc_1(k2_zfmisc_1(C_739, '#skF_2'))) | ~v1_funct_2(E_740, C_739, '#skF_2') | ~v1_funct_1(E_740) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_738)) | ~m1_subset_1(C_739, k1_zfmisc_1(A_738)) | v1_xboole_0(C_739) | v1_xboole_0(A_738))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_3453])).
% 8.44/2.72  tff(c_3485, plain, (![A_738]: (v1_funct_1(k1_tmap_1(A_738, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_738)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_738)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_738))), inference(resolution, [status(thm)], [c_56, c_3483])).
% 8.44/2.72  tff(c_3490, plain, (![A_738]: (v1_funct_1(k1_tmap_1(A_738, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_738)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_738)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_738))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_3485])).
% 8.44/2.72  tff(c_3503, plain, (![A_742]: (v1_funct_1(k1_tmap_1(A_742, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_742)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_742)) | v1_xboole_0(A_742))), inference(negUnitSimplification, [status(thm)], [c_70, c_3490])).
% 8.44/2.72  tff(c_3506, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_68, c_3503])).
% 8.44/2.72  tff(c_3509, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_3506])).
% 8.44/2.72  tff(c_3510, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_74, c_3509])).
% 8.44/2.72  tff(c_3366, plain, (![A_716, B_717, C_718, D_719]: (k2_partfun1(A_716, B_717, C_718, D_719)=k7_relat_1(C_718, D_719) | ~m1_subset_1(C_718, k1_zfmisc_1(k2_zfmisc_1(A_716, B_717))) | ~v1_funct_1(C_718))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.44/2.72  tff(c_3368, plain, (![D_719]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_719)=k7_relat_1('#skF_5', D_719) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_3366])).
% 8.44/2.72  tff(c_3373, plain, (![D_719]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_719)=k7_relat_1('#skF_5', D_719))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_3368])).
% 8.44/2.72  tff(c_3370, plain, (![D_719]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_719)=k7_relat_1('#skF_6', D_719) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_50, c_3366])).
% 8.44/2.72  tff(c_3376, plain, (![D_719]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_719)=k7_relat_1('#skF_6', D_719))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3370])).
% 8.44/2.72  tff(c_44, plain, (![B_161, C_162, A_160, E_164, F_165, D_163]: (v1_funct_2(k1_tmap_1(A_160, B_161, C_162, D_163, E_164, F_165), k4_subset_1(A_160, C_162, D_163), B_161) | ~m1_subset_1(F_165, k1_zfmisc_1(k2_zfmisc_1(D_163, B_161))) | ~v1_funct_2(F_165, D_163, B_161) | ~v1_funct_1(F_165) | ~m1_subset_1(E_164, k1_zfmisc_1(k2_zfmisc_1(C_162, B_161))) | ~v1_funct_2(E_164, C_162, B_161) | ~v1_funct_1(E_164) | ~m1_subset_1(D_163, k1_zfmisc_1(A_160)) | v1_xboole_0(D_163) | ~m1_subset_1(C_162, k1_zfmisc_1(A_160)) | v1_xboole_0(C_162) | v1_xboole_0(B_161) | v1_xboole_0(A_160))), inference(cnfTransformation, [status(thm)], [f_181])).
% 8.44/2.72  tff(c_42, plain, (![B_161, C_162, A_160, E_164, F_165, D_163]: (m1_subset_1(k1_tmap_1(A_160, B_161, C_162, D_163, E_164, F_165), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_160, C_162, D_163), B_161))) | ~m1_subset_1(F_165, k1_zfmisc_1(k2_zfmisc_1(D_163, B_161))) | ~v1_funct_2(F_165, D_163, B_161) | ~v1_funct_1(F_165) | ~m1_subset_1(E_164, k1_zfmisc_1(k2_zfmisc_1(C_162, B_161))) | ~v1_funct_2(E_164, C_162, B_161) | ~v1_funct_1(E_164) | ~m1_subset_1(D_163, k1_zfmisc_1(A_160)) | v1_xboole_0(D_163) | ~m1_subset_1(C_162, k1_zfmisc_1(A_160)) | v1_xboole_0(C_162) | v1_xboole_0(B_161) | v1_xboole_0(A_160))), inference(cnfTransformation, [status(thm)], [f_181])).
% 8.44/2.72  tff(c_3616, plain, (![D_771, F_769, E_767, B_768, A_766, C_770]: (k2_partfun1(k4_subset_1(A_766, C_770, D_771), B_768, k1_tmap_1(A_766, B_768, C_770, D_771, E_767, F_769), C_770)=E_767 | ~m1_subset_1(k1_tmap_1(A_766, B_768, C_770, D_771, E_767, F_769), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_766, C_770, D_771), B_768))) | ~v1_funct_2(k1_tmap_1(A_766, B_768, C_770, D_771, E_767, F_769), k4_subset_1(A_766, C_770, D_771), B_768) | ~v1_funct_1(k1_tmap_1(A_766, B_768, C_770, D_771, E_767, F_769)) | k2_partfun1(D_771, B_768, F_769, k9_subset_1(A_766, C_770, D_771))!=k2_partfun1(C_770, B_768, E_767, k9_subset_1(A_766, C_770, D_771)) | ~m1_subset_1(F_769, k1_zfmisc_1(k2_zfmisc_1(D_771, B_768))) | ~v1_funct_2(F_769, D_771, B_768) | ~v1_funct_1(F_769) | ~m1_subset_1(E_767, k1_zfmisc_1(k2_zfmisc_1(C_770, B_768))) | ~v1_funct_2(E_767, C_770, B_768) | ~v1_funct_1(E_767) | ~m1_subset_1(D_771, k1_zfmisc_1(A_766)) | v1_xboole_0(D_771) | ~m1_subset_1(C_770, k1_zfmisc_1(A_766)) | v1_xboole_0(C_770) | v1_xboole_0(B_768) | v1_xboole_0(A_766))), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.44/2.72  tff(c_4043, plain, (![B_877, A_880, D_878, C_876, F_881, E_879]: (k2_partfun1(k4_subset_1(A_880, C_876, D_878), B_877, k1_tmap_1(A_880, B_877, C_876, D_878, E_879, F_881), C_876)=E_879 | ~v1_funct_2(k1_tmap_1(A_880, B_877, C_876, D_878, E_879, F_881), k4_subset_1(A_880, C_876, D_878), B_877) | ~v1_funct_1(k1_tmap_1(A_880, B_877, C_876, D_878, E_879, F_881)) | k2_partfun1(D_878, B_877, F_881, k9_subset_1(A_880, C_876, D_878))!=k2_partfun1(C_876, B_877, E_879, k9_subset_1(A_880, C_876, D_878)) | ~m1_subset_1(F_881, k1_zfmisc_1(k2_zfmisc_1(D_878, B_877))) | ~v1_funct_2(F_881, D_878, B_877) | ~v1_funct_1(F_881) | ~m1_subset_1(E_879, k1_zfmisc_1(k2_zfmisc_1(C_876, B_877))) | ~v1_funct_2(E_879, C_876, B_877) | ~v1_funct_1(E_879) | ~m1_subset_1(D_878, k1_zfmisc_1(A_880)) | v1_xboole_0(D_878) | ~m1_subset_1(C_876, k1_zfmisc_1(A_880)) | v1_xboole_0(C_876) | v1_xboole_0(B_877) | v1_xboole_0(A_880))), inference(resolution, [status(thm)], [c_42, c_3616])).
% 8.44/2.72  tff(c_4384, plain, (![A_940, F_941, D_938, C_936, E_939, B_937]: (k2_partfun1(k4_subset_1(A_940, C_936, D_938), B_937, k1_tmap_1(A_940, B_937, C_936, D_938, E_939, F_941), C_936)=E_939 | ~v1_funct_1(k1_tmap_1(A_940, B_937, C_936, D_938, E_939, F_941)) | k2_partfun1(D_938, B_937, F_941, k9_subset_1(A_940, C_936, D_938))!=k2_partfun1(C_936, B_937, E_939, k9_subset_1(A_940, C_936, D_938)) | ~m1_subset_1(F_941, k1_zfmisc_1(k2_zfmisc_1(D_938, B_937))) | ~v1_funct_2(F_941, D_938, B_937) | ~v1_funct_1(F_941) | ~m1_subset_1(E_939, k1_zfmisc_1(k2_zfmisc_1(C_936, B_937))) | ~v1_funct_2(E_939, C_936, B_937) | ~v1_funct_1(E_939) | ~m1_subset_1(D_938, k1_zfmisc_1(A_940)) | v1_xboole_0(D_938) | ~m1_subset_1(C_936, k1_zfmisc_1(A_940)) | v1_xboole_0(C_936) | v1_xboole_0(B_937) | v1_xboole_0(A_940))), inference(resolution, [status(thm)], [c_44, c_4043])).
% 8.44/2.72  tff(c_4390, plain, (![A_940, C_936, E_939]: (k2_partfun1(k4_subset_1(A_940, C_936, '#skF_4'), '#skF_2', k1_tmap_1(A_940, '#skF_2', C_936, '#skF_4', E_939, '#skF_6'), C_936)=E_939 | ~v1_funct_1(k1_tmap_1(A_940, '#skF_2', C_936, '#skF_4', E_939, '#skF_6')) | k2_partfun1(C_936, '#skF_2', E_939, k9_subset_1(A_940, C_936, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_940, C_936, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_939, k1_zfmisc_1(k2_zfmisc_1(C_936, '#skF_2'))) | ~v1_funct_2(E_939, C_936, '#skF_2') | ~v1_funct_1(E_939) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_940)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_936, k1_zfmisc_1(A_940)) | v1_xboole_0(C_936) | v1_xboole_0('#skF_2') | v1_xboole_0(A_940))), inference(resolution, [status(thm)], [c_50, c_4384])).
% 8.44/2.72  tff(c_4398, plain, (![A_940, C_936, E_939]: (k2_partfun1(k4_subset_1(A_940, C_936, '#skF_4'), '#skF_2', k1_tmap_1(A_940, '#skF_2', C_936, '#skF_4', E_939, '#skF_6'), C_936)=E_939 | ~v1_funct_1(k1_tmap_1(A_940, '#skF_2', C_936, '#skF_4', E_939, '#skF_6')) | k2_partfun1(C_936, '#skF_2', E_939, k9_subset_1(A_940, C_936, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_940, C_936, '#skF_4')) | ~m1_subset_1(E_939, k1_zfmisc_1(k2_zfmisc_1(C_936, '#skF_2'))) | ~v1_funct_2(E_939, C_936, '#skF_2') | ~v1_funct_1(E_939) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_940)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_936, k1_zfmisc_1(A_940)) | v1_xboole_0(C_936) | v1_xboole_0('#skF_2') | v1_xboole_0(A_940))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_3376, c_4390])).
% 8.44/2.72  tff(c_4574, plain, (![A_963, C_964, E_965]: (k2_partfun1(k4_subset_1(A_963, C_964, '#skF_4'), '#skF_2', k1_tmap_1(A_963, '#skF_2', C_964, '#skF_4', E_965, '#skF_6'), C_964)=E_965 | ~v1_funct_1(k1_tmap_1(A_963, '#skF_2', C_964, '#skF_4', E_965, '#skF_6')) | k2_partfun1(C_964, '#skF_2', E_965, k9_subset_1(A_963, C_964, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_963, C_964, '#skF_4')) | ~m1_subset_1(E_965, k1_zfmisc_1(k2_zfmisc_1(C_964, '#skF_2'))) | ~v1_funct_2(E_965, C_964, '#skF_2') | ~v1_funct_1(E_965) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_963)) | ~m1_subset_1(C_964, k1_zfmisc_1(A_963)) | v1_xboole_0(C_964) | v1_xboole_0(A_963))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_4398])).
% 8.44/2.72  tff(c_4579, plain, (![A_963]: (k2_partfun1(k4_subset_1(A_963, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_963, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_963, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_963, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_963, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_963)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_963)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_963))), inference(resolution, [status(thm)], [c_56, c_4574])).
% 8.44/2.72  tff(c_4587, plain, (![A_963]: (k2_partfun1(k4_subset_1(A_963, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_963, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_963, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_963, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_963, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_963)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_963)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_963))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_3373, c_4579])).
% 8.44/2.72  tff(c_4673, plain, (![A_981]: (k2_partfun1(k4_subset_1(A_981, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_981, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_981, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_981, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_981, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_981)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_981)) | v1_xboole_0(A_981))), inference(negUnitSimplification, [status(thm)], [c_70, c_4587])).
% 8.44/2.72  tff(c_1230, plain, (![A_386, B_387, C_388, D_389]: (k2_partfun1(A_386, B_387, C_388, D_389)=k7_relat_1(C_388, D_389) | ~m1_subset_1(C_388, k1_zfmisc_1(k2_zfmisc_1(A_386, B_387))) | ~v1_funct_1(C_388))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.44/2.72  tff(c_1234, plain, (![D_389]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_389)=k7_relat_1('#skF_6', D_389) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_50, c_1230])).
% 8.44/2.72  tff(c_1240, plain, (![D_389]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_389)=k7_relat_1('#skF_6', D_389))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1234])).
% 8.44/2.72  tff(c_1232, plain, (![D_389]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_389)=k7_relat_1('#skF_5', D_389) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_1230])).
% 8.44/2.72  tff(c_1237, plain, (![D_389]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_389)=k7_relat_1('#skF_5', D_389))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1232])).
% 8.44/2.72  tff(c_1215, plain, (![A_384, B_385]: (k3_xboole_0(A_384, B_385)=k1_xboole_0 | ~r1_subset_1(A_384, B_385) | v1_xboole_0(B_385) | v1_xboole_0(A_384))), inference(resolution, [status(thm)], [c_455, c_4])).
% 8.44/2.72  tff(c_1221, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_62, c_1215])).
% 8.44/2.72  tff(c_1224, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1221])).
% 8.44/2.72  tff(c_1225, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_70, c_66, c_1224])).
% 8.44/2.72  tff(c_1130, plain, (![A_374, B_375, C_376]: (k9_subset_1(A_374, B_375, C_376)=k3_xboole_0(B_375, C_376) | ~m1_subset_1(C_376, k1_zfmisc_1(A_374)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.44/2.72  tff(c_1142, plain, (![B_375]: (k9_subset_1('#skF_1', B_375, '#skF_4')=k3_xboole_0(B_375, '#skF_4'))), inference(resolution, [status(thm)], [c_64, c_1130])).
% 8.44/2.72  tff(c_172, plain, (![C_231, A_232, B_233]: (v1_relat_1(C_231) | ~m1_subset_1(C_231, k1_zfmisc_1(k2_zfmisc_1(A_232, B_233))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.44/2.72  tff(c_179, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_172])).
% 8.44/2.72  tff(c_220, plain, (![A_242, B_243]: (k7_relat_1(A_242, B_243)=k1_xboole_0 | ~r1_xboole_0(B_243, k1_relat_1(A_242)) | ~v1_relat_1(A_242))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.44/2.72  tff(c_312, plain, (![A_258, A_259]: (k7_relat_1(A_258, A_259)=k1_xboole_0 | ~v1_relat_1(A_258) | k3_xboole_0(A_259, k1_relat_1(A_258))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_220])).
% 8.44/2.72  tff(c_326, plain, (![A_260]: (k7_relat_1(A_260, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_260))), inference(superposition, [status(thm), theory('equality')], [c_98, c_312])).
% 8.44/2.72  tff(c_334, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_179, c_326])).
% 8.44/2.72  tff(c_180, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_172])).
% 8.44/2.72  tff(c_333, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_180, c_326])).
% 8.44/2.72  tff(c_232, plain, (![A_247, B_248]: (r1_xboole_0(A_247, B_248) | ~r1_subset_1(A_247, B_248) | v1_xboole_0(B_248) | v1_xboole_0(A_247))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.44/2.72  tff(c_374, plain, (![A_269, B_270]: (k3_xboole_0(A_269, B_270)=k1_xboole_0 | ~r1_subset_1(A_269, B_270) | v1_xboole_0(B_270) | v1_xboole_0(A_269))), inference(resolution, [status(thm)], [c_232, c_4])).
% 8.44/2.72  tff(c_380, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_62, c_374])).
% 8.44/2.72  tff(c_383, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_380])).
% 8.44/2.72  tff(c_384, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_70, c_66, c_383])).
% 8.44/2.72  tff(c_343, plain, (![A_261, B_262, C_263, D_264]: (k2_partfun1(A_261, B_262, C_263, D_264)=k7_relat_1(C_263, D_264) | ~m1_subset_1(C_263, k1_zfmisc_1(k2_zfmisc_1(A_261, B_262))) | ~v1_funct_1(C_263))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.44/2.72  tff(c_347, plain, (![D_264]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_264)=k7_relat_1('#skF_6', D_264) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_50, c_343])).
% 8.44/2.72  tff(c_353, plain, (![D_264]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_264)=k7_relat_1('#skF_6', D_264))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_347])).
% 8.44/2.72  tff(c_345, plain, (![D_264]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_264)=k7_relat_1('#skF_5', D_264) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_343])).
% 8.44/2.72  tff(c_350, plain, (![D_264]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_264)=k7_relat_1('#skF_5', D_264))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_345])).
% 8.44/2.72  tff(c_246, plain, (![A_249, B_250, C_251]: (k9_subset_1(A_249, B_250, C_251)=k3_xboole_0(B_250, C_251) | ~m1_subset_1(C_251, k1_zfmisc_1(A_249)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.44/2.72  tff(c_258, plain, (![B_250]: (k9_subset_1('#skF_1', B_250, '#skF_4')=k3_xboole_0(B_250, '#skF_4'))), inference(resolution, [status(thm)], [c_64, c_246])).
% 8.44/2.72  tff(c_48, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_223])).
% 8.44/2.72  tff(c_165, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_48])).
% 8.44/2.72  tff(c_268, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_258, c_258, c_165])).
% 8.44/2.72  tff(c_269, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_4', '#skF_3'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_268])).
% 8.44/2.72  tff(c_373, plain, (k7_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3'))!=k7_relat_1('#skF_6', k3_xboole_0('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_353, c_350, c_269])).
% 8.44/2.72  tff(c_385, plain, (k7_relat_1('#skF_5', k1_xboole_0)!=k7_relat_1('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_384, c_384, c_373])).
% 8.44/2.72  tff(c_388, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_334, c_333, c_385])).
% 8.44/2.72  tff(c_390, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_48])).
% 8.44/2.72  tff(c_1152, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1142, c_1142, c_390])).
% 8.44/2.72  tff(c_1153, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_4', '#skF_3'))=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_1152])).
% 8.44/2.72  tff(c_1283, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k7_relat_1('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1240, c_1237, c_1225, c_1225, c_1153])).
% 8.44/2.72  tff(c_436, plain, (![C_283, A_284, B_285]: (v4_relat_1(C_283, A_284) | ~m1_subset_1(C_283, k1_zfmisc_1(k2_zfmisc_1(A_284, B_285))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.44/2.72  tff(c_443, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_436])).
% 8.44/2.72  tff(c_475, plain, (![B_293, A_294]: (k1_relat_1(B_293)=A_294 | ~v1_partfun1(B_293, A_294) | ~v4_relat_1(B_293, A_294) | ~v1_relat_1(B_293))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.44/2.72  tff(c_481, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_443, c_475])).
% 8.44/2.72  tff(c_487, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_404, c_481])).
% 8.44/2.72  tff(c_803, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_487])).
% 8.44/2.72  tff(c_1056, plain, (![C_366, A_367, B_368]: (v1_partfun1(C_366, A_367) | ~v1_funct_2(C_366, A_367, B_368) | ~v1_funct_1(C_366) | ~m1_subset_1(C_366, k1_zfmisc_1(k2_zfmisc_1(A_367, B_368))) | v1_xboole_0(B_368))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.44/2.72  tff(c_1059, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_56, c_1056])).
% 8.44/2.72  tff(c_1065, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1059])).
% 8.44/2.72  tff(c_1067, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_803, c_1065])).
% 8.44/2.72  tff(c_1068, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_487])).
% 8.44/2.72  tff(c_14, plain, (![A_12, B_14]: (k7_relat_1(A_12, B_14)=k1_xboole_0 | ~r1_xboole_0(B_14, k1_relat_1(A_12)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.44/2.72  tff(c_1076, plain, (![B_14]: (k7_relat_1('#skF_5', B_14)=k1_xboole_0 | ~r1_xboole_0(B_14, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1068, c_14])).
% 8.44/2.72  tff(c_1098, plain, (![B_370]: (k7_relat_1('#skF_5', B_370)=k1_xboole_0 | ~r1_xboole_0(B_370, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_404, c_1076])).
% 8.44/2.72  tff(c_1110, plain, (![A_3]: (k7_relat_1('#skF_5', A_3)=k1_xboole_0 | k3_xboole_0(A_3, '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_1098])).
% 8.44/2.72  tff(c_1287, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0 | k3_xboole_0(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1283, c_1110])).
% 8.44/2.72  tff(c_1294, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_98, c_1287])).
% 8.44/2.72  tff(c_1298, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1294, c_1283])).
% 8.44/2.72  tff(c_1452, plain, (![F_407, C_402, D_404, B_403, A_406, E_405]: (v1_funct_1(k1_tmap_1(A_406, B_403, C_402, D_404, E_405, F_407)) | ~m1_subset_1(F_407, k1_zfmisc_1(k2_zfmisc_1(D_404, B_403))) | ~v1_funct_2(F_407, D_404, B_403) | ~v1_funct_1(F_407) | ~m1_subset_1(E_405, k1_zfmisc_1(k2_zfmisc_1(C_402, B_403))) | ~v1_funct_2(E_405, C_402, B_403) | ~v1_funct_1(E_405) | ~m1_subset_1(D_404, k1_zfmisc_1(A_406)) | v1_xboole_0(D_404) | ~m1_subset_1(C_402, k1_zfmisc_1(A_406)) | v1_xboole_0(C_402) | v1_xboole_0(B_403) | v1_xboole_0(A_406))), inference(cnfTransformation, [status(thm)], [f_181])).
% 8.44/2.72  tff(c_1456, plain, (![A_406, C_402, E_405]: (v1_funct_1(k1_tmap_1(A_406, '#skF_2', C_402, '#skF_4', E_405, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_405, k1_zfmisc_1(k2_zfmisc_1(C_402, '#skF_2'))) | ~v1_funct_2(E_405, C_402, '#skF_2') | ~v1_funct_1(E_405) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_406)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_402, k1_zfmisc_1(A_406)) | v1_xboole_0(C_402) | v1_xboole_0('#skF_2') | v1_xboole_0(A_406))), inference(resolution, [status(thm)], [c_50, c_1452])).
% 8.44/2.72  tff(c_1463, plain, (![A_406, C_402, E_405]: (v1_funct_1(k1_tmap_1(A_406, '#skF_2', C_402, '#skF_4', E_405, '#skF_6')) | ~m1_subset_1(E_405, k1_zfmisc_1(k2_zfmisc_1(C_402, '#skF_2'))) | ~v1_funct_2(E_405, C_402, '#skF_2') | ~v1_funct_1(E_405) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_406)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_402, k1_zfmisc_1(A_406)) | v1_xboole_0(C_402) | v1_xboole_0('#skF_2') | v1_xboole_0(A_406))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1456])).
% 8.44/2.72  tff(c_1483, plain, (![A_410, C_411, E_412]: (v1_funct_1(k1_tmap_1(A_410, '#skF_2', C_411, '#skF_4', E_412, '#skF_6')) | ~m1_subset_1(E_412, k1_zfmisc_1(k2_zfmisc_1(C_411, '#skF_2'))) | ~v1_funct_2(E_412, C_411, '#skF_2') | ~v1_funct_1(E_412) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_410)) | ~m1_subset_1(C_411, k1_zfmisc_1(A_410)) | v1_xboole_0(C_411) | v1_xboole_0(A_410))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_1463])).
% 8.44/2.72  tff(c_1485, plain, (![A_410]: (v1_funct_1(k1_tmap_1(A_410, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_410)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_410)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_410))), inference(resolution, [status(thm)], [c_56, c_1483])).
% 8.44/2.72  tff(c_1490, plain, (![A_410]: (v1_funct_1(k1_tmap_1(A_410, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_410)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_410)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_410))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1485])).
% 8.44/2.72  tff(c_1503, plain, (![A_414]: (v1_funct_1(k1_tmap_1(A_414, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_414)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_414)) | v1_xboole_0(A_414))), inference(negUnitSimplification, [status(thm)], [c_70, c_1490])).
% 8.44/2.72  tff(c_1506, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_68, c_1503])).
% 8.44/2.72  tff(c_1509, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1506])).
% 8.44/2.72  tff(c_1510, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_74, c_1509])).
% 8.44/2.72  tff(c_1682, plain, (![C_457, E_454, F_456, D_458, B_455, A_453]: (k2_partfun1(k4_subset_1(A_453, C_457, D_458), B_455, k1_tmap_1(A_453, B_455, C_457, D_458, E_454, F_456), D_458)=F_456 | ~m1_subset_1(k1_tmap_1(A_453, B_455, C_457, D_458, E_454, F_456), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_453, C_457, D_458), B_455))) | ~v1_funct_2(k1_tmap_1(A_453, B_455, C_457, D_458, E_454, F_456), k4_subset_1(A_453, C_457, D_458), B_455) | ~v1_funct_1(k1_tmap_1(A_453, B_455, C_457, D_458, E_454, F_456)) | k2_partfun1(D_458, B_455, F_456, k9_subset_1(A_453, C_457, D_458))!=k2_partfun1(C_457, B_455, E_454, k9_subset_1(A_453, C_457, D_458)) | ~m1_subset_1(F_456, k1_zfmisc_1(k2_zfmisc_1(D_458, B_455))) | ~v1_funct_2(F_456, D_458, B_455) | ~v1_funct_1(F_456) | ~m1_subset_1(E_454, k1_zfmisc_1(k2_zfmisc_1(C_457, B_455))) | ~v1_funct_2(E_454, C_457, B_455) | ~v1_funct_1(E_454) | ~m1_subset_1(D_458, k1_zfmisc_1(A_453)) | v1_xboole_0(D_458) | ~m1_subset_1(C_457, k1_zfmisc_1(A_453)) | v1_xboole_0(C_457) | v1_xboole_0(B_455) | v1_xboole_0(A_453))), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.44/2.72  tff(c_2119, plain, (![D_572, F_575, B_571, A_574, C_570, E_573]: (k2_partfun1(k4_subset_1(A_574, C_570, D_572), B_571, k1_tmap_1(A_574, B_571, C_570, D_572, E_573, F_575), D_572)=F_575 | ~v1_funct_2(k1_tmap_1(A_574, B_571, C_570, D_572, E_573, F_575), k4_subset_1(A_574, C_570, D_572), B_571) | ~v1_funct_1(k1_tmap_1(A_574, B_571, C_570, D_572, E_573, F_575)) | k2_partfun1(D_572, B_571, F_575, k9_subset_1(A_574, C_570, D_572))!=k2_partfun1(C_570, B_571, E_573, k9_subset_1(A_574, C_570, D_572)) | ~m1_subset_1(F_575, k1_zfmisc_1(k2_zfmisc_1(D_572, B_571))) | ~v1_funct_2(F_575, D_572, B_571) | ~v1_funct_1(F_575) | ~m1_subset_1(E_573, k1_zfmisc_1(k2_zfmisc_1(C_570, B_571))) | ~v1_funct_2(E_573, C_570, B_571) | ~v1_funct_1(E_573) | ~m1_subset_1(D_572, k1_zfmisc_1(A_574)) | v1_xboole_0(D_572) | ~m1_subset_1(C_570, k1_zfmisc_1(A_574)) | v1_xboole_0(C_570) | v1_xboole_0(B_571) | v1_xboole_0(A_574))), inference(resolution, [status(thm)], [c_42, c_1682])).
% 8.44/2.72  tff(c_2335, plain, (![C_604, B_605, E_607, F_609, A_608, D_606]: (k2_partfun1(k4_subset_1(A_608, C_604, D_606), B_605, k1_tmap_1(A_608, B_605, C_604, D_606, E_607, F_609), D_606)=F_609 | ~v1_funct_1(k1_tmap_1(A_608, B_605, C_604, D_606, E_607, F_609)) | k2_partfun1(D_606, B_605, F_609, k9_subset_1(A_608, C_604, D_606))!=k2_partfun1(C_604, B_605, E_607, k9_subset_1(A_608, C_604, D_606)) | ~m1_subset_1(F_609, k1_zfmisc_1(k2_zfmisc_1(D_606, B_605))) | ~v1_funct_2(F_609, D_606, B_605) | ~v1_funct_1(F_609) | ~m1_subset_1(E_607, k1_zfmisc_1(k2_zfmisc_1(C_604, B_605))) | ~v1_funct_2(E_607, C_604, B_605) | ~v1_funct_1(E_607) | ~m1_subset_1(D_606, k1_zfmisc_1(A_608)) | v1_xboole_0(D_606) | ~m1_subset_1(C_604, k1_zfmisc_1(A_608)) | v1_xboole_0(C_604) | v1_xboole_0(B_605) | v1_xboole_0(A_608))), inference(resolution, [status(thm)], [c_44, c_2119])).
% 8.44/2.72  tff(c_2341, plain, (![A_608, C_604, E_607]: (k2_partfun1(k4_subset_1(A_608, C_604, '#skF_4'), '#skF_2', k1_tmap_1(A_608, '#skF_2', C_604, '#skF_4', E_607, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_608, '#skF_2', C_604, '#skF_4', E_607, '#skF_6')) | k2_partfun1(C_604, '#skF_2', E_607, k9_subset_1(A_608, C_604, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_608, C_604, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_607, k1_zfmisc_1(k2_zfmisc_1(C_604, '#skF_2'))) | ~v1_funct_2(E_607, C_604, '#skF_2') | ~v1_funct_1(E_607) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_608)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_604, k1_zfmisc_1(A_608)) | v1_xboole_0(C_604) | v1_xboole_0('#skF_2') | v1_xboole_0(A_608))), inference(resolution, [status(thm)], [c_50, c_2335])).
% 8.44/2.72  tff(c_2349, plain, (![A_608, C_604, E_607]: (k2_partfun1(k4_subset_1(A_608, C_604, '#skF_4'), '#skF_2', k1_tmap_1(A_608, '#skF_2', C_604, '#skF_4', E_607, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_608, '#skF_2', C_604, '#skF_4', E_607, '#skF_6')) | k2_partfun1(C_604, '#skF_2', E_607, k9_subset_1(A_608, C_604, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_608, C_604, '#skF_4')) | ~m1_subset_1(E_607, k1_zfmisc_1(k2_zfmisc_1(C_604, '#skF_2'))) | ~v1_funct_2(E_607, C_604, '#skF_2') | ~v1_funct_1(E_607) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_608)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_604, k1_zfmisc_1(A_608)) | v1_xboole_0(C_604) | v1_xboole_0('#skF_2') | v1_xboole_0(A_608))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1240, c_2341])).
% 8.44/2.72  tff(c_2639, plain, (![A_655, C_656, E_657]: (k2_partfun1(k4_subset_1(A_655, C_656, '#skF_4'), '#skF_2', k1_tmap_1(A_655, '#skF_2', C_656, '#skF_4', E_657, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_655, '#skF_2', C_656, '#skF_4', E_657, '#skF_6')) | k2_partfun1(C_656, '#skF_2', E_657, k9_subset_1(A_655, C_656, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_655, C_656, '#skF_4')) | ~m1_subset_1(E_657, k1_zfmisc_1(k2_zfmisc_1(C_656, '#skF_2'))) | ~v1_funct_2(E_657, C_656, '#skF_2') | ~v1_funct_1(E_657) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_655)) | ~m1_subset_1(C_656, k1_zfmisc_1(A_655)) | v1_xboole_0(C_656) | v1_xboole_0(A_655))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_2349])).
% 8.44/2.72  tff(c_2644, plain, (![A_655]: (k2_partfun1(k4_subset_1(A_655, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_655, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_655, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_655, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_655, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_655)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_655)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_655))), inference(resolution, [status(thm)], [c_56, c_2639])).
% 8.44/2.72  tff(c_2652, plain, (![A_655]: (k2_partfun1(k4_subset_1(A_655, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_655, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_655, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_655, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_655, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_655)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_655)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_655))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1237, c_2644])).
% 8.44/2.72  tff(c_2705, plain, (![A_660]: (k2_partfun1(k4_subset_1(A_660, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_660, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_660, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_660, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_660, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_660)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_660)) | v1_xboole_0(A_660))), inference(negUnitSimplification, [status(thm)], [c_70, c_2652])).
% 8.44/2.72  tff(c_389, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_48])).
% 8.44/2.72  tff(c_802, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_389])).
% 8.44/2.72  tff(c_2716, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2705, c_802])).
% 8.44/2.72  tff(c_2730, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_1294, c_1225, c_2, c_1298, c_1225, c_2, c_1142, c_1142, c_1510, c_2716])).
% 8.44/2.72  tff(c_2732, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_2730])).
% 8.44/2.72  tff(c_2733, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_389])).
% 8.44/2.72  tff(c_4682, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4673, c_2733])).
% 8.44/2.72  tff(c_4693, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_3201, c_3241, c_2, c_3202, c_3241, c_2, c_3091, c_3091, c_3510, c_4682])).
% 8.44/2.72  tff(c_4695, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_4693])).
% 8.44/2.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.44/2.72  
% 8.44/2.72  Inference rules
% 8.44/2.72  ----------------------
% 8.44/2.72  #Ref     : 0
% 8.44/2.72  #Sup     : 950
% 8.44/2.72  #Fact    : 0
% 8.44/2.72  #Define  : 0
% 8.44/2.72  #Split   : 36
% 8.44/2.72  #Chain   : 0
% 8.44/2.72  #Close   : 0
% 8.44/2.72  
% 8.44/2.72  Ordering : KBO
% 8.44/2.72  
% 8.44/2.72  Simplification rules
% 8.44/2.72  ----------------------
% 8.44/2.72  #Subsume      : 87
% 8.44/2.72  #Demod        : 773
% 8.44/2.72  #Tautology    : 466
% 8.44/2.72  #SimpNegUnit  : 204
% 8.44/2.72  #BackRed      : 11
% 8.44/2.72  
% 8.44/2.72  #Partial instantiations: 0
% 8.44/2.72  #Strategies tried      : 1
% 8.44/2.72  
% 8.44/2.72  Timing (in seconds)
% 8.44/2.72  ----------------------
% 8.44/2.73  Preprocessing        : 0.40
% 8.44/2.73  Parsing              : 0.20
% 8.44/2.73  CNF conversion       : 0.05
% 8.44/2.73  Main loop            : 1.54
% 8.44/2.73  Inferencing          : 0.54
% 8.44/2.73  Reduction            : 0.51
% 8.44/2.73  Demodulation         : 0.38
% 8.44/2.73  BG Simplification    : 0.05
% 8.44/2.73  Subsumption          : 0.34
% 8.44/2.73  Abstraction          : 0.06
% 8.44/2.73  MUC search           : 0.00
% 8.44/2.73  Cooper               : 0.00
% 8.44/2.73  Total                : 2.01
% 8.44/2.73  Index Insertion      : 0.00
% 8.44/2.73  Index Deletion       : 0.00
% 8.44/2.73  Index Matching       : 0.00
% 8.44/2.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
