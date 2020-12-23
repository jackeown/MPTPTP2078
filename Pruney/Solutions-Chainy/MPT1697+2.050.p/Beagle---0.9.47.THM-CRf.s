%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:17 EST 2020

% Result     : Theorem 7.94s
% Output     : CNFRefutation 8.06s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 436 expanded)
%              Number of leaves         :   40 ( 178 expanded)
%              Depth                    :   12
%              Number of atoms          :  583 (2464 expanded)
%              Number of equality atoms :  103 ( 440 expanded)
%              Maximal formula depth    :   23 (   6 average)
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

tff(f_218,negated_conjecture,(
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

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_35,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_56,axiom,(
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

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_176,axiom,(
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

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_142,axiom,(
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

tff(c_72,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_401,plain,(
    ! [C_278,A_279,B_280] :
      ( v1_relat_1(C_278)
      | ~ m1_subset_1(C_278,k1_zfmisc_1(k2_zfmisc_1(A_279,B_280))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_409,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_401])).

tff(c_8,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_74,plain,(
    ! [B_221,A_222] :
      ( r1_xboole_0(B_221,A_222)
      | ~ r1_xboole_0(A_222,B_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_77,plain,(
    ! [A_5] : r1_xboole_0(k1_xboole_0,A_5) ),
    inference(resolution,[status(thm)],[c_8,c_74])).

tff(c_3434,plain,(
    ! [A_709,B_710] :
      ( k7_relat_1(A_709,B_710) = k1_xboole_0
      | ~ r1_xboole_0(B_710,k1_relat_1(A_709))
      | ~ v1_relat_1(A_709) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3455,plain,(
    ! [A_711] :
      ( k7_relat_1(A_711,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_711) ) ),
    inference(resolution,[status(thm)],[c_77,c_3434])).

tff(c_3462,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_409,c_3455])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_408,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_401])).

tff(c_3463,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_408,c_3455])).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_60,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_3422,plain,(
    ! [A_707,B_708] :
      ( r1_xboole_0(A_707,B_708)
      | ~ r1_subset_1(A_707,B_708)
      | v1_xboole_0(B_708)
      | v1_xboole_0(A_707) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4707,plain,(
    ! [A_828,B_829] :
      ( k3_xboole_0(A_828,B_829) = k1_xboole_0
      | ~ r1_subset_1(A_828,B_829)
      | v1_xboole_0(B_829)
      | v1_xboole_0(A_828) ) ),
    inference(resolution,[status(thm)],[c_3422,c_2])).

tff(c_4713,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_4707])).

tff(c_4719,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_64,c_4713])).

tff(c_4556,plain,(
    ! [A_816,B_817,C_818] :
      ( k9_subset_1(A_816,B_817,C_818) = k3_xboole_0(B_817,C_818)
      | ~ m1_subset_1(C_818,k1_zfmisc_1(A_816)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4567,plain,(
    ! [B_817] : k9_subset_1('#skF_1',B_817,'#skF_4') = k3_xboole_0(B_817,'#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_4556])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_56,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_52,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_50,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_4944,plain,(
    ! [D_854,B_858,E_853,C_856,F_857,A_855] :
      ( v1_funct_1(k1_tmap_1(A_855,B_858,C_856,D_854,E_853,F_857))
      | ~ m1_subset_1(F_857,k1_zfmisc_1(k2_zfmisc_1(D_854,B_858)))
      | ~ v1_funct_2(F_857,D_854,B_858)
      | ~ v1_funct_1(F_857)
      | ~ m1_subset_1(E_853,k1_zfmisc_1(k2_zfmisc_1(C_856,B_858)))
      | ~ v1_funct_2(E_853,C_856,B_858)
      | ~ v1_funct_1(E_853)
      | ~ m1_subset_1(D_854,k1_zfmisc_1(A_855))
      | v1_xboole_0(D_854)
      | ~ m1_subset_1(C_856,k1_zfmisc_1(A_855))
      | v1_xboole_0(C_856)
      | v1_xboole_0(B_858)
      | v1_xboole_0(A_855) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_4946,plain,(
    ! [A_855,C_856,E_853] :
      ( v1_funct_1(k1_tmap_1(A_855,'#skF_2',C_856,'#skF_4',E_853,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_853,k1_zfmisc_1(k2_zfmisc_1(C_856,'#skF_2')))
      | ~ v1_funct_2(E_853,C_856,'#skF_2')
      | ~ v1_funct_1(E_853)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_855))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_856,k1_zfmisc_1(A_855))
      | v1_xboole_0(C_856)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_855) ) ),
    inference(resolution,[status(thm)],[c_48,c_4944])).

tff(c_4951,plain,(
    ! [A_855,C_856,E_853] :
      ( v1_funct_1(k1_tmap_1(A_855,'#skF_2',C_856,'#skF_4',E_853,'#skF_6'))
      | ~ m1_subset_1(E_853,k1_zfmisc_1(k2_zfmisc_1(C_856,'#skF_2')))
      | ~ v1_funct_2(E_853,C_856,'#skF_2')
      | ~ v1_funct_1(E_853)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_855))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_856,k1_zfmisc_1(A_855))
      | v1_xboole_0(C_856)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_855) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_4946])).

tff(c_4957,plain,(
    ! [A_859,C_860,E_861] :
      ( v1_funct_1(k1_tmap_1(A_859,'#skF_2',C_860,'#skF_4',E_861,'#skF_6'))
      | ~ m1_subset_1(E_861,k1_zfmisc_1(k2_zfmisc_1(C_860,'#skF_2')))
      | ~ v1_funct_2(E_861,C_860,'#skF_2')
      | ~ v1_funct_1(E_861)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_859))
      | ~ m1_subset_1(C_860,k1_zfmisc_1(A_859))
      | v1_xboole_0(C_860)
      | v1_xboole_0(A_859) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_4951])).

tff(c_4961,plain,(
    ! [A_859] :
      ( v1_funct_1(k1_tmap_1(A_859,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_859))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_859))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_859) ) ),
    inference(resolution,[status(thm)],[c_54,c_4957])).

tff(c_4968,plain,(
    ! [A_859] :
      ( v1_funct_1(k1_tmap_1(A_859,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_859))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_859))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_859) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_4961])).

tff(c_4977,plain,(
    ! [A_863] :
      ( v1_funct_1(k1_tmap_1(A_863,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_863))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_863))
      | v1_xboole_0(A_863) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_4968])).

tff(c_4980,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_4977])).

tff(c_4983,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_4980])).

tff(c_4984,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_4983])).

tff(c_4800,plain,(
    ! [A_836,B_837,C_838,D_839] :
      ( k2_partfun1(A_836,B_837,C_838,D_839) = k7_relat_1(C_838,D_839)
      | ~ m1_subset_1(C_838,k1_zfmisc_1(k2_zfmisc_1(A_836,B_837)))
      | ~ v1_funct_1(C_838) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_4804,plain,(
    ! [D_839] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_839) = k7_relat_1('#skF_5',D_839)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_4800])).

tff(c_4810,plain,(
    ! [D_839] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_839) = k7_relat_1('#skF_5',D_839) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_4804])).

tff(c_4802,plain,(
    ! [D_839] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_839) = k7_relat_1('#skF_6',D_839)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_48,c_4800])).

tff(c_4807,plain,(
    ! [D_839] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_839) = k7_relat_1('#skF_6',D_839) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_4802])).

tff(c_42,plain,(
    ! [C_159,D_160,F_162,A_157,B_158,E_161] :
      ( v1_funct_2(k1_tmap_1(A_157,B_158,C_159,D_160,E_161,F_162),k4_subset_1(A_157,C_159,D_160),B_158)
      | ~ m1_subset_1(F_162,k1_zfmisc_1(k2_zfmisc_1(D_160,B_158)))
      | ~ v1_funct_2(F_162,D_160,B_158)
      | ~ v1_funct_1(F_162)
      | ~ m1_subset_1(E_161,k1_zfmisc_1(k2_zfmisc_1(C_159,B_158)))
      | ~ v1_funct_2(E_161,C_159,B_158)
      | ~ v1_funct_1(E_161)
      | ~ m1_subset_1(D_160,k1_zfmisc_1(A_157))
      | v1_xboole_0(D_160)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(A_157))
      | v1_xboole_0(C_159)
      | v1_xboole_0(B_158)
      | v1_xboole_0(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_40,plain,(
    ! [C_159,D_160,F_162,A_157,B_158,E_161] :
      ( m1_subset_1(k1_tmap_1(A_157,B_158,C_159,D_160,E_161,F_162),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_157,C_159,D_160),B_158)))
      | ~ m1_subset_1(F_162,k1_zfmisc_1(k2_zfmisc_1(D_160,B_158)))
      | ~ v1_funct_2(F_162,D_160,B_158)
      | ~ v1_funct_1(F_162)
      | ~ m1_subset_1(E_161,k1_zfmisc_1(k2_zfmisc_1(C_159,B_158)))
      | ~ v1_funct_2(E_161,C_159,B_158)
      | ~ v1_funct_1(E_161)
      | ~ m1_subset_1(D_160,k1_zfmisc_1(A_157))
      | v1_xboole_0(D_160)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(A_157))
      | v1_xboole_0(C_159)
      | v1_xboole_0(B_158)
      | v1_xboole_0(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_5114,plain,(
    ! [A_894,B_892,E_893,C_896,F_897,D_895] :
      ( k2_partfun1(k4_subset_1(A_894,C_896,D_895),B_892,k1_tmap_1(A_894,B_892,C_896,D_895,E_893,F_897),C_896) = E_893
      | ~ m1_subset_1(k1_tmap_1(A_894,B_892,C_896,D_895,E_893,F_897),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_894,C_896,D_895),B_892)))
      | ~ v1_funct_2(k1_tmap_1(A_894,B_892,C_896,D_895,E_893,F_897),k4_subset_1(A_894,C_896,D_895),B_892)
      | ~ v1_funct_1(k1_tmap_1(A_894,B_892,C_896,D_895,E_893,F_897))
      | k2_partfun1(D_895,B_892,F_897,k9_subset_1(A_894,C_896,D_895)) != k2_partfun1(C_896,B_892,E_893,k9_subset_1(A_894,C_896,D_895))
      | ~ m1_subset_1(F_897,k1_zfmisc_1(k2_zfmisc_1(D_895,B_892)))
      | ~ v1_funct_2(F_897,D_895,B_892)
      | ~ v1_funct_1(F_897)
      | ~ m1_subset_1(E_893,k1_zfmisc_1(k2_zfmisc_1(C_896,B_892)))
      | ~ v1_funct_2(E_893,C_896,B_892)
      | ~ v1_funct_1(E_893)
      | ~ m1_subset_1(D_895,k1_zfmisc_1(A_894))
      | v1_xboole_0(D_895)
      | ~ m1_subset_1(C_896,k1_zfmisc_1(A_894))
      | v1_xboole_0(C_896)
      | v1_xboole_0(B_892)
      | v1_xboole_0(A_894) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_5613,plain,(
    ! [B_997,E_992,F_996,A_994,D_993,C_995] :
      ( k2_partfun1(k4_subset_1(A_994,C_995,D_993),B_997,k1_tmap_1(A_994,B_997,C_995,D_993,E_992,F_996),C_995) = E_992
      | ~ v1_funct_2(k1_tmap_1(A_994,B_997,C_995,D_993,E_992,F_996),k4_subset_1(A_994,C_995,D_993),B_997)
      | ~ v1_funct_1(k1_tmap_1(A_994,B_997,C_995,D_993,E_992,F_996))
      | k2_partfun1(D_993,B_997,F_996,k9_subset_1(A_994,C_995,D_993)) != k2_partfun1(C_995,B_997,E_992,k9_subset_1(A_994,C_995,D_993))
      | ~ m1_subset_1(F_996,k1_zfmisc_1(k2_zfmisc_1(D_993,B_997)))
      | ~ v1_funct_2(F_996,D_993,B_997)
      | ~ v1_funct_1(F_996)
      | ~ m1_subset_1(E_992,k1_zfmisc_1(k2_zfmisc_1(C_995,B_997)))
      | ~ v1_funct_2(E_992,C_995,B_997)
      | ~ v1_funct_1(E_992)
      | ~ m1_subset_1(D_993,k1_zfmisc_1(A_994))
      | v1_xboole_0(D_993)
      | ~ m1_subset_1(C_995,k1_zfmisc_1(A_994))
      | v1_xboole_0(C_995)
      | v1_xboole_0(B_997)
      | v1_xboole_0(A_994) ) ),
    inference(resolution,[status(thm)],[c_40,c_5114])).

tff(c_5911,plain,(
    ! [F_1045,D_1042,C_1044,B_1046,A_1043,E_1041] :
      ( k2_partfun1(k4_subset_1(A_1043,C_1044,D_1042),B_1046,k1_tmap_1(A_1043,B_1046,C_1044,D_1042,E_1041,F_1045),C_1044) = E_1041
      | ~ v1_funct_1(k1_tmap_1(A_1043,B_1046,C_1044,D_1042,E_1041,F_1045))
      | k2_partfun1(D_1042,B_1046,F_1045,k9_subset_1(A_1043,C_1044,D_1042)) != k2_partfun1(C_1044,B_1046,E_1041,k9_subset_1(A_1043,C_1044,D_1042))
      | ~ m1_subset_1(F_1045,k1_zfmisc_1(k2_zfmisc_1(D_1042,B_1046)))
      | ~ v1_funct_2(F_1045,D_1042,B_1046)
      | ~ v1_funct_1(F_1045)
      | ~ m1_subset_1(E_1041,k1_zfmisc_1(k2_zfmisc_1(C_1044,B_1046)))
      | ~ v1_funct_2(E_1041,C_1044,B_1046)
      | ~ v1_funct_1(E_1041)
      | ~ m1_subset_1(D_1042,k1_zfmisc_1(A_1043))
      | v1_xboole_0(D_1042)
      | ~ m1_subset_1(C_1044,k1_zfmisc_1(A_1043))
      | v1_xboole_0(C_1044)
      | v1_xboole_0(B_1046)
      | v1_xboole_0(A_1043) ) ),
    inference(resolution,[status(thm)],[c_42,c_5613])).

tff(c_5915,plain,(
    ! [A_1043,C_1044,E_1041] :
      ( k2_partfun1(k4_subset_1(A_1043,C_1044,'#skF_4'),'#skF_2',k1_tmap_1(A_1043,'#skF_2',C_1044,'#skF_4',E_1041,'#skF_6'),C_1044) = E_1041
      | ~ v1_funct_1(k1_tmap_1(A_1043,'#skF_2',C_1044,'#skF_4',E_1041,'#skF_6'))
      | k2_partfun1(C_1044,'#skF_2',E_1041,k9_subset_1(A_1043,C_1044,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_1043,C_1044,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1041,k1_zfmisc_1(k2_zfmisc_1(C_1044,'#skF_2')))
      | ~ v1_funct_2(E_1041,C_1044,'#skF_2')
      | ~ v1_funct_1(E_1041)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1043))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1044,k1_zfmisc_1(A_1043))
      | v1_xboole_0(C_1044)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1043) ) ),
    inference(resolution,[status(thm)],[c_48,c_5911])).

tff(c_5921,plain,(
    ! [A_1043,C_1044,E_1041] :
      ( k2_partfun1(k4_subset_1(A_1043,C_1044,'#skF_4'),'#skF_2',k1_tmap_1(A_1043,'#skF_2',C_1044,'#skF_4',E_1041,'#skF_6'),C_1044) = E_1041
      | ~ v1_funct_1(k1_tmap_1(A_1043,'#skF_2',C_1044,'#skF_4',E_1041,'#skF_6'))
      | k2_partfun1(C_1044,'#skF_2',E_1041,k9_subset_1(A_1043,C_1044,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1043,C_1044,'#skF_4'))
      | ~ m1_subset_1(E_1041,k1_zfmisc_1(k2_zfmisc_1(C_1044,'#skF_2')))
      | ~ v1_funct_2(E_1041,C_1044,'#skF_2')
      | ~ v1_funct_1(E_1041)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1043))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1044,k1_zfmisc_1(A_1043))
      | v1_xboole_0(C_1044)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1043) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_4807,c_5915])).

tff(c_6253,plain,(
    ! [A_1095,C_1096,E_1097] :
      ( k2_partfun1(k4_subset_1(A_1095,C_1096,'#skF_4'),'#skF_2',k1_tmap_1(A_1095,'#skF_2',C_1096,'#skF_4',E_1097,'#skF_6'),C_1096) = E_1097
      | ~ v1_funct_1(k1_tmap_1(A_1095,'#skF_2',C_1096,'#skF_4',E_1097,'#skF_6'))
      | k2_partfun1(C_1096,'#skF_2',E_1097,k9_subset_1(A_1095,C_1096,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1095,C_1096,'#skF_4'))
      | ~ m1_subset_1(E_1097,k1_zfmisc_1(k2_zfmisc_1(C_1096,'#skF_2')))
      | ~ v1_funct_2(E_1097,C_1096,'#skF_2')
      | ~ v1_funct_1(E_1097)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1095))
      | ~ m1_subset_1(C_1096,k1_zfmisc_1(A_1095))
      | v1_xboole_0(C_1096)
      | v1_xboole_0(A_1095) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_5921])).

tff(c_6260,plain,(
    ! [A_1095] :
      ( k2_partfun1(k4_subset_1(A_1095,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1095,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1095,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1095,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1095,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1095))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1095))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1095) ) ),
    inference(resolution,[status(thm)],[c_54,c_6253])).

tff(c_6270,plain,(
    ! [A_1095] :
      ( k2_partfun1(k4_subset_1(A_1095,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1095,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1095,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1095,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1095,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1095))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1095))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1095) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_4810,c_6260])).

tff(c_6295,plain,(
    ! [A_1099] :
      ( k2_partfun1(k4_subset_1(A_1099,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1099,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1099,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1099,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1099,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1099))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1099))
      | v1_xboole_0(A_1099) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_6270])).

tff(c_482,plain,(
    ! [A_296,B_297] :
      ( k7_relat_1(A_296,B_297) = k1_xboole_0
      | ~ r1_xboole_0(B_297,k1_relat_1(A_296))
      | ~ v1_relat_1(A_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_516,plain,(
    ! [A_300] :
      ( k7_relat_1(A_300,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_300) ) ),
    inference(resolution,[status(thm)],[c_77,c_482])).

tff(c_523,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_409,c_516])).

tff(c_524,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_408,c_516])).

tff(c_470,plain,(
    ! [A_294,B_295] :
      ( r1_xboole_0(A_294,B_295)
      | ~ r1_subset_1(A_294,B_295)
      | v1_xboole_0(B_295)
      | v1_xboole_0(A_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1829,plain,(
    ! [A_434,B_435] :
      ( k3_xboole_0(A_434,B_435) = k1_xboole_0
      | ~ r1_subset_1(A_434,B_435)
      | v1_xboole_0(B_435)
      | v1_xboole_0(A_434) ) ),
    inference(resolution,[status(thm)],[c_470,c_2])).

tff(c_1838,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_1829])).

tff(c_1845,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_64,c_1838])).

tff(c_1596,plain,(
    ! [A_409,B_410,C_411] :
      ( k9_subset_1(A_409,B_410,C_411) = k3_xboole_0(B_410,C_411)
      | ~ m1_subset_1(C_411,k1_zfmisc_1(A_409)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1607,plain,(
    ! [B_410] : k9_subset_1('#skF_1',B_410,'#skF_4') = k3_xboole_0(B_410,'#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_1596])).

tff(c_1970,plain,(
    ! [A_449,C_450,E_447,D_448,F_451,B_452] :
      ( v1_funct_1(k1_tmap_1(A_449,B_452,C_450,D_448,E_447,F_451))
      | ~ m1_subset_1(F_451,k1_zfmisc_1(k2_zfmisc_1(D_448,B_452)))
      | ~ v1_funct_2(F_451,D_448,B_452)
      | ~ v1_funct_1(F_451)
      | ~ m1_subset_1(E_447,k1_zfmisc_1(k2_zfmisc_1(C_450,B_452)))
      | ~ v1_funct_2(E_447,C_450,B_452)
      | ~ v1_funct_1(E_447)
      | ~ m1_subset_1(D_448,k1_zfmisc_1(A_449))
      | v1_xboole_0(D_448)
      | ~ m1_subset_1(C_450,k1_zfmisc_1(A_449))
      | v1_xboole_0(C_450)
      | v1_xboole_0(B_452)
      | v1_xboole_0(A_449) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_1972,plain,(
    ! [A_449,C_450,E_447] :
      ( v1_funct_1(k1_tmap_1(A_449,'#skF_2',C_450,'#skF_4',E_447,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_447,k1_zfmisc_1(k2_zfmisc_1(C_450,'#skF_2')))
      | ~ v1_funct_2(E_447,C_450,'#skF_2')
      | ~ v1_funct_1(E_447)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_449))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_450,k1_zfmisc_1(A_449))
      | v1_xboole_0(C_450)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_449) ) ),
    inference(resolution,[status(thm)],[c_48,c_1970])).

tff(c_1977,plain,(
    ! [A_449,C_450,E_447] :
      ( v1_funct_1(k1_tmap_1(A_449,'#skF_2',C_450,'#skF_4',E_447,'#skF_6'))
      | ~ m1_subset_1(E_447,k1_zfmisc_1(k2_zfmisc_1(C_450,'#skF_2')))
      | ~ v1_funct_2(E_447,C_450,'#skF_2')
      | ~ v1_funct_1(E_447)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_449))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_450,k1_zfmisc_1(A_449))
      | v1_xboole_0(C_450)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_449) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1972])).

tff(c_2034,plain,(
    ! [A_460,C_461,E_462] :
      ( v1_funct_1(k1_tmap_1(A_460,'#skF_2',C_461,'#skF_4',E_462,'#skF_6'))
      | ~ m1_subset_1(E_462,k1_zfmisc_1(k2_zfmisc_1(C_461,'#skF_2')))
      | ~ v1_funct_2(E_462,C_461,'#skF_2')
      | ~ v1_funct_1(E_462)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_460))
      | ~ m1_subset_1(C_461,k1_zfmisc_1(A_460))
      | v1_xboole_0(C_461)
      | v1_xboole_0(A_460) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_1977])).

tff(c_2038,plain,(
    ! [A_460] :
      ( v1_funct_1(k1_tmap_1(A_460,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_460))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_460))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_460) ) ),
    inference(resolution,[status(thm)],[c_54,c_2034])).

tff(c_2045,plain,(
    ! [A_460] :
      ( v1_funct_1(k1_tmap_1(A_460,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_460))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_460))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_460) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_2038])).

tff(c_2055,plain,(
    ! [A_470] :
      ( v1_funct_1(k1_tmap_1(A_470,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_470))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_470))
      | v1_xboole_0(A_470) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2045])).

tff(c_2058,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_2055])).

tff(c_2061,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2058])).

tff(c_2062,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2061])).

tff(c_1712,plain,(
    ! [A_421,B_422,C_423,D_424] :
      ( k2_partfun1(A_421,B_422,C_423,D_424) = k7_relat_1(C_423,D_424)
      | ~ m1_subset_1(C_423,k1_zfmisc_1(k2_zfmisc_1(A_421,B_422)))
      | ~ v1_funct_1(C_423) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1716,plain,(
    ! [D_424] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_424) = k7_relat_1('#skF_5',D_424)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_1712])).

tff(c_1722,plain,(
    ! [D_424] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_424) = k7_relat_1('#skF_5',D_424) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1716])).

tff(c_1714,plain,(
    ! [D_424] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_424) = k7_relat_1('#skF_6',D_424)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_48,c_1712])).

tff(c_1719,plain,(
    ! [D_424] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_424) = k7_relat_1('#skF_6',D_424) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1714])).

tff(c_2218,plain,(
    ! [B_505,A_507,F_510,D_508,C_509,E_506] :
      ( k2_partfun1(k4_subset_1(A_507,C_509,D_508),B_505,k1_tmap_1(A_507,B_505,C_509,D_508,E_506,F_510),D_508) = F_510
      | ~ m1_subset_1(k1_tmap_1(A_507,B_505,C_509,D_508,E_506,F_510),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_507,C_509,D_508),B_505)))
      | ~ v1_funct_2(k1_tmap_1(A_507,B_505,C_509,D_508,E_506,F_510),k4_subset_1(A_507,C_509,D_508),B_505)
      | ~ v1_funct_1(k1_tmap_1(A_507,B_505,C_509,D_508,E_506,F_510))
      | k2_partfun1(D_508,B_505,F_510,k9_subset_1(A_507,C_509,D_508)) != k2_partfun1(C_509,B_505,E_506,k9_subset_1(A_507,C_509,D_508))
      | ~ m1_subset_1(F_510,k1_zfmisc_1(k2_zfmisc_1(D_508,B_505)))
      | ~ v1_funct_2(F_510,D_508,B_505)
      | ~ v1_funct_1(F_510)
      | ~ m1_subset_1(E_506,k1_zfmisc_1(k2_zfmisc_1(C_509,B_505)))
      | ~ v1_funct_2(E_506,C_509,B_505)
      | ~ v1_funct_1(E_506)
      | ~ m1_subset_1(D_508,k1_zfmisc_1(A_507))
      | v1_xboole_0(D_508)
      | ~ m1_subset_1(C_509,k1_zfmisc_1(A_507))
      | v1_xboole_0(C_509)
      | v1_xboole_0(B_505)
      | v1_xboole_0(A_507) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_2796,plain,(
    ! [B_617,C_615,A_614,F_616,D_613,E_612] :
      ( k2_partfun1(k4_subset_1(A_614,C_615,D_613),B_617,k1_tmap_1(A_614,B_617,C_615,D_613,E_612,F_616),D_613) = F_616
      | ~ v1_funct_2(k1_tmap_1(A_614,B_617,C_615,D_613,E_612,F_616),k4_subset_1(A_614,C_615,D_613),B_617)
      | ~ v1_funct_1(k1_tmap_1(A_614,B_617,C_615,D_613,E_612,F_616))
      | k2_partfun1(D_613,B_617,F_616,k9_subset_1(A_614,C_615,D_613)) != k2_partfun1(C_615,B_617,E_612,k9_subset_1(A_614,C_615,D_613))
      | ~ m1_subset_1(F_616,k1_zfmisc_1(k2_zfmisc_1(D_613,B_617)))
      | ~ v1_funct_2(F_616,D_613,B_617)
      | ~ v1_funct_1(F_616)
      | ~ m1_subset_1(E_612,k1_zfmisc_1(k2_zfmisc_1(C_615,B_617)))
      | ~ v1_funct_2(E_612,C_615,B_617)
      | ~ v1_funct_1(E_612)
      | ~ m1_subset_1(D_613,k1_zfmisc_1(A_614))
      | v1_xboole_0(D_613)
      | ~ m1_subset_1(C_615,k1_zfmisc_1(A_614))
      | v1_xboole_0(C_615)
      | v1_xboole_0(B_617)
      | v1_xboole_0(A_614) ) ),
    inference(resolution,[status(thm)],[c_40,c_2218])).

tff(c_2936,plain,(
    ! [A_645,F_647,B_648,D_644,C_646,E_643] :
      ( k2_partfun1(k4_subset_1(A_645,C_646,D_644),B_648,k1_tmap_1(A_645,B_648,C_646,D_644,E_643,F_647),D_644) = F_647
      | ~ v1_funct_1(k1_tmap_1(A_645,B_648,C_646,D_644,E_643,F_647))
      | k2_partfun1(D_644,B_648,F_647,k9_subset_1(A_645,C_646,D_644)) != k2_partfun1(C_646,B_648,E_643,k9_subset_1(A_645,C_646,D_644))
      | ~ m1_subset_1(F_647,k1_zfmisc_1(k2_zfmisc_1(D_644,B_648)))
      | ~ v1_funct_2(F_647,D_644,B_648)
      | ~ v1_funct_1(F_647)
      | ~ m1_subset_1(E_643,k1_zfmisc_1(k2_zfmisc_1(C_646,B_648)))
      | ~ v1_funct_2(E_643,C_646,B_648)
      | ~ v1_funct_1(E_643)
      | ~ m1_subset_1(D_644,k1_zfmisc_1(A_645))
      | v1_xboole_0(D_644)
      | ~ m1_subset_1(C_646,k1_zfmisc_1(A_645))
      | v1_xboole_0(C_646)
      | v1_xboole_0(B_648)
      | v1_xboole_0(A_645) ) ),
    inference(resolution,[status(thm)],[c_42,c_2796])).

tff(c_2940,plain,(
    ! [A_645,C_646,E_643] :
      ( k2_partfun1(k4_subset_1(A_645,C_646,'#skF_4'),'#skF_2',k1_tmap_1(A_645,'#skF_2',C_646,'#skF_4',E_643,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_645,'#skF_2',C_646,'#skF_4',E_643,'#skF_6'))
      | k2_partfun1(C_646,'#skF_2',E_643,k9_subset_1(A_645,C_646,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_645,C_646,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_643,k1_zfmisc_1(k2_zfmisc_1(C_646,'#skF_2')))
      | ~ v1_funct_2(E_643,C_646,'#skF_2')
      | ~ v1_funct_1(E_643)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_645))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_646,k1_zfmisc_1(A_645))
      | v1_xboole_0(C_646)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_645) ) ),
    inference(resolution,[status(thm)],[c_48,c_2936])).

tff(c_2946,plain,(
    ! [A_645,C_646,E_643] :
      ( k2_partfun1(k4_subset_1(A_645,C_646,'#skF_4'),'#skF_2',k1_tmap_1(A_645,'#skF_2',C_646,'#skF_4',E_643,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_645,'#skF_2',C_646,'#skF_4',E_643,'#skF_6'))
      | k2_partfun1(C_646,'#skF_2',E_643,k9_subset_1(A_645,C_646,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_645,C_646,'#skF_4'))
      | ~ m1_subset_1(E_643,k1_zfmisc_1(k2_zfmisc_1(C_646,'#skF_2')))
      | ~ v1_funct_2(E_643,C_646,'#skF_2')
      | ~ v1_funct_1(E_643)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_645))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_646,k1_zfmisc_1(A_645))
      | v1_xboole_0(C_646)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_645) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1719,c_2940])).

tff(c_3289,plain,(
    ! [A_696,C_697,E_698] :
      ( k2_partfun1(k4_subset_1(A_696,C_697,'#skF_4'),'#skF_2',k1_tmap_1(A_696,'#skF_2',C_697,'#skF_4',E_698,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_696,'#skF_2',C_697,'#skF_4',E_698,'#skF_6'))
      | k2_partfun1(C_697,'#skF_2',E_698,k9_subset_1(A_696,C_697,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_696,C_697,'#skF_4'))
      | ~ m1_subset_1(E_698,k1_zfmisc_1(k2_zfmisc_1(C_697,'#skF_2')))
      | ~ v1_funct_2(E_698,C_697,'#skF_2')
      | ~ v1_funct_1(E_698)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_696))
      | ~ m1_subset_1(C_697,k1_zfmisc_1(A_696))
      | v1_xboole_0(C_697)
      | v1_xboole_0(A_696) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_2946])).

tff(c_3296,plain,(
    ! [A_696] :
      ( k2_partfun1(k4_subset_1(A_696,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_696,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_696,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_696,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_696,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_696))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_696))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_696) ) ),
    inference(resolution,[status(thm)],[c_54,c_3289])).

tff(c_3306,plain,(
    ! [A_696] :
      ( k2_partfun1(k4_subset_1(A_696,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_696,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_696,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_696,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_696,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_696))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_696))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_696) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1722,c_3296])).

tff(c_3390,plain,(
    ! [A_705] :
      ( k2_partfun1(k4_subset_1(A_705,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_705,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_705,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_705,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_705,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_705))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_705))
      | v1_xboole_0(A_705) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3306])).

tff(c_131,plain,(
    ! [C_232,A_233,B_234] :
      ( v1_relat_1(C_232)
      | ~ m1_subset_1(C_232,k1_zfmisc_1(k2_zfmisc_1(A_233,B_234))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_138,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_131])).

tff(c_199,plain,(
    ! [A_248,B_249] :
      ( k7_relat_1(A_248,B_249) = k1_xboole_0
      | ~ r1_xboole_0(B_249,k1_relat_1(A_248))
      | ~ v1_relat_1(A_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_220,plain,(
    ! [A_250] :
      ( k7_relat_1(A_250,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_250) ) ),
    inference(resolution,[status(thm)],[c_77,c_199])).

tff(c_228,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_138,c_220])).

tff(c_139,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_131])).

tff(c_227,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_139,c_220])).

tff(c_187,plain,(
    ! [A_246,B_247] :
      ( r1_xboole_0(A_246,B_247)
      | ~ r1_subset_1(A_246,B_247)
      | v1_xboole_0(B_247)
      | v1_xboole_0(A_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_370,plain,(
    ! [A_274,B_275] :
      ( k3_xboole_0(A_274,B_275) = k1_xboole_0
      | ~ r1_subset_1(A_274,B_275)
      | v1_xboole_0(B_275)
      | v1_xboole_0(A_274) ) ),
    inference(resolution,[status(thm)],[c_187,c_2])).

tff(c_379,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_370])).

tff(c_386,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_64,c_379])).

tff(c_321,plain,(
    ! [A_263,B_264,C_265,D_266] :
      ( k2_partfun1(A_263,B_264,C_265,D_266) = k7_relat_1(C_265,D_266)
      | ~ m1_subset_1(C_265,k1_zfmisc_1(k2_zfmisc_1(A_263,B_264)))
      | ~ v1_funct_1(C_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_325,plain,(
    ! [D_266] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_266) = k7_relat_1('#skF_5',D_266)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_321])).

tff(c_331,plain,(
    ! [D_266] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_266) = k7_relat_1('#skF_5',D_266) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_325])).

tff(c_323,plain,(
    ! [D_266] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_266) = k7_relat_1('#skF_6',D_266)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_48,c_321])).

tff(c_328,plain,(
    ! [D_266] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_266) = k7_relat_1('#skF_6',D_266) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_323])).

tff(c_280,plain,(
    ! [A_257,B_258,C_259] :
      ( k9_subset_1(A_257,B_258,C_259) = k3_xboole_0(B_258,C_259)
      | ~ m1_subset_1(C_259,k1_zfmisc_1(A_257)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_291,plain,(
    ! [B_258] : k9_subset_1('#skF_1',B_258,'#skF_4') = k3_xboole_0(B_258,'#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_280])).

tff(c_46,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_114,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_293,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_291,c_114])).

tff(c_359,plain,(
    k7_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k7_relat_1('#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_331,c_328,c_293])).

tff(c_387,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) != k7_relat_1('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_386,c_359])).

tff(c_390,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_227,c_387])).

tff(c_391,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_467,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_391])).

tff(c_3401,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3390,c_467])).

tff(c_3415,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_523,c_524,c_1845,c_1607,c_1845,c_1607,c_2062,c_3401])).

tff(c_3417,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3415])).

tff(c_3418,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_391])).

tff(c_6304,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6295,c_3418])).

tff(c_6315,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_3462,c_3463,c_4719,c_4567,c_4719,c_4567,c_4984,c_6304])).

tff(c_6317,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_6315])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:56:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.94/2.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.94/2.76  
% 7.94/2.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.94/2.76  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.94/2.76  
% 7.94/2.76  %Foreground sorts:
% 7.94/2.76  
% 7.94/2.76  
% 7.94/2.76  %Background operators:
% 7.94/2.76  
% 7.94/2.76  
% 7.94/2.76  %Foreground operators:
% 7.94/2.76  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 7.94/2.76  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.94/2.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.94/2.76  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.94/2.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.94/2.76  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 7.94/2.76  tff('#skF_5', type, '#skF_5': $i).
% 7.94/2.76  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.94/2.76  tff('#skF_6', type, '#skF_6': $i).
% 7.94/2.76  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.94/2.76  tff('#skF_2', type, '#skF_2': $i).
% 7.94/2.76  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.94/2.76  tff('#skF_3', type, '#skF_3': $i).
% 7.94/2.76  tff('#skF_1', type, '#skF_1': $i).
% 7.94/2.76  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.94/2.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.94/2.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.94/2.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.94/2.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.94/2.76  tff('#skF_4', type, '#skF_4': $i).
% 7.94/2.76  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.94/2.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.94/2.76  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 7.94/2.76  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.94/2.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.94/2.76  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.94/2.76  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.94/2.76  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.94/2.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.94/2.76  
% 8.06/2.79  tff(f_218, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 8.06/2.79  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.06/2.79  tff(f_35, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 8.06/2.79  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 8.06/2.79  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 8.06/2.79  tff(f_56, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 8.06/2.79  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.06/2.79  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 8.06/2.79  tff(f_176, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 8.06/2.79  tff(f_94, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 8.06/2.79  tff(f_142, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 8.06/2.79  tff(c_72, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_218])).
% 8.06/2.79  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_218])).
% 8.06/2.79  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_218])).
% 8.06/2.79  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_218])).
% 8.06/2.79  tff(c_401, plain, (![C_278, A_279, B_280]: (v1_relat_1(C_278) | ~m1_subset_1(C_278, k1_zfmisc_1(k2_zfmisc_1(A_279, B_280))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.06/2.79  tff(c_409, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_401])).
% 8.06/2.79  tff(c_8, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.06/2.79  tff(c_74, plain, (![B_221, A_222]: (r1_xboole_0(B_221, A_222) | ~r1_xboole_0(A_222, B_221))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.06/2.79  tff(c_77, plain, (![A_5]: (r1_xboole_0(k1_xboole_0, A_5))), inference(resolution, [status(thm)], [c_8, c_74])).
% 8.06/2.79  tff(c_3434, plain, (![A_709, B_710]: (k7_relat_1(A_709, B_710)=k1_xboole_0 | ~r1_xboole_0(B_710, k1_relat_1(A_709)) | ~v1_relat_1(A_709))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.06/2.79  tff(c_3455, plain, (![A_711]: (k7_relat_1(A_711, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_711))), inference(resolution, [status(thm)], [c_77, c_3434])).
% 8.06/2.79  tff(c_3462, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_409, c_3455])).
% 8.06/2.79  tff(c_48, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_218])).
% 8.06/2.79  tff(c_408, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_48, c_401])).
% 8.06/2.79  tff(c_3463, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_408, c_3455])).
% 8.06/2.79  tff(c_68, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_218])).
% 8.06/2.79  tff(c_64, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_218])).
% 8.06/2.79  tff(c_60, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_218])).
% 8.06/2.79  tff(c_3422, plain, (![A_707, B_708]: (r1_xboole_0(A_707, B_708) | ~r1_subset_1(A_707, B_708) | v1_xboole_0(B_708) | v1_xboole_0(A_707))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.06/2.79  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.06/2.79  tff(c_4707, plain, (![A_828, B_829]: (k3_xboole_0(A_828, B_829)=k1_xboole_0 | ~r1_subset_1(A_828, B_829) | v1_xboole_0(B_829) | v1_xboole_0(A_828))), inference(resolution, [status(thm)], [c_3422, c_2])).
% 8.06/2.79  tff(c_4713, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_4707])).
% 8.06/2.79  tff(c_4719, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_68, c_64, c_4713])).
% 8.06/2.79  tff(c_4556, plain, (![A_816, B_817, C_818]: (k9_subset_1(A_816, B_817, C_818)=k3_xboole_0(B_817, C_818) | ~m1_subset_1(C_818, k1_zfmisc_1(A_816)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.06/2.79  tff(c_4567, plain, (![B_817]: (k9_subset_1('#skF_1', B_817, '#skF_4')=k3_xboole_0(B_817, '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_4556])).
% 8.06/2.79  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_218])).
% 8.06/2.79  tff(c_56, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_218])).
% 8.06/2.79  tff(c_70, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_218])).
% 8.06/2.79  tff(c_52, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_218])).
% 8.06/2.79  tff(c_50, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_218])).
% 8.06/2.79  tff(c_4944, plain, (![D_854, B_858, E_853, C_856, F_857, A_855]: (v1_funct_1(k1_tmap_1(A_855, B_858, C_856, D_854, E_853, F_857)) | ~m1_subset_1(F_857, k1_zfmisc_1(k2_zfmisc_1(D_854, B_858))) | ~v1_funct_2(F_857, D_854, B_858) | ~v1_funct_1(F_857) | ~m1_subset_1(E_853, k1_zfmisc_1(k2_zfmisc_1(C_856, B_858))) | ~v1_funct_2(E_853, C_856, B_858) | ~v1_funct_1(E_853) | ~m1_subset_1(D_854, k1_zfmisc_1(A_855)) | v1_xboole_0(D_854) | ~m1_subset_1(C_856, k1_zfmisc_1(A_855)) | v1_xboole_0(C_856) | v1_xboole_0(B_858) | v1_xboole_0(A_855))), inference(cnfTransformation, [status(thm)], [f_176])).
% 8.06/2.79  tff(c_4946, plain, (![A_855, C_856, E_853]: (v1_funct_1(k1_tmap_1(A_855, '#skF_2', C_856, '#skF_4', E_853, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_853, k1_zfmisc_1(k2_zfmisc_1(C_856, '#skF_2'))) | ~v1_funct_2(E_853, C_856, '#skF_2') | ~v1_funct_1(E_853) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_855)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_856, k1_zfmisc_1(A_855)) | v1_xboole_0(C_856) | v1_xboole_0('#skF_2') | v1_xboole_0(A_855))), inference(resolution, [status(thm)], [c_48, c_4944])).
% 8.06/2.79  tff(c_4951, plain, (![A_855, C_856, E_853]: (v1_funct_1(k1_tmap_1(A_855, '#skF_2', C_856, '#skF_4', E_853, '#skF_6')) | ~m1_subset_1(E_853, k1_zfmisc_1(k2_zfmisc_1(C_856, '#skF_2'))) | ~v1_funct_2(E_853, C_856, '#skF_2') | ~v1_funct_1(E_853) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_855)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_856, k1_zfmisc_1(A_855)) | v1_xboole_0(C_856) | v1_xboole_0('#skF_2') | v1_xboole_0(A_855))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_4946])).
% 8.06/2.79  tff(c_4957, plain, (![A_859, C_860, E_861]: (v1_funct_1(k1_tmap_1(A_859, '#skF_2', C_860, '#skF_4', E_861, '#skF_6')) | ~m1_subset_1(E_861, k1_zfmisc_1(k2_zfmisc_1(C_860, '#skF_2'))) | ~v1_funct_2(E_861, C_860, '#skF_2') | ~v1_funct_1(E_861) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_859)) | ~m1_subset_1(C_860, k1_zfmisc_1(A_859)) | v1_xboole_0(C_860) | v1_xboole_0(A_859))), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_4951])).
% 8.06/2.79  tff(c_4961, plain, (![A_859]: (v1_funct_1(k1_tmap_1(A_859, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_859)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_859)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_859))), inference(resolution, [status(thm)], [c_54, c_4957])).
% 8.06/2.79  tff(c_4968, plain, (![A_859]: (v1_funct_1(k1_tmap_1(A_859, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_859)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_859)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_859))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_4961])).
% 8.06/2.79  tff(c_4977, plain, (![A_863]: (v1_funct_1(k1_tmap_1(A_863, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_863)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_863)) | v1_xboole_0(A_863))), inference(negUnitSimplification, [status(thm)], [c_68, c_4968])).
% 8.06/2.79  tff(c_4980, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_66, c_4977])).
% 8.06/2.79  tff(c_4983, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_4980])).
% 8.06/2.79  tff(c_4984, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_72, c_4983])).
% 8.06/2.79  tff(c_4800, plain, (![A_836, B_837, C_838, D_839]: (k2_partfun1(A_836, B_837, C_838, D_839)=k7_relat_1(C_838, D_839) | ~m1_subset_1(C_838, k1_zfmisc_1(k2_zfmisc_1(A_836, B_837))) | ~v1_funct_1(C_838))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.06/2.79  tff(c_4804, plain, (![D_839]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_839)=k7_relat_1('#skF_5', D_839) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_4800])).
% 8.06/2.79  tff(c_4810, plain, (![D_839]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_839)=k7_relat_1('#skF_5', D_839))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_4804])).
% 8.06/2.79  tff(c_4802, plain, (![D_839]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_839)=k7_relat_1('#skF_6', D_839) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_48, c_4800])).
% 8.06/2.79  tff(c_4807, plain, (![D_839]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_839)=k7_relat_1('#skF_6', D_839))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_4802])).
% 8.06/2.79  tff(c_42, plain, (![C_159, D_160, F_162, A_157, B_158, E_161]: (v1_funct_2(k1_tmap_1(A_157, B_158, C_159, D_160, E_161, F_162), k4_subset_1(A_157, C_159, D_160), B_158) | ~m1_subset_1(F_162, k1_zfmisc_1(k2_zfmisc_1(D_160, B_158))) | ~v1_funct_2(F_162, D_160, B_158) | ~v1_funct_1(F_162) | ~m1_subset_1(E_161, k1_zfmisc_1(k2_zfmisc_1(C_159, B_158))) | ~v1_funct_2(E_161, C_159, B_158) | ~v1_funct_1(E_161) | ~m1_subset_1(D_160, k1_zfmisc_1(A_157)) | v1_xboole_0(D_160) | ~m1_subset_1(C_159, k1_zfmisc_1(A_157)) | v1_xboole_0(C_159) | v1_xboole_0(B_158) | v1_xboole_0(A_157))), inference(cnfTransformation, [status(thm)], [f_176])).
% 8.06/2.79  tff(c_40, plain, (![C_159, D_160, F_162, A_157, B_158, E_161]: (m1_subset_1(k1_tmap_1(A_157, B_158, C_159, D_160, E_161, F_162), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_157, C_159, D_160), B_158))) | ~m1_subset_1(F_162, k1_zfmisc_1(k2_zfmisc_1(D_160, B_158))) | ~v1_funct_2(F_162, D_160, B_158) | ~v1_funct_1(F_162) | ~m1_subset_1(E_161, k1_zfmisc_1(k2_zfmisc_1(C_159, B_158))) | ~v1_funct_2(E_161, C_159, B_158) | ~v1_funct_1(E_161) | ~m1_subset_1(D_160, k1_zfmisc_1(A_157)) | v1_xboole_0(D_160) | ~m1_subset_1(C_159, k1_zfmisc_1(A_157)) | v1_xboole_0(C_159) | v1_xboole_0(B_158) | v1_xboole_0(A_157))), inference(cnfTransformation, [status(thm)], [f_176])).
% 8.06/2.79  tff(c_5114, plain, (![A_894, B_892, E_893, C_896, F_897, D_895]: (k2_partfun1(k4_subset_1(A_894, C_896, D_895), B_892, k1_tmap_1(A_894, B_892, C_896, D_895, E_893, F_897), C_896)=E_893 | ~m1_subset_1(k1_tmap_1(A_894, B_892, C_896, D_895, E_893, F_897), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_894, C_896, D_895), B_892))) | ~v1_funct_2(k1_tmap_1(A_894, B_892, C_896, D_895, E_893, F_897), k4_subset_1(A_894, C_896, D_895), B_892) | ~v1_funct_1(k1_tmap_1(A_894, B_892, C_896, D_895, E_893, F_897)) | k2_partfun1(D_895, B_892, F_897, k9_subset_1(A_894, C_896, D_895))!=k2_partfun1(C_896, B_892, E_893, k9_subset_1(A_894, C_896, D_895)) | ~m1_subset_1(F_897, k1_zfmisc_1(k2_zfmisc_1(D_895, B_892))) | ~v1_funct_2(F_897, D_895, B_892) | ~v1_funct_1(F_897) | ~m1_subset_1(E_893, k1_zfmisc_1(k2_zfmisc_1(C_896, B_892))) | ~v1_funct_2(E_893, C_896, B_892) | ~v1_funct_1(E_893) | ~m1_subset_1(D_895, k1_zfmisc_1(A_894)) | v1_xboole_0(D_895) | ~m1_subset_1(C_896, k1_zfmisc_1(A_894)) | v1_xboole_0(C_896) | v1_xboole_0(B_892) | v1_xboole_0(A_894))), inference(cnfTransformation, [status(thm)], [f_142])).
% 8.06/2.79  tff(c_5613, plain, (![B_997, E_992, F_996, A_994, D_993, C_995]: (k2_partfun1(k4_subset_1(A_994, C_995, D_993), B_997, k1_tmap_1(A_994, B_997, C_995, D_993, E_992, F_996), C_995)=E_992 | ~v1_funct_2(k1_tmap_1(A_994, B_997, C_995, D_993, E_992, F_996), k4_subset_1(A_994, C_995, D_993), B_997) | ~v1_funct_1(k1_tmap_1(A_994, B_997, C_995, D_993, E_992, F_996)) | k2_partfun1(D_993, B_997, F_996, k9_subset_1(A_994, C_995, D_993))!=k2_partfun1(C_995, B_997, E_992, k9_subset_1(A_994, C_995, D_993)) | ~m1_subset_1(F_996, k1_zfmisc_1(k2_zfmisc_1(D_993, B_997))) | ~v1_funct_2(F_996, D_993, B_997) | ~v1_funct_1(F_996) | ~m1_subset_1(E_992, k1_zfmisc_1(k2_zfmisc_1(C_995, B_997))) | ~v1_funct_2(E_992, C_995, B_997) | ~v1_funct_1(E_992) | ~m1_subset_1(D_993, k1_zfmisc_1(A_994)) | v1_xboole_0(D_993) | ~m1_subset_1(C_995, k1_zfmisc_1(A_994)) | v1_xboole_0(C_995) | v1_xboole_0(B_997) | v1_xboole_0(A_994))), inference(resolution, [status(thm)], [c_40, c_5114])).
% 8.06/2.79  tff(c_5911, plain, (![F_1045, D_1042, C_1044, B_1046, A_1043, E_1041]: (k2_partfun1(k4_subset_1(A_1043, C_1044, D_1042), B_1046, k1_tmap_1(A_1043, B_1046, C_1044, D_1042, E_1041, F_1045), C_1044)=E_1041 | ~v1_funct_1(k1_tmap_1(A_1043, B_1046, C_1044, D_1042, E_1041, F_1045)) | k2_partfun1(D_1042, B_1046, F_1045, k9_subset_1(A_1043, C_1044, D_1042))!=k2_partfun1(C_1044, B_1046, E_1041, k9_subset_1(A_1043, C_1044, D_1042)) | ~m1_subset_1(F_1045, k1_zfmisc_1(k2_zfmisc_1(D_1042, B_1046))) | ~v1_funct_2(F_1045, D_1042, B_1046) | ~v1_funct_1(F_1045) | ~m1_subset_1(E_1041, k1_zfmisc_1(k2_zfmisc_1(C_1044, B_1046))) | ~v1_funct_2(E_1041, C_1044, B_1046) | ~v1_funct_1(E_1041) | ~m1_subset_1(D_1042, k1_zfmisc_1(A_1043)) | v1_xboole_0(D_1042) | ~m1_subset_1(C_1044, k1_zfmisc_1(A_1043)) | v1_xboole_0(C_1044) | v1_xboole_0(B_1046) | v1_xboole_0(A_1043))), inference(resolution, [status(thm)], [c_42, c_5613])).
% 8.06/2.79  tff(c_5915, plain, (![A_1043, C_1044, E_1041]: (k2_partfun1(k4_subset_1(A_1043, C_1044, '#skF_4'), '#skF_2', k1_tmap_1(A_1043, '#skF_2', C_1044, '#skF_4', E_1041, '#skF_6'), C_1044)=E_1041 | ~v1_funct_1(k1_tmap_1(A_1043, '#skF_2', C_1044, '#skF_4', E_1041, '#skF_6')) | k2_partfun1(C_1044, '#skF_2', E_1041, k9_subset_1(A_1043, C_1044, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_1043, C_1044, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1041, k1_zfmisc_1(k2_zfmisc_1(C_1044, '#skF_2'))) | ~v1_funct_2(E_1041, C_1044, '#skF_2') | ~v1_funct_1(E_1041) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1043)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1044, k1_zfmisc_1(A_1043)) | v1_xboole_0(C_1044) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1043))), inference(resolution, [status(thm)], [c_48, c_5911])).
% 8.06/2.79  tff(c_5921, plain, (![A_1043, C_1044, E_1041]: (k2_partfun1(k4_subset_1(A_1043, C_1044, '#skF_4'), '#skF_2', k1_tmap_1(A_1043, '#skF_2', C_1044, '#skF_4', E_1041, '#skF_6'), C_1044)=E_1041 | ~v1_funct_1(k1_tmap_1(A_1043, '#skF_2', C_1044, '#skF_4', E_1041, '#skF_6')) | k2_partfun1(C_1044, '#skF_2', E_1041, k9_subset_1(A_1043, C_1044, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1043, C_1044, '#skF_4')) | ~m1_subset_1(E_1041, k1_zfmisc_1(k2_zfmisc_1(C_1044, '#skF_2'))) | ~v1_funct_2(E_1041, C_1044, '#skF_2') | ~v1_funct_1(E_1041) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1043)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1044, k1_zfmisc_1(A_1043)) | v1_xboole_0(C_1044) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1043))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_4807, c_5915])).
% 8.06/2.79  tff(c_6253, plain, (![A_1095, C_1096, E_1097]: (k2_partfun1(k4_subset_1(A_1095, C_1096, '#skF_4'), '#skF_2', k1_tmap_1(A_1095, '#skF_2', C_1096, '#skF_4', E_1097, '#skF_6'), C_1096)=E_1097 | ~v1_funct_1(k1_tmap_1(A_1095, '#skF_2', C_1096, '#skF_4', E_1097, '#skF_6')) | k2_partfun1(C_1096, '#skF_2', E_1097, k9_subset_1(A_1095, C_1096, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1095, C_1096, '#skF_4')) | ~m1_subset_1(E_1097, k1_zfmisc_1(k2_zfmisc_1(C_1096, '#skF_2'))) | ~v1_funct_2(E_1097, C_1096, '#skF_2') | ~v1_funct_1(E_1097) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1095)) | ~m1_subset_1(C_1096, k1_zfmisc_1(A_1095)) | v1_xboole_0(C_1096) | v1_xboole_0(A_1095))), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_5921])).
% 8.06/2.79  tff(c_6260, plain, (![A_1095]: (k2_partfun1(k4_subset_1(A_1095, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1095, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1095, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_1095, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1095, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1095)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1095)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1095))), inference(resolution, [status(thm)], [c_54, c_6253])).
% 8.06/2.79  tff(c_6270, plain, (![A_1095]: (k2_partfun1(k4_subset_1(A_1095, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1095, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1095, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1095, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1095, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1095)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1095)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1095))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_4810, c_6260])).
% 8.06/2.79  tff(c_6295, plain, (![A_1099]: (k2_partfun1(k4_subset_1(A_1099, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1099, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1099, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1099, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1099, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1099)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1099)) | v1_xboole_0(A_1099))), inference(negUnitSimplification, [status(thm)], [c_68, c_6270])).
% 8.06/2.79  tff(c_482, plain, (![A_296, B_297]: (k7_relat_1(A_296, B_297)=k1_xboole_0 | ~r1_xboole_0(B_297, k1_relat_1(A_296)) | ~v1_relat_1(A_296))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.06/2.79  tff(c_516, plain, (![A_300]: (k7_relat_1(A_300, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_300))), inference(resolution, [status(thm)], [c_77, c_482])).
% 8.06/2.79  tff(c_523, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_409, c_516])).
% 8.06/2.79  tff(c_524, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_408, c_516])).
% 8.06/2.79  tff(c_470, plain, (![A_294, B_295]: (r1_xboole_0(A_294, B_295) | ~r1_subset_1(A_294, B_295) | v1_xboole_0(B_295) | v1_xboole_0(A_294))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.06/2.79  tff(c_1829, plain, (![A_434, B_435]: (k3_xboole_0(A_434, B_435)=k1_xboole_0 | ~r1_subset_1(A_434, B_435) | v1_xboole_0(B_435) | v1_xboole_0(A_434))), inference(resolution, [status(thm)], [c_470, c_2])).
% 8.06/2.79  tff(c_1838, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_1829])).
% 8.06/2.79  tff(c_1845, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_68, c_64, c_1838])).
% 8.06/2.79  tff(c_1596, plain, (![A_409, B_410, C_411]: (k9_subset_1(A_409, B_410, C_411)=k3_xboole_0(B_410, C_411) | ~m1_subset_1(C_411, k1_zfmisc_1(A_409)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.06/2.79  tff(c_1607, plain, (![B_410]: (k9_subset_1('#skF_1', B_410, '#skF_4')=k3_xboole_0(B_410, '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_1596])).
% 8.06/2.79  tff(c_1970, plain, (![A_449, C_450, E_447, D_448, F_451, B_452]: (v1_funct_1(k1_tmap_1(A_449, B_452, C_450, D_448, E_447, F_451)) | ~m1_subset_1(F_451, k1_zfmisc_1(k2_zfmisc_1(D_448, B_452))) | ~v1_funct_2(F_451, D_448, B_452) | ~v1_funct_1(F_451) | ~m1_subset_1(E_447, k1_zfmisc_1(k2_zfmisc_1(C_450, B_452))) | ~v1_funct_2(E_447, C_450, B_452) | ~v1_funct_1(E_447) | ~m1_subset_1(D_448, k1_zfmisc_1(A_449)) | v1_xboole_0(D_448) | ~m1_subset_1(C_450, k1_zfmisc_1(A_449)) | v1_xboole_0(C_450) | v1_xboole_0(B_452) | v1_xboole_0(A_449))), inference(cnfTransformation, [status(thm)], [f_176])).
% 8.06/2.79  tff(c_1972, plain, (![A_449, C_450, E_447]: (v1_funct_1(k1_tmap_1(A_449, '#skF_2', C_450, '#skF_4', E_447, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_447, k1_zfmisc_1(k2_zfmisc_1(C_450, '#skF_2'))) | ~v1_funct_2(E_447, C_450, '#skF_2') | ~v1_funct_1(E_447) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_449)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_450, k1_zfmisc_1(A_449)) | v1_xboole_0(C_450) | v1_xboole_0('#skF_2') | v1_xboole_0(A_449))), inference(resolution, [status(thm)], [c_48, c_1970])).
% 8.06/2.79  tff(c_1977, plain, (![A_449, C_450, E_447]: (v1_funct_1(k1_tmap_1(A_449, '#skF_2', C_450, '#skF_4', E_447, '#skF_6')) | ~m1_subset_1(E_447, k1_zfmisc_1(k2_zfmisc_1(C_450, '#skF_2'))) | ~v1_funct_2(E_447, C_450, '#skF_2') | ~v1_funct_1(E_447) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_449)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_450, k1_zfmisc_1(A_449)) | v1_xboole_0(C_450) | v1_xboole_0('#skF_2') | v1_xboole_0(A_449))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1972])).
% 8.06/2.79  tff(c_2034, plain, (![A_460, C_461, E_462]: (v1_funct_1(k1_tmap_1(A_460, '#skF_2', C_461, '#skF_4', E_462, '#skF_6')) | ~m1_subset_1(E_462, k1_zfmisc_1(k2_zfmisc_1(C_461, '#skF_2'))) | ~v1_funct_2(E_462, C_461, '#skF_2') | ~v1_funct_1(E_462) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_460)) | ~m1_subset_1(C_461, k1_zfmisc_1(A_460)) | v1_xboole_0(C_461) | v1_xboole_0(A_460))), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_1977])).
% 8.06/2.79  tff(c_2038, plain, (![A_460]: (v1_funct_1(k1_tmap_1(A_460, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_460)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_460)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_460))), inference(resolution, [status(thm)], [c_54, c_2034])).
% 8.06/2.79  tff(c_2045, plain, (![A_460]: (v1_funct_1(k1_tmap_1(A_460, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_460)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_460)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_460))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_2038])).
% 8.06/2.79  tff(c_2055, plain, (![A_470]: (v1_funct_1(k1_tmap_1(A_470, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_470)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_470)) | v1_xboole_0(A_470))), inference(negUnitSimplification, [status(thm)], [c_68, c_2045])).
% 8.06/2.79  tff(c_2058, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_66, c_2055])).
% 8.06/2.79  tff(c_2061, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2058])).
% 8.06/2.79  tff(c_2062, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_72, c_2061])).
% 8.06/2.79  tff(c_1712, plain, (![A_421, B_422, C_423, D_424]: (k2_partfun1(A_421, B_422, C_423, D_424)=k7_relat_1(C_423, D_424) | ~m1_subset_1(C_423, k1_zfmisc_1(k2_zfmisc_1(A_421, B_422))) | ~v1_funct_1(C_423))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.06/2.79  tff(c_1716, plain, (![D_424]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_424)=k7_relat_1('#skF_5', D_424) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_1712])).
% 8.06/2.79  tff(c_1722, plain, (![D_424]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_424)=k7_relat_1('#skF_5', D_424))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1716])).
% 8.06/2.79  tff(c_1714, plain, (![D_424]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_424)=k7_relat_1('#skF_6', D_424) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_48, c_1712])).
% 8.06/2.79  tff(c_1719, plain, (![D_424]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_424)=k7_relat_1('#skF_6', D_424))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1714])).
% 8.06/2.79  tff(c_2218, plain, (![B_505, A_507, F_510, D_508, C_509, E_506]: (k2_partfun1(k4_subset_1(A_507, C_509, D_508), B_505, k1_tmap_1(A_507, B_505, C_509, D_508, E_506, F_510), D_508)=F_510 | ~m1_subset_1(k1_tmap_1(A_507, B_505, C_509, D_508, E_506, F_510), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_507, C_509, D_508), B_505))) | ~v1_funct_2(k1_tmap_1(A_507, B_505, C_509, D_508, E_506, F_510), k4_subset_1(A_507, C_509, D_508), B_505) | ~v1_funct_1(k1_tmap_1(A_507, B_505, C_509, D_508, E_506, F_510)) | k2_partfun1(D_508, B_505, F_510, k9_subset_1(A_507, C_509, D_508))!=k2_partfun1(C_509, B_505, E_506, k9_subset_1(A_507, C_509, D_508)) | ~m1_subset_1(F_510, k1_zfmisc_1(k2_zfmisc_1(D_508, B_505))) | ~v1_funct_2(F_510, D_508, B_505) | ~v1_funct_1(F_510) | ~m1_subset_1(E_506, k1_zfmisc_1(k2_zfmisc_1(C_509, B_505))) | ~v1_funct_2(E_506, C_509, B_505) | ~v1_funct_1(E_506) | ~m1_subset_1(D_508, k1_zfmisc_1(A_507)) | v1_xboole_0(D_508) | ~m1_subset_1(C_509, k1_zfmisc_1(A_507)) | v1_xboole_0(C_509) | v1_xboole_0(B_505) | v1_xboole_0(A_507))), inference(cnfTransformation, [status(thm)], [f_142])).
% 8.06/2.79  tff(c_2796, plain, (![B_617, C_615, A_614, F_616, D_613, E_612]: (k2_partfun1(k4_subset_1(A_614, C_615, D_613), B_617, k1_tmap_1(A_614, B_617, C_615, D_613, E_612, F_616), D_613)=F_616 | ~v1_funct_2(k1_tmap_1(A_614, B_617, C_615, D_613, E_612, F_616), k4_subset_1(A_614, C_615, D_613), B_617) | ~v1_funct_1(k1_tmap_1(A_614, B_617, C_615, D_613, E_612, F_616)) | k2_partfun1(D_613, B_617, F_616, k9_subset_1(A_614, C_615, D_613))!=k2_partfun1(C_615, B_617, E_612, k9_subset_1(A_614, C_615, D_613)) | ~m1_subset_1(F_616, k1_zfmisc_1(k2_zfmisc_1(D_613, B_617))) | ~v1_funct_2(F_616, D_613, B_617) | ~v1_funct_1(F_616) | ~m1_subset_1(E_612, k1_zfmisc_1(k2_zfmisc_1(C_615, B_617))) | ~v1_funct_2(E_612, C_615, B_617) | ~v1_funct_1(E_612) | ~m1_subset_1(D_613, k1_zfmisc_1(A_614)) | v1_xboole_0(D_613) | ~m1_subset_1(C_615, k1_zfmisc_1(A_614)) | v1_xboole_0(C_615) | v1_xboole_0(B_617) | v1_xboole_0(A_614))), inference(resolution, [status(thm)], [c_40, c_2218])).
% 8.06/2.79  tff(c_2936, plain, (![A_645, F_647, B_648, D_644, C_646, E_643]: (k2_partfun1(k4_subset_1(A_645, C_646, D_644), B_648, k1_tmap_1(A_645, B_648, C_646, D_644, E_643, F_647), D_644)=F_647 | ~v1_funct_1(k1_tmap_1(A_645, B_648, C_646, D_644, E_643, F_647)) | k2_partfun1(D_644, B_648, F_647, k9_subset_1(A_645, C_646, D_644))!=k2_partfun1(C_646, B_648, E_643, k9_subset_1(A_645, C_646, D_644)) | ~m1_subset_1(F_647, k1_zfmisc_1(k2_zfmisc_1(D_644, B_648))) | ~v1_funct_2(F_647, D_644, B_648) | ~v1_funct_1(F_647) | ~m1_subset_1(E_643, k1_zfmisc_1(k2_zfmisc_1(C_646, B_648))) | ~v1_funct_2(E_643, C_646, B_648) | ~v1_funct_1(E_643) | ~m1_subset_1(D_644, k1_zfmisc_1(A_645)) | v1_xboole_0(D_644) | ~m1_subset_1(C_646, k1_zfmisc_1(A_645)) | v1_xboole_0(C_646) | v1_xboole_0(B_648) | v1_xboole_0(A_645))), inference(resolution, [status(thm)], [c_42, c_2796])).
% 8.06/2.79  tff(c_2940, plain, (![A_645, C_646, E_643]: (k2_partfun1(k4_subset_1(A_645, C_646, '#skF_4'), '#skF_2', k1_tmap_1(A_645, '#skF_2', C_646, '#skF_4', E_643, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_645, '#skF_2', C_646, '#skF_4', E_643, '#skF_6')) | k2_partfun1(C_646, '#skF_2', E_643, k9_subset_1(A_645, C_646, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_645, C_646, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_643, k1_zfmisc_1(k2_zfmisc_1(C_646, '#skF_2'))) | ~v1_funct_2(E_643, C_646, '#skF_2') | ~v1_funct_1(E_643) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_645)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_646, k1_zfmisc_1(A_645)) | v1_xboole_0(C_646) | v1_xboole_0('#skF_2') | v1_xboole_0(A_645))), inference(resolution, [status(thm)], [c_48, c_2936])).
% 8.06/2.79  tff(c_2946, plain, (![A_645, C_646, E_643]: (k2_partfun1(k4_subset_1(A_645, C_646, '#skF_4'), '#skF_2', k1_tmap_1(A_645, '#skF_2', C_646, '#skF_4', E_643, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_645, '#skF_2', C_646, '#skF_4', E_643, '#skF_6')) | k2_partfun1(C_646, '#skF_2', E_643, k9_subset_1(A_645, C_646, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_645, C_646, '#skF_4')) | ~m1_subset_1(E_643, k1_zfmisc_1(k2_zfmisc_1(C_646, '#skF_2'))) | ~v1_funct_2(E_643, C_646, '#skF_2') | ~v1_funct_1(E_643) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_645)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_646, k1_zfmisc_1(A_645)) | v1_xboole_0(C_646) | v1_xboole_0('#skF_2') | v1_xboole_0(A_645))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1719, c_2940])).
% 8.06/2.79  tff(c_3289, plain, (![A_696, C_697, E_698]: (k2_partfun1(k4_subset_1(A_696, C_697, '#skF_4'), '#skF_2', k1_tmap_1(A_696, '#skF_2', C_697, '#skF_4', E_698, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_696, '#skF_2', C_697, '#skF_4', E_698, '#skF_6')) | k2_partfun1(C_697, '#skF_2', E_698, k9_subset_1(A_696, C_697, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_696, C_697, '#skF_4')) | ~m1_subset_1(E_698, k1_zfmisc_1(k2_zfmisc_1(C_697, '#skF_2'))) | ~v1_funct_2(E_698, C_697, '#skF_2') | ~v1_funct_1(E_698) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_696)) | ~m1_subset_1(C_697, k1_zfmisc_1(A_696)) | v1_xboole_0(C_697) | v1_xboole_0(A_696))), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_2946])).
% 8.06/2.79  tff(c_3296, plain, (![A_696]: (k2_partfun1(k4_subset_1(A_696, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_696, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_696, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_696, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_696, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_696)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_696)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_696))), inference(resolution, [status(thm)], [c_54, c_3289])).
% 8.06/2.79  tff(c_3306, plain, (![A_696]: (k2_partfun1(k4_subset_1(A_696, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_696, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_696, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_696, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_696, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_696)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_696)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_696))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_1722, c_3296])).
% 8.06/2.79  tff(c_3390, plain, (![A_705]: (k2_partfun1(k4_subset_1(A_705, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_705, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_705, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_705, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_705, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_705)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_705)) | v1_xboole_0(A_705))), inference(negUnitSimplification, [status(thm)], [c_68, c_3306])).
% 8.06/2.79  tff(c_131, plain, (![C_232, A_233, B_234]: (v1_relat_1(C_232) | ~m1_subset_1(C_232, k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.06/2.79  tff(c_138, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_48, c_131])).
% 8.06/2.79  tff(c_199, plain, (![A_248, B_249]: (k7_relat_1(A_248, B_249)=k1_xboole_0 | ~r1_xboole_0(B_249, k1_relat_1(A_248)) | ~v1_relat_1(A_248))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.06/2.79  tff(c_220, plain, (![A_250]: (k7_relat_1(A_250, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_250))), inference(resolution, [status(thm)], [c_77, c_199])).
% 8.06/2.79  tff(c_228, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_138, c_220])).
% 8.06/2.79  tff(c_139, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_131])).
% 8.06/2.79  tff(c_227, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_139, c_220])).
% 8.06/2.79  tff(c_187, plain, (![A_246, B_247]: (r1_xboole_0(A_246, B_247) | ~r1_subset_1(A_246, B_247) | v1_xboole_0(B_247) | v1_xboole_0(A_246))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.06/2.79  tff(c_370, plain, (![A_274, B_275]: (k3_xboole_0(A_274, B_275)=k1_xboole_0 | ~r1_subset_1(A_274, B_275) | v1_xboole_0(B_275) | v1_xboole_0(A_274))), inference(resolution, [status(thm)], [c_187, c_2])).
% 8.06/2.79  tff(c_379, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_370])).
% 8.06/2.79  tff(c_386, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_68, c_64, c_379])).
% 8.06/2.79  tff(c_321, plain, (![A_263, B_264, C_265, D_266]: (k2_partfun1(A_263, B_264, C_265, D_266)=k7_relat_1(C_265, D_266) | ~m1_subset_1(C_265, k1_zfmisc_1(k2_zfmisc_1(A_263, B_264))) | ~v1_funct_1(C_265))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.06/2.79  tff(c_325, plain, (![D_266]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_266)=k7_relat_1('#skF_5', D_266) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_321])).
% 8.06/2.79  tff(c_331, plain, (![D_266]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_266)=k7_relat_1('#skF_5', D_266))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_325])).
% 8.06/2.79  tff(c_323, plain, (![D_266]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_266)=k7_relat_1('#skF_6', D_266) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_48, c_321])).
% 8.06/2.79  tff(c_328, plain, (![D_266]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_266)=k7_relat_1('#skF_6', D_266))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_323])).
% 8.06/2.79  tff(c_280, plain, (![A_257, B_258, C_259]: (k9_subset_1(A_257, B_258, C_259)=k3_xboole_0(B_258, C_259) | ~m1_subset_1(C_259, k1_zfmisc_1(A_257)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.06/2.79  tff(c_291, plain, (![B_258]: (k9_subset_1('#skF_1', B_258, '#skF_4')=k3_xboole_0(B_258, '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_280])).
% 8.06/2.79  tff(c_46, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_218])).
% 8.06/2.79  tff(c_114, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_46])).
% 8.06/2.79  tff(c_293, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_291, c_291, c_114])).
% 8.06/2.79  tff(c_359, plain, (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_331, c_328, c_293])).
% 8.06/2.79  tff(c_387, plain, (k7_relat_1('#skF_5', k1_xboole_0)!=k7_relat_1('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_386, c_386, c_359])).
% 8.06/2.79  tff(c_390, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_228, c_227, c_387])).
% 8.06/2.79  tff(c_391, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_46])).
% 8.06/2.79  tff(c_467, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_391])).
% 8.06/2.79  tff(c_3401, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3390, c_467])).
% 8.06/2.79  tff(c_3415, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_523, c_524, c_1845, c_1607, c_1845, c_1607, c_2062, c_3401])).
% 8.06/2.79  tff(c_3417, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_3415])).
% 8.06/2.79  tff(c_3418, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_391])).
% 8.06/2.79  tff(c_6304, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6295, c_3418])).
% 8.06/2.79  tff(c_6315, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_3462, c_3463, c_4719, c_4567, c_4719, c_4567, c_4984, c_6304])).
% 8.06/2.79  tff(c_6317, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_6315])).
% 8.06/2.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.06/2.79  
% 8.06/2.79  Inference rules
% 8.06/2.79  ----------------------
% 8.06/2.79  #Ref     : 0
% 8.06/2.79  #Sup     : 1285
% 8.06/2.79  #Fact    : 0
% 8.06/2.79  #Define  : 0
% 8.06/2.79  #Split   : 42
% 8.06/2.79  #Chain   : 0
% 8.06/2.79  #Close   : 0
% 8.06/2.79  
% 8.06/2.79  Ordering : KBO
% 8.06/2.79  
% 8.06/2.79  Simplification rules
% 8.06/2.79  ----------------------
% 8.06/2.79  #Subsume      : 161
% 8.06/2.79  #Demod        : 866
% 8.06/2.79  #Tautology    : 639
% 8.06/2.79  #SimpNegUnit  : 296
% 8.06/2.79  #BackRed      : 13
% 8.06/2.79  
% 8.06/2.79  #Partial instantiations: 0
% 8.06/2.79  #Strategies tried      : 1
% 8.06/2.79  
% 8.06/2.79  Timing (in seconds)
% 8.06/2.79  ----------------------
% 8.06/2.79  Preprocessing        : 0.44
% 8.06/2.79  Parsing              : 0.21
% 8.06/2.79  CNF conversion       : 0.06
% 8.06/2.79  Main loop            : 1.57
% 8.06/2.79  Inferencing          : 0.57
% 8.06/2.79  Reduction            : 0.51
% 8.06/2.79  Demodulation         : 0.37
% 8.06/2.79  BG Simplification    : 0.06
% 8.06/2.79  Subsumption          : 0.32
% 8.06/2.79  Abstraction          : 0.07
% 8.06/2.79  MUC search           : 0.00
% 8.06/2.79  Cooper               : 0.00
% 8.06/2.79  Total                : 2.06
% 8.06/2.79  Index Insertion      : 0.00
% 8.06/2.79  Index Deletion       : 0.00
% 8.06/2.79  Index Matching       : 0.00
% 8.06/2.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
