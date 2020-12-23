%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:22 EST 2020

% Result     : Theorem 7.88s
% Output     : CNFRefutation 8.06s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 540 expanded)
%              Number of leaves         :   40 ( 212 expanded)
%              Depth                    :   12
%              Number of atoms          :  602 (2846 expanded)
%              Number of equality atoms :  106 ( 504 expanded)
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

tff(f_202,negated_conjecture,(
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

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_66,axiom,(
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

tff(f_160,axiom,(
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

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_126,axiom,(
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

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_60,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_6,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_86,plain,(
    ! [B_224,A_225] :
      ( v1_relat_1(B_224)
      | ~ m1_subset_1(B_224,k1_zfmisc_1(A_225))
      | ~ v1_relat_1(A_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_92,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_86])).

tff(c_104,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_92])).

tff(c_656,plain,(
    ! [C_300,A_301,B_302] :
      ( v4_relat_1(C_300,A_301)
      | ~ m1_subset_1(C_300,k1_zfmisc_1(k2_zfmisc_1(A_301,B_302))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_664,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_656])).

tff(c_16,plain,(
    ! [B_16,A_15] :
      ( k7_relat_1(B_16,A_15) = B_16
      | ~ v4_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_673,plain,
    ( k7_relat_1('#skF_6','#skF_4') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_664,c_16])).

tff(c_676,plain,(
    k7_relat_1('#skF_6','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_673])).

tff(c_717,plain,(
    ! [C_310,A_311,B_312] :
      ( k7_relat_1(k7_relat_1(C_310,A_311),B_312) = k1_xboole_0
      | ~ r1_xboole_0(A_311,B_312)
      | ~ v1_relat_1(C_310) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_732,plain,(
    ! [B_312] :
      ( k7_relat_1('#skF_6',B_312) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_312)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_676,c_717])).

tff(c_742,plain,(
    ! [B_313] :
      ( k7_relat_1('#skF_6',B_313) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_313) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_732])).

tff(c_759,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_742])).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_54,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_708,plain,(
    ! [A_308,B_309] :
      ( r1_xboole_0(A_308,B_309)
      | ~ r1_subset_1(A_308,B_309)
      | v1_xboole_0(B_309)
      | v1_xboole_0(A_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_3009,plain,(
    ! [A_734,B_735] :
      ( k3_xboole_0(A_734,B_735) = k1_xboole_0
      | ~ r1_subset_1(A_734,B_735)
      | v1_xboole_0(B_735)
      | v1_xboole_0(A_734) ) ),
    inference(resolution,[status(thm)],[c_708,c_2])).

tff(c_3015,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_3009])).

tff(c_3019,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_58,c_3015])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_89,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_86])).

tff(c_101,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_89])).

tff(c_663,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_656])).

tff(c_667,plain,
    ( k7_relat_1('#skF_5','#skF_3') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_663,c_16])).

tff(c_670,plain,(
    k7_relat_1('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_667])).

tff(c_735,plain,(
    ! [B_312] :
      ( k7_relat_1('#skF_5',B_312) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_312)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_670,c_717])).

tff(c_769,plain,(
    ! [B_314] :
      ( k7_relat_1('#skF_5',B_314) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_314) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_735])).

tff(c_786,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_769])).

tff(c_836,plain,(
    ! [A_317,B_318,C_319] :
      ( k9_subset_1(A_317,B_318,C_319) = k3_xboole_0(B_318,C_319)
      | ~ m1_subset_1(C_319,k1_zfmisc_1(A_317)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_848,plain,(
    ! [B_318] : k9_subset_1('#skF_1',B_318,'#skF_4') = k3_xboole_0(B_318,'#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_836])).

tff(c_52,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_50,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_46,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_44,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_3077,plain,(
    ! [B_747,A_748,F_745,C_744,D_749,E_746] :
      ( v1_funct_1(k1_tmap_1(A_748,B_747,C_744,D_749,E_746,F_745))
      | ~ m1_subset_1(F_745,k1_zfmisc_1(k2_zfmisc_1(D_749,B_747)))
      | ~ v1_funct_2(F_745,D_749,B_747)
      | ~ v1_funct_1(F_745)
      | ~ m1_subset_1(E_746,k1_zfmisc_1(k2_zfmisc_1(C_744,B_747)))
      | ~ v1_funct_2(E_746,C_744,B_747)
      | ~ v1_funct_1(E_746)
      | ~ m1_subset_1(D_749,k1_zfmisc_1(A_748))
      | v1_xboole_0(D_749)
      | ~ m1_subset_1(C_744,k1_zfmisc_1(A_748))
      | v1_xboole_0(C_744)
      | v1_xboole_0(B_747)
      | v1_xboole_0(A_748) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_3081,plain,(
    ! [A_748,C_744,E_746] :
      ( v1_funct_1(k1_tmap_1(A_748,'#skF_2',C_744,'#skF_4',E_746,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_746,k1_zfmisc_1(k2_zfmisc_1(C_744,'#skF_2')))
      | ~ v1_funct_2(E_746,C_744,'#skF_2')
      | ~ v1_funct_1(E_746)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_748))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_744,k1_zfmisc_1(A_748))
      | v1_xboole_0(C_744)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_748) ) ),
    inference(resolution,[status(thm)],[c_42,c_3077])).

tff(c_3088,plain,(
    ! [A_748,C_744,E_746] :
      ( v1_funct_1(k1_tmap_1(A_748,'#skF_2',C_744,'#skF_4',E_746,'#skF_6'))
      | ~ m1_subset_1(E_746,k1_zfmisc_1(k2_zfmisc_1(C_744,'#skF_2')))
      | ~ v1_funct_2(E_746,C_744,'#skF_2')
      | ~ v1_funct_1(E_746)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_748))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_744,k1_zfmisc_1(A_748))
      | v1_xboole_0(C_744)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_748) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_3081])).

tff(c_3112,plain,(
    ! [A_754,C_755,E_756] :
      ( v1_funct_1(k1_tmap_1(A_754,'#skF_2',C_755,'#skF_4',E_756,'#skF_6'))
      | ~ m1_subset_1(E_756,k1_zfmisc_1(k2_zfmisc_1(C_755,'#skF_2')))
      | ~ v1_funct_2(E_756,C_755,'#skF_2')
      | ~ v1_funct_1(E_756)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_754))
      | ~ m1_subset_1(C_755,k1_zfmisc_1(A_754))
      | v1_xboole_0(C_755)
      | v1_xboole_0(A_754) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_3088])).

tff(c_3114,plain,(
    ! [A_754] :
      ( v1_funct_1(k1_tmap_1(A_754,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_754))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_754))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_754) ) ),
    inference(resolution,[status(thm)],[c_48,c_3112])).

tff(c_3119,plain,(
    ! [A_754] :
      ( v1_funct_1(k1_tmap_1(A_754,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_754))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_754))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_754) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_3114])).

tff(c_3273,plain,(
    ! [A_786] :
      ( v1_funct_1(k1_tmap_1(A_786,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_786))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_786))
      | v1_xboole_0(A_786) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_3119])).

tff(c_3276,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_3273])).

tff(c_3279,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3276])).

tff(c_3280,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_3279])).

tff(c_969,plain,(
    ! [A_326,B_327,C_328,D_329] :
      ( k2_partfun1(A_326,B_327,C_328,D_329) = k7_relat_1(C_328,D_329)
      | ~ m1_subset_1(C_328,k1_zfmisc_1(k2_zfmisc_1(A_326,B_327)))
      | ~ v1_funct_1(C_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_971,plain,(
    ! [D_329] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_329) = k7_relat_1('#skF_5',D_329)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_969])).

tff(c_976,plain,(
    ! [D_329] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_329) = k7_relat_1('#skF_5',D_329) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_971])).

tff(c_973,plain,(
    ! [D_329] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_329) = k7_relat_1('#skF_6',D_329)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_42,c_969])).

tff(c_979,plain,(
    ! [D_329] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_329) = k7_relat_1('#skF_6',D_329) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_973])).

tff(c_36,plain,(
    ! [F_158,C_155,D_156,E_157,A_153,B_154] :
      ( v1_funct_2(k1_tmap_1(A_153,B_154,C_155,D_156,E_157,F_158),k4_subset_1(A_153,C_155,D_156),B_154)
      | ~ m1_subset_1(F_158,k1_zfmisc_1(k2_zfmisc_1(D_156,B_154)))
      | ~ v1_funct_2(F_158,D_156,B_154)
      | ~ v1_funct_1(F_158)
      | ~ m1_subset_1(E_157,k1_zfmisc_1(k2_zfmisc_1(C_155,B_154)))
      | ~ v1_funct_2(E_157,C_155,B_154)
      | ~ v1_funct_1(E_157)
      | ~ m1_subset_1(D_156,k1_zfmisc_1(A_153))
      | v1_xboole_0(D_156)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(A_153))
      | v1_xboole_0(C_155)
      | v1_xboole_0(B_154)
      | v1_xboole_0(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_34,plain,(
    ! [F_158,C_155,D_156,E_157,A_153,B_154] :
      ( m1_subset_1(k1_tmap_1(A_153,B_154,C_155,D_156,E_157,F_158),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_153,C_155,D_156),B_154)))
      | ~ m1_subset_1(F_158,k1_zfmisc_1(k2_zfmisc_1(D_156,B_154)))
      | ~ v1_funct_2(F_158,D_156,B_154)
      | ~ v1_funct_1(F_158)
      | ~ m1_subset_1(E_157,k1_zfmisc_1(k2_zfmisc_1(C_155,B_154)))
      | ~ v1_funct_2(E_157,C_155,B_154)
      | ~ v1_funct_1(E_157)
      | ~ m1_subset_1(D_156,k1_zfmisc_1(A_153))
      | v1_xboole_0(D_156)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(A_153))
      | v1_xboole_0(C_155)
      | v1_xboole_0(B_154)
      | v1_xboole_0(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_3384,plain,(
    ! [A_801,F_804,C_805,E_806,D_802,B_803] :
      ( k2_partfun1(k4_subset_1(A_801,C_805,D_802),B_803,k1_tmap_1(A_801,B_803,C_805,D_802,E_806,F_804),C_805) = E_806
      | ~ m1_subset_1(k1_tmap_1(A_801,B_803,C_805,D_802,E_806,F_804),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_801,C_805,D_802),B_803)))
      | ~ v1_funct_2(k1_tmap_1(A_801,B_803,C_805,D_802,E_806,F_804),k4_subset_1(A_801,C_805,D_802),B_803)
      | ~ v1_funct_1(k1_tmap_1(A_801,B_803,C_805,D_802,E_806,F_804))
      | k2_partfun1(D_802,B_803,F_804,k9_subset_1(A_801,C_805,D_802)) != k2_partfun1(C_805,B_803,E_806,k9_subset_1(A_801,C_805,D_802))
      | ~ m1_subset_1(F_804,k1_zfmisc_1(k2_zfmisc_1(D_802,B_803)))
      | ~ v1_funct_2(F_804,D_802,B_803)
      | ~ v1_funct_1(F_804)
      | ~ m1_subset_1(E_806,k1_zfmisc_1(k2_zfmisc_1(C_805,B_803)))
      | ~ v1_funct_2(E_806,C_805,B_803)
      | ~ v1_funct_1(E_806)
      | ~ m1_subset_1(D_802,k1_zfmisc_1(A_801))
      | v1_xboole_0(D_802)
      | ~ m1_subset_1(C_805,k1_zfmisc_1(A_801))
      | v1_xboole_0(C_805)
      | v1_xboole_0(B_803)
      | v1_xboole_0(A_801) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_3858,plain,(
    ! [E_920,B_921,A_922,D_923,C_918,F_919] :
      ( k2_partfun1(k4_subset_1(A_922,C_918,D_923),B_921,k1_tmap_1(A_922,B_921,C_918,D_923,E_920,F_919),C_918) = E_920
      | ~ v1_funct_2(k1_tmap_1(A_922,B_921,C_918,D_923,E_920,F_919),k4_subset_1(A_922,C_918,D_923),B_921)
      | ~ v1_funct_1(k1_tmap_1(A_922,B_921,C_918,D_923,E_920,F_919))
      | k2_partfun1(D_923,B_921,F_919,k9_subset_1(A_922,C_918,D_923)) != k2_partfun1(C_918,B_921,E_920,k9_subset_1(A_922,C_918,D_923))
      | ~ m1_subset_1(F_919,k1_zfmisc_1(k2_zfmisc_1(D_923,B_921)))
      | ~ v1_funct_2(F_919,D_923,B_921)
      | ~ v1_funct_1(F_919)
      | ~ m1_subset_1(E_920,k1_zfmisc_1(k2_zfmisc_1(C_918,B_921)))
      | ~ v1_funct_2(E_920,C_918,B_921)
      | ~ v1_funct_1(E_920)
      | ~ m1_subset_1(D_923,k1_zfmisc_1(A_922))
      | v1_xboole_0(D_923)
      | ~ m1_subset_1(C_918,k1_zfmisc_1(A_922))
      | v1_xboole_0(C_918)
      | v1_xboole_0(B_921)
      | v1_xboole_0(A_922) ) ),
    inference(resolution,[status(thm)],[c_34,c_3384])).

tff(c_4365,plain,(
    ! [C_992,A_996,D_997,B_995,F_993,E_994] :
      ( k2_partfun1(k4_subset_1(A_996,C_992,D_997),B_995,k1_tmap_1(A_996,B_995,C_992,D_997,E_994,F_993),C_992) = E_994
      | ~ v1_funct_1(k1_tmap_1(A_996,B_995,C_992,D_997,E_994,F_993))
      | k2_partfun1(D_997,B_995,F_993,k9_subset_1(A_996,C_992,D_997)) != k2_partfun1(C_992,B_995,E_994,k9_subset_1(A_996,C_992,D_997))
      | ~ m1_subset_1(F_993,k1_zfmisc_1(k2_zfmisc_1(D_997,B_995)))
      | ~ v1_funct_2(F_993,D_997,B_995)
      | ~ v1_funct_1(F_993)
      | ~ m1_subset_1(E_994,k1_zfmisc_1(k2_zfmisc_1(C_992,B_995)))
      | ~ v1_funct_2(E_994,C_992,B_995)
      | ~ v1_funct_1(E_994)
      | ~ m1_subset_1(D_997,k1_zfmisc_1(A_996))
      | v1_xboole_0(D_997)
      | ~ m1_subset_1(C_992,k1_zfmisc_1(A_996))
      | v1_xboole_0(C_992)
      | v1_xboole_0(B_995)
      | v1_xboole_0(A_996) ) ),
    inference(resolution,[status(thm)],[c_36,c_3858])).

tff(c_4371,plain,(
    ! [A_996,C_992,E_994] :
      ( k2_partfun1(k4_subset_1(A_996,C_992,'#skF_4'),'#skF_2',k1_tmap_1(A_996,'#skF_2',C_992,'#skF_4',E_994,'#skF_6'),C_992) = E_994
      | ~ v1_funct_1(k1_tmap_1(A_996,'#skF_2',C_992,'#skF_4',E_994,'#skF_6'))
      | k2_partfun1(C_992,'#skF_2',E_994,k9_subset_1(A_996,C_992,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_996,C_992,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_994,k1_zfmisc_1(k2_zfmisc_1(C_992,'#skF_2')))
      | ~ v1_funct_2(E_994,C_992,'#skF_2')
      | ~ v1_funct_1(E_994)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_996))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_992,k1_zfmisc_1(A_996))
      | v1_xboole_0(C_992)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_996) ) ),
    inference(resolution,[status(thm)],[c_42,c_4365])).

tff(c_4379,plain,(
    ! [A_996,C_992,E_994] :
      ( k2_partfun1(k4_subset_1(A_996,C_992,'#skF_4'),'#skF_2',k1_tmap_1(A_996,'#skF_2',C_992,'#skF_4',E_994,'#skF_6'),C_992) = E_994
      | ~ v1_funct_1(k1_tmap_1(A_996,'#skF_2',C_992,'#skF_4',E_994,'#skF_6'))
      | k2_partfun1(C_992,'#skF_2',E_994,k9_subset_1(A_996,C_992,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_996,C_992,'#skF_4'))
      | ~ m1_subset_1(E_994,k1_zfmisc_1(k2_zfmisc_1(C_992,'#skF_2')))
      | ~ v1_funct_2(E_994,C_992,'#skF_2')
      | ~ v1_funct_1(E_994)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_996))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_992,k1_zfmisc_1(A_996))
      | v1_xboole_0(C_992)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_996) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_979,c_4371])).

tff(c_4706,plain,(
    ! [A_1063,C_1064,E_1065] :
      ( k2_partfun1(k4_subset_1(A_1063,C_1064,'#skF_4'),'#skF_2',k1_tmap_1(A_1063,'#skF_2',C_1064,'#skF_4',E_1065,'#skF_6'),C_1064) = E_1065
      | ~ v1_funct_1(k1_tmap_1(A_1063,'#skF_2',C_1064,'#skF_4',E_1065,'#skF_6'))
      | k2_partfun1(C_1064,'#skF_2',E_1065,k9_subset_1(A_1063,C_1064,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1063,C_1064,'#skF_4'))
      | ~ m1_subset_1(E_1065,k1_zfmisc_1(k2_zfmisc_1(C_1064,'#skF_2')))
      | ~ v1_funct_2(E_1065,C_1064,'#skF_2')
      | ~ v1_funct_1(E_1065)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1063))
      | ~ m1_subset_1(C_1064,k1_zfmisc_1(A_1063))
      | v1_xboole_0(C_1064)
      | v1_xboole_0(A_1063) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_4379])).

tff(c_4711,plain,(
    ! [A_1063] :
      ( k2_partfun1(k4_subset_1(A_1063,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1063,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1063,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1063,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1063,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1063))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1063))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1063) ) ),
    inference(resolution,[status(thm)],[c_48,c_4706])).

tff(c_4719,plain,(
    ! [A_1063] :
      ( k2_partfun1(k4_subset_1(A_1063,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1063,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1063,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1063,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1063,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1063))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1063))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1063) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_976,c_4711])).

tff(c_4725,plain,(
    ! [A_1066] :
      ( k2_partfun1(k4_subset_1(A_1066,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1066,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1066,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1066,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1066,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1066))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1066))
      | v1_xboole_0(A_1066) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_4719])).

tff(c_1086,plain,(
    ! [A_339,B_340] :
      ( k3_xboole_0(A_339,B_340) = k1_xboole_0
      | ~ r1_subset_1(A_339,B_340)
      | v1_xboole_0(B_340)
      | v1_xboole_0(A_339) ) ),
    inference(resolution,[status(thm)],[c_708,c_2])).

tff(c_1092,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_1086])).

tff(c_1096,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_58,c_1092])).

tff(c_1177,plain,(
    ! [A_361,C_357,F_358,D_362,B_360,E_359] :
      ( v1_funct_1(k1_tmap_1(A_361,B_360,C_357,D_362,E_359,F_358))
      | ~ m1_subset_1(F_358,k1_zfmisc_1(k2_zfmisc_1(D_362,B_360)))
      | ~ v1_funct_2(F_358,D_362,B_360)
      | ~ v1_funct_1(F_358)
      | ~ m1_subset_1(E_359,k1_zfmisc_1(k2_zfmisc_1(C_357,B_360)))
      | ~ v1_funct_2(E_359,C_357,B_360)
      | ~ v1_funct_1(E_359)
      | ~ m1_subset_1(D_362,k1_zfmisc_1(A_361))
      | v1_xboole_0(D_362)
      | ~ m1_subset_1(C_357,k1_zfmisc_1(A_361))
      | v1_xboole_0(C_357)
      | v1_xboole_0(B_360)
      | v1_xboole_0(A_361) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1181,plain,(
    ! [A_361,C_357,E_359] :
      ( v1_funct_1(k1_tmap_1(A_361,'#skF_2',C_357,'#skF_4',E_359,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_359,k1_zfmisc_1(k2_zfmisc_1(C_357,'#skF_2')))
      | ~ v1_funct_2(E_359,C_357,'#skF_2')
      | ~ v1_funct_1(E_359)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_361))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_357,k1_zfmisc_1(A_361))
      | v1_xboole_0(C_357)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_361) ) ),
    inference(resolution,[status(thm)],[c_42,c_1177])).

tff(c_1188,plain,(
    ! [A_361,C_357,E_359] :
      ( v1_funct_1(k1_tmap_1(A_361,'#skF_2',C_357,'#skF_4',E_359,'#skF_6'))
      | ~ m1_subset_1(E_359,k1_zfmisc_1(k2_zfmisc_1(C_357,'#skF_2')))
      | ~ v1_funct_2(E_359,C_357,'#skF_2')
      | ~ v1_funct_1(E_359)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_361))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_357,k1_zfmisc_1(A_361))
      | v1_xboole_0(C_357)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_361) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_1181])).

tff(c_1433,plain,(
    ! [A_404,C_405,E_406] :
      ( v1_funct_1(k1_tmap_1(A_404,'#skF_2',C_405,'#skF_4',E_406,'#skF_6'))
      | ~ m1_subset_1(E_406,k1_zfmisc_1(k2_zfmisc_1(C_405,'#skF_2')))
      | ~ v1_funct_2(E_406,C_405,'#skF_2')
      | ~ v1_funct_1(E_406)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_404))
      | ~ m1_subset_1(C_405,k1_zfmisc_1(A_404))
      | v1_xboole_0(C_405)
      | v1_xboole_0(A_404) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_1188])).

tff(c_1438,plain,(
    ! [A_404] :
      ( v1_funct_1(k1_tmap_1(A_404,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_404))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_404))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_404) ) ),
    inference(resolution,[status(thm)],[c_48,c_1433])).

tff(c_1446,plain,(
    ! [A_404] :
      ( v1_funct_1(k1_tmap_1(A_404,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_404))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_404))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_404) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1438])).

tff(c_1459,plain,(
    ! [A_408] :
      ( v1_funct_1(k1_tmap_1(A_408,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_408))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_408))
      | v1_xboole_0(A_408) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1446])).

tff(c_1462,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_1459])).

tff(c_1465,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1462])).

tff(c_1466,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1465])).

tff(c_1509,plain,(
    ! [C_423,E_424,D_420,B_421,A_419,F_422] :
      ( k2_partfun1(k4_subset_1(A_419,C_423,D_420),B_421,k1_tmap_1(A_419,B_421,C_423,D_420,E_424,F_422),D_420) = F_422
      | ~ m1_subset_1(k1_tmap_1(A_419,B_421,C_423,D_420,E_424,F_422),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_419,C_423,D_420),B_421)))
      | ~ v1_funct_2(k1_tmap_1(A_419,B_421,C_423,D_420,E_424,F_422),k4_subset_1(A_419,C_423,D_420),B_421)
      | ~ v1_funct_1(k1_tmap_1(A_419,B_421,C_423,D_420,E_424,F_422))
      | k2_partfun1(D_420,B_421,F_422,k9_subset_1(A_419,C_423,D_420)) != k2_partfun1(C_423,B_421,E_424,k9_subset_1(A_419,C_423,D_420))
      | ~ m1_subset_1(F_422,k1_zfmisc_1(k2_zfmisc_1(D_420,B_421)))
      | ~ v1_funct_2(F_422,D_420,B_421)
      | ~ v1_funct_1(F_422)
      | ~ m1_subset_1(E_424,k1_zfmisc_1(k2_zfmisc_1(C_423,B_421)))
      | ~ v1_funct_2(E_424,C_423,B_421)
      | ~ v1_funct_1(E_424)
      | ~ m1_subset_1(D_420,k1_zfmisc_1(A_419))
      | v1_xboole_0(D_420)
      | ~ m1_subset_1(C_423,k1_zfmisc_1(A_419))
      | v1_xboole_0(C_423)
      | v1_xboole_0(B_421)
      | v1_xboole_0(A_419) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2027,plain,(
    ! [D_533,A_532,E_530,F_529,B_531,C_528] :
      ( k2_partfun1(k4_subset_1(A_532,C_528,D_533),B_531,k1_tmap_1(A_532,B_531,C_528,D_533,E_530,F_529),D_533) = F_529
      | ~ v1_funct_2(k1_tmap_1(A_532,B_531,C_528,D_533,E_530,F_529),k4_subset_1(A_532,C_528,D_533),B_531)
      | ~ v1_funct_1(k1_tmap_1(A_532,B_531,C_528,D_533,E_530,F_529))
      | k2_partfun1(D_533,B_531,F_529,k9_subset_1(A_532,C_528,D_533)) != k2_partfun1(C_528,B_531,E_530,k9_subset_1(A_532,C_528,D_533))
      | ~ m1_subset_1(F_529,k1_zfmisc_1(k2_zfmisc_1(D_533,B_531)))
      | ~ v1_funct_2(F_529,D_533,B_531)
      | ~ v1_funct_1(F_529)
      | ~ m1_subset_1(E_530,k1_zfmisc_1(k2_zfmisc_1(C_528,B_531)))
      | ~ v1_funct_2(E_530,C_528,B_531)
      | ~ v1_funct_1(E_530)
      | ~ m1_subset_1(D_533,k1_zfmisc_1(A_532))
      | v1_xboole_0(D_533)
      | ~ m1_subset_1(C_528,k1_zfmisc_1(A_532))
      | v1_xboole_0(C_528)
      | v1_xboole_0(B_531)
      | v1_xboole_0(A_532) ) ),
    inference(resolution,[status(thm)],[c_34,c_1509])).

tff(c_2350,plain,(
    ! [E_587,D_590,F_586,A_589,B_588,C_585] :
      ( k2_partfun1(k4_subset_1(A_589,C_585,D_590),B_588,k1_tmap_1(A_589,B_588,C_585,D_590,E_587,F_586),D_590) = F_586
      | ~ v1_funct_1(k1_tmap_1(A_589,B_588,C_585,D_590,E_587,F_586))
      | k2_partfun1(D_590,B_588,F_586,k9_subset_1(A_589,C_585,D_590)) != k2_partfun1(C_585,B_588,E_587,k9_subset_1(A_589,C_585,D_590))
      | ~ m1_subset_1(F_586,k1_zfmisc_1(k2_zfmisc_1(D_590,B_588)))
      | ~ v1_funct_2(F_586,D_590,B_588)
      | ~ v1_funct_1(F_586)
      | ~ m1_subset_1(E_587,k1_zfmisc_1(k2_zfmisc_1(C_585,B_588)))
      | ~ v1_funct_2(E_587,C_585,B_588)
      | ~ v1_funct_1(E_587)
      | ~ m1_subset_1(D_590,k1_zfmisc_1(A_589))
      | v1_xboole_0(D_590)
      | ~ m1_subset_1(C_585,k1_zfmisc_1(A_589))
      | v1_xboole_0(C_585)
      | v1_xboole_0(B_588)
      | v1_xboole_0(A_589) ) ),
    inference(resolution,[status(thm)],[c_36,c_2027])).

tff(c_2356,plain,(
    ! [A_589,C_585,E_587] :
      ( k2_partfun1(k4_subset_1(A_589,C_585,'#skF_4'),'#skF_2',k1_tmap_1(A_589,'#skF_2',C_585,'#skF_4',E_587,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_589,'#skF_2',C_585,'#skF_4',E_587,'#skF_6'))
      | k2_partfun1(C_585,'#skF_2',E_587,k9_subset_1(A_589,C_585,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_589,C_585,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_587,k1_zfmisc_1(k2_zfmisc_1(C_585,'#skF_2')))
      | ~ v1_funct_2(E_587,C_585,'#skF_2')
      | ~ v1_funct_1(E_587)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_589))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_585,k1_zfmisc_1(A_589))
      | v1_xboole_0(C_585)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_589) ) ),
    inference(resolution,[status(thm)],[c_42,c_2350])).

tff(c_2364,plain,(
    ! [A_589,C_585,E_587] :
      ( k2_partfun1(k4_subset_1(A_589,C_585,'#skF_4'),'#skF_2',k1_tmap_1(A_589,'#skF_2',C_585,'#skF_4',E_587,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_589,'#skF_2',C_585,'#skF_4',E_587,'#skF_6'))
      | k2_partfun1(C_585,'#skF_2',E_587,k9_subset_1(A_589,C_585,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_589,C_585,'#skF_4'))
      | ~ m1_subset_1(E_587,k1_zfmisc_1(k2_zfmisc_1(C_585,'#skF_2')))
      | ~ v1_funct_2(E_587,C_585,'#skF_2')
      | ~ v1_funct_1(E_587)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_589))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_585,k1_zfmisc_1(A_589))
      | v1_xboole_0(C_585)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_589) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_979,c_2356])).

tff(c_2915,plain,(
    ! [A_724,C_725,E_726] :
      ( k2_partfun1(k4_subset_1(A_724,C_725,'#skF_4'),'#skF_2',k1_tmap_1(A_724,'#skF_2',C_725,'#skF_4',E_726,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_724,'#skF_2',C_725,'#skF_4',E_726,'#skF_6'))
      | k2_partfun1(C_725,'#skF_2',E_726,k9_subset_1(A_724,C_725,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_724,C_725,'#skF_4'))
      | ~ m1_subset_1(E_726,k1_zfmisc_1(k2_zfmisc_1(C_725,'#skF_2')))
      | ~ v1_funct_2(E_726,C_725,'#skF_2')
      | ~ v1_funct_1(E_726)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_724))
      | ~ m1_subset_1(C_725,k1_zfmisc_1(A_724))
      | v1_xboole_0(C_725)
      | v1_xboole_0(A_724) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_2364])).

tff(c_2920,plain,(
    ! [A_724] :
      ( k2_partfun1(k4_subset_1(A_724,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_724,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_724,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_724,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_724,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_724))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_724))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_724) ) ),
    inference(resolution,[status(thm)],[c_48,c_2915])).

tff(c_2928,plain,(
    ! [A_724] :
      ( k2_partfun1(k4_subset_1(A_724,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_724,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_724,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_724,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_724,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_724))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_724))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_724) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_976,c_2920])).

tff(c_2943,plain,(
    ! [A_730] :
      ( k2_partfun1(k4_subset_1(A_730,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_730,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_730,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_730,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_730,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_730))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_730))
      | v1_xboole_0(A_730) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2928])).

tff(c_119,plain,(
    ! [C_231,A_232,B_233] :
      ( v4_relat_1(C_231,A_232)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(A_232,B_233))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_127,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_119])).

tff(c_136,plain,
    ( k7_relat_1('#skF_6','#skF_4') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_127,c_16])).

tff(c_139,plain,(
    k7_relat_1('#skF_6','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_136])).

tff(c_217,plain,(
    ! [C_245,A_246,B_247] :
      ( k7_relat_1(k7_relat_1(C_245,A_246),B_247) = k1_xboole_0
      | ~ r1_xboole_0(A_246,B_247)
      | ~ v1_relat_1(C_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_232,plain,(
    ! [B_247] :
      ( k7_relat_1('#skF_6',B_247) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_247)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_217])).

tff(c_253,plain,(
    ! [B_252] :
      ( k7_relat_1('#skF_6',B_252) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_252) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_232])).

tff(c_270,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_253])).

tff(c_148,plain,(
    ! [A_234,B_235] :
      ( r1_xboole_0(A_234,B_235)
      | ~ r1_subset_1(A_234,B_235)
      | v1_xboole_0(B_235)
      | v1_xboole_0(A_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_549,plain,(
    ! [A_279,B_280] :
      ( k3_xboole_0(A_279,B_280) = k1_xboole_0
      | ~ r1_subset_1(A_279,B_280)
      | v1_xboole_0(B_280)
      | v1_xboole_0(A_279) ) ),
    inference(resolution,[status(thm)],[c_148,c_2])).

tff(c_555,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_549])).

tff(c_559,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_58,c_555])).

tff(c_126,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_119])).

tff(c_130,plain,
    ( k7_relat_1('#skF_5','#skF_3') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_126,c_16])).

tff(c_133,plain,(
    k7_relat_1('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_130])).

tff(c_235,plain,(
    ! [B_247] :
      ( k7_relat_1('#skF_5',B_247) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_247)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_217])).

tff(c_280,plain,(
    ! [B_253] :
      ( k7_relat_1('#skF_5',B_253) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_253) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_235])).

tff(c_297,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_280])).

tff(c_242,plain,(
    ! [A_248,B_249,C_250,D_251] :
      ( k2_partfun1(A_248,B_249,C_250,D_251) = k7_relat_1(C_250,D_251)
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(A_248,B_249)))
      | ~ v1_funct_1(C_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_246,plain,(
    ! [D_251] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_251) = k7_relat_1('#skF_6',D_251)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_42,c_242])).

tff(c_252,plain,(
    ! [D_251] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_251) = k7_relat_1('#skF_6',D_251) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_246])).

tff(c_244,plain,(
    ! [D_251] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_251) = k7_relat_1('#skF_5',D_251)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_242])).

tff(c_249,plain,(
    ! [D_251] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_251) = k7_relat_1('#skF_5',D_251) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_244])).

tff(c_167,plain,(
    ! [A_238,B_239,C_240] :
      ( k9_subset_1(A_238,B_239,C_240) = k3_xboole_0(B_239,C_240)
      | ~ m1_subset_1(C_240,k1_zfmisc_1(A_238)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_179,plain,(
    ! [B_239] : k9_subset_1('#skF_1',B_239,'#skF_4') = k3_xboole_0(B_239,'#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_167])).

tff(c_40,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_107,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_189,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_179,c_107])).

tff(c_650,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_559,c_297,c_559,c_252,c_249,c_189])).

tff(c_651,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_1065,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_651])).

tff(c_2954,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2943,c_1065])).

tff(c_2968,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_759,c_1096,c_786,c_1096,c_848,c_848,c_1466,c_2954])).

tff(c_2970,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_2968])).

tff(c_2971,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_651])).

tff(c_4734,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4725,c_2971])).

tff(c_4745,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_759,c_3019,c_786,c_3019,c_848,c_848,c_3280,c_4734])).

tff(c_4747,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_4745])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:05:12 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.88/2.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.94/2.82  
% 7.94/2.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.94/2.82  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.94/2.82  
% 7.94/2.82  %Foreground sorts:
% 7.94/2.82  
% 7.94/2.82  
% 7.94/2.82  %Background operators:
% 7.94/2.82  
% 7.94/2.82  
% 7.94/2.82  %Foreground operators:
% 7.94/2.82  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 7.94/2.82  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.94/2.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.94/2.82  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.94/2.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.94/2.82  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 7.94/2.82  tff('#skF_5', type, '#skF_5': $i).
% 7.94/2.82  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.94/2.82  tff('#skF_6', type, '#skF_6': $i).
% 7.94/2.82  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.94/2.82  tff('#skF_2', type, '#skF_2': $i).
% 7.94/2.82  tff('#skF_3', type, '#skF_3': $i).
% 7.94/2.82  tff('#skF_1', type, '#skF_1': $i).
% 7.94/2.82  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.94/2.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.94/2.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.94/2.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.94/2.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.94/2.82  tff('#skF_4', type, '#skF_4': $i).
% 7.94/2.82  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.94/2.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.94/2.82  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 7.94/2.82  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.94/2.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.94/2.82  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.94/2.82  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.94/2.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.94/2.82  
% 8.06/2.84  tff(f_202, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 8.06/2.84  tff(f_31, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 8.06/2.84  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.06/2.84  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.06/2.84  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.06/2.84  tff(f_56, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 8.06/2.84  tff(f_50, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 8.06/2.84  tff(f_66, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 8.06/2.84  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.06/2.84  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 8.06/2.84  tff(f_160, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 8.06/2.84  tff(f_78, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 8.06/2.84  tff(f_126, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 8.06/2.84  tff(c_66, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_202])).
% 8.06/2.84  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_202])).
% 8.06/2.84  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_202])).
% 8.06/2.84  tff(c_6, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.06/2.84  tff(c_12, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.06/2.84  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_202])).
% 8.06/2.84  tff(c_86, plain, (![B_224, A_225]: (v1_relat_1(B_224) | ~m1_subset_1(B_224, k1_zfmisc_1(A_225)) | ~v1_relat_1(A_225))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.06/2.84  tff(c_92, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_42, c_86])).
% 8.06/2.84  tff(c_104, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_92])).
% 8.06/2.84  tff(c_656, plain, (![C_300, A_301, B_302]: (v4_relat_1(C_300, A_301) | ~m1_subset_1(C_300, k1_zfmisc_1(k2_zfmisc_1(A_301, B_302))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.06/2.84  tff(c_664, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_656])).
% 8.06/2.84  tff(c_16, plain, (![B_16, A_15]: (k7_relat_1(B_16, A_15)=B_16 | ~v4_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.06/2.84  tff(c_673, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_664, c_16])).
% 8.06/2.84  tff(c_676, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_673])).
% 8.06/2.84  tff(c_717, plain, (![C_310, A_311, B_312]: (k7_relat_1(k7_relat_1(C_310, A_311), B_312)=k1_xboole_0 | ~r1_xboole_0(A_311, B_312) | ~v1_relat_1(C_310))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.06/2.84  tff(c_732, plain, (![B_312]: (k7_relat_1('#skF_6', B_312)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_312) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_676, c_717])).
% 8.06/2.84  tff(c_742, plain, (![B_313]: (k7_relat_1('#skF_6', B_313)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_313))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_732])).
% 8.06/2.84  tff(c_759, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_742])).
% 8.06/2.84  tff(c_62, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_202])).
% 8.06/2.84  tff(c_58, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_202])).
% 8.06/2.84  tff(c_54, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_202])).
% 8.06/2.84  tff(c_708, plain, (![A_308, B_309]: (r1_xboole_0(A_308, B_309) | ~r1_subset_1(A_308, B_309) | v1_xboole_0(B_309) | v1_xboole_0(A_308))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.06/2.84  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.06/2.84  tff(c_3009, plain, (![A_734, B_735]: (k3_xboole_0(A_734, B_735)=k1_xboole_0 | ~r1_subset_1(A_734, B_735) | v1_xboole_0(B_735) | v1_xboole_0(A_734))), inference(resolution, [status(thm)], [c_708, c_2])).
% 8.06/2.84  tff(c_3015, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_54, c_3009])).
% 8.06/2.84  tff(c_3019, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_62, c_58, c_3015])).
% 8.06/2.84  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_202])).
% 8.06/2.84  tff(c_89, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_48, c_86])).
% 8.06/2.84  tff(c_101, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_89])).
% 8.06/2.84  tff(c_663, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_656])).
% 8.06/2.84  tff(c_667, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_663, c_16])).
% 8.06/2.84  tff(c_670, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_101, c_667])).
% 8.06/2.84  tff(c_735, plain, (![B_312]: (k7_relat_1('#skF_5', B_312)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_312) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_670, c_717])).
% 8.06/2.84  tff(c_769, plain, (![B_314]: (k7_relat_1('#skF_5', B_314)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_314))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_735])).
% 8.06/2.84  tff(c_786, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_769])).
% 8.06/2.84  tff(c_836, plain, (![A_317, B_318, C_319]: (k9_subset_1(A_317, B_318, C_319)=k3_xboole_0(B_318, C_319) | ~m1_subset_1(C_319, k1_zfmisc_1(A_317)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.06/2.84  tff(c_848, plain, (![B_318]: (k9_subset_1('#skF_1', B_318, '#skF_4')=k3_xboole_0(B_318, '#skF_4'))), inference(resolution, [status(thm)], [c_56, c_836])).
% 8.06/2.84  tff(c_52, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_202])).
% 8.06/2.84  tff(c_50, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_202])).
% 8.06/2.84  tff(c_64, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_202])).
% 8.06/2.84  tff(c_46, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_202])).
% 8.06/2.84  tff(c_44, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_202])).
% 8.06/2.84  tff(c_3077, plain, (![B_747, A_748, F_745, C_744, D_749, E_746]: (v1_funct_1(k1_tmap_1(A_748, B_747, C_744, D_749, E_746, F_745)) | ~m1_subset_1(F_745, k1_zfmisc_1(k2_zfmisc_1(D_749, B_747))) | ~v1_funct_2(F_745, D_749, B_747) | ~v1_funct_1(F_745) | ~m1_subset_1(E_746, k1_zfmisc_1(k2_zfmisc_1(C_744, B_747))) | ~v1_funct_2(E_746, C_744, B_747) | ~v1_funct_1(E_746) | ~m1_subset_1(D_749, k1_zfmisc_1(A_748)) | v1_xboole_0(D_749) | ~m1_subset_1(C_744, k1_zfmisc_1(A_748)) | v1_xboole_0(C_744) | v1_xboole_0(B_747) | v1_xboole_0(A_748))), inference(cnfTransformation, [status(thm)], [f_160])).
% 8.06/2.84  tff(c_3081, plain, (![A_748, C_744, E_746]: (v1_funct_1(k1_tmap_1(A_748, '#skF_2', C_744, '#skF_4', E_746, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_746, k1_zfmisc_1(k2_zfmisc_1(C_744, '#skF_2'))) | ~v1_funct_2(E_746, C_744, '#skF_2') | ~v1_funct_1(E_746) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_748)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_744, k1_zfmisc_1(A_748)) | v1_xboole_0(C_744) | v1_xboole_0('#skF_2') | v1_xboole_0(A_748))), inference(resolution, [status(thm)], [c_42, c_3077])).
% 8.06/2.84  tff(c_3088, plain, (![A_748, C_744, E_746]: (v1_funct_1(k1_tmap_1(A_748, '#skF_2', C_744, '#skF_4', E_746, '#skF_6')) | ~m1_subset_1(E_746, k1_zfmisc_1(k2_zfmisc_1(C_744, '#skF_2'))) | ~v1_funct_2(E_746, C_744, '#skF_2') | ~v1_funct_1(E_746) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_748)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_744, k1_zfmisc_1(A_748)) | v1_xboole_0(C_744) | v1_xboole_0('#skF_2') | v1_xboole_0(A_748))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_3081])).
% 8.06/2.84  tff(c_3112, plain, (![A_754, C_755, E_756]: (v1_funct_1(k1_tmap_1(A_754, '#skF_2', C_755, '#skF_4', E_756, '#skF_6')) | ~m1_subset_1(E_756, k1_zfmisc_1(k2_zfmisc_1(C_755, '#skF_2'))) | ~v1_funct_2(E_756, C_755, '#skF_2') | ~v1_funct_1(E_756) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_754)) | ~m1_subset_1(C_755, k1_zfmisc_1(A_754)) | v1_xboole_0(C_755) | v1_xboole_0(A_754))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_3088])).
% 8.06/2.84  tff(c_3114, plain, (![A_754]: (v1_funct_1(k1_tmap_1(A_754, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_754)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_754)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_754))), inference(resolution, [status(thm)], [c_48, c_3112])).
% 8.06/2.84  tff(c_3119, plain, (![A_754]: (v1_funct_1(k1_tmap_1(A_754, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_754)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_754)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_754))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_3114])).
% 8.06/2.84  tff(c_3273, plain, (![A_786]: (v1_funct_1(k1_tmap_1(A_786, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_786)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_786)) | v1_xboole_0(A_786))), inference(negUnitSimplification, [status(thm)], [c_62, c_3119])).
% 8.06/2.84  tff(c_3276, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_3273])).
% 8.06/2.84  tff(c_3279, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_3276])).
% 8.06/2.84  tff(c_3280, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_66, c_3279])).
% 8.06/2.84  tff(c_969, plain, (![A_326, B_327, C_328, D_329]: (k2_partfun1(A_326, B_327, C_328, D_329)=k7_relat_1(C_328, D_329) | ~m1_subset_1(C_328, k1_zfmisc_1(k2_zfmisc_1(A_326, B_327))) | ~v1_funct_1(C_328))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.06/2.84  tff(c_971, plain, (![D_329]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_329)=k7_relat_1('#skF_5', D_329) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_48, c_969])).
% 8.06/2.84  tff(c_976, plain, (![D_329]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_329)=k7_relat_1('#skF_5', D_329))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_971])).
% 8.06/2.84  tff(c_973, plain, (![D_329]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_329)=k7_relat_1('#skF_6', D_329) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_42, c_969])).
% 8.06/2.84  tff(c_979, plain, (![D_329]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_329)=k7_relat_1('#skF_6', D_329))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_973])).
% 8.06/2.84  tff(c_36, plain, (![F_158, C_155, D_156, E_157, A_153, B_154]: (v1_funct_2(k1_tmap_1(A_153, B_154, C_155, D_156, E_157, F_158), k4_subset_1(A_153, C_155, D_156), B_154) | ~m1_subset_1(F_158, k1_zfmisc_1(k2_zfmisc_1(D_156, B_154))) | ~v1_funct_2(F_158, D_156, B_154) | ~v1_funct_1(F_158) | ~m1_subset_1(E_157, k1_zfmisc_1(k2_zfmisc_1(C_155, B_154))) | ~v1_funct_2(E_157, C_155, B_154) | ~v1_funct_1(E_157) | ~m1_subset_1(D_156, k1_zfmisc_1(A_153)) | v1_xboole_0(D_156) | ~m1_subset_1(C_155, k1_zfmisc_1(A_153)) | v1_xboole_0(C_155) | v1_xboole_0(B_154) | v1_xboole_0(A_153))), inference(cnfTransformation, [status(thm)], [f_160])).
% 8.06/2.84  tff(c_34, plain, (![F_158, C_155, D_156, E_157, A_153, B_154]: (m1_subset_1(k1_tmap_1(A_153, B_154, C_155, D_156, E_157, F_158), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_153, C_155, D_156), B_154))) | ~m1_subset_1(F_158, k1_zfmisc_1(k2_zfmisc_1(D_156, B_154))) | ~v1_funct_2(F_158, D_156, B_154) | ~v1_funct_1(F_158) | ~m1_subset_1(E_157, k1_zfmisc_1(k2_zfmisc_1(C_155, B_154))) | ~v1_funct_2(E_157, C_155, B_154) | ~v1_funct_1(E_157) | ~m1_subset_1(D_156, k1_zfmisc_1(A_153)) | v1_xboole_0(D_156) | ~m1_subset_1(C_155, k1_zfmisc_1(A_153)) | v1_xboole_0(C_155) | v1_xboole_0(B_154) | v1_xboole_0(A_153))), inference(cnfTransformation, [status(thm)], [f_160])).
% 8.06/2.84  tff(c_3384, plain, (![A_801, F_804, C_805, E_806, D_802, B_803]: (k2_partfun1(k4_subset_1(A_801, C_805, D_802), B_803, k1_tmap_1(A_801, B_803, C_805, D_802, E_806, F_804), C_805)=E_806 | ~m1_subset_1(k1_tmap_1(A_801, B_803, C_805, D_802, E_806, F_804), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_801, C_805, D_802), B_803))) | ~v1_funct_2(k1_tmap_1(A_801, B_803, C_805, D_802, E_806, F_804), k4_subset_1(A_801, C_805, D_802), B_803) | ~v1_funct_1(k1_tmap_1(A_801, B_803, C_805, D_802, E_806, F_804)) | k2_partfun1(D_802, B_803, F_804, k9_subset_1(A_801, C_805, D_802))!=k2_partfun1(C_805, B_803, E_806, k9_subset_1(A_801, C_805, D_802)) | ~m1_subset_1(F_804, k1_zfmisc_1(k2_zfmisc_1(D_802, B_803))) | ~v1_funct_2(F_804, D_802, B_803) | ~v1_funct_1(F_804) | ~m1_subset_1(E_806, k1_zfmisc_1(k2_zfmisc_1(C_805, B_803))) | ~v1_funct_2(E_806, C_805, B_803) | ~v1_funct_1(E_806) | ~m1_subset_1(D_802, k1_zfmisc_1(A_801)) | v1_xboole_0(D_802) | ~m1_subset_1(C_805, k1_zfmisc_1(A_801)) | v1_xboole_0(C_805) | v1_xboole_0(B_803) | v1_xboole_0(A_801))), inference(cnfTransformation, [status(thm)], [f_126])).
% 8.06/2.85  tff(c_3858, plain, (![E_920, B_921, A_922, D_923, C_918, F_919]: (k2_partfun1(k4_subset_1(A_922, C_918, D_923), B_921, k1_tmap_1(A_922, B_921, C_918, D_923, E_920, F_919), C_918)=E_920 | ~v1_funct_2(k1_tmap_1(A_922, B_921, C_918, D_923, E_920, F_919), k4_subset_1(A_922, C_918, D_923), B_921) | ~v1_funct_1(k1_tmap_1(A_922, B_921, C_918, D_923, E_920, F_919)) | k2_partfun1(D_923, B_921, F_919, k9_subset_1(A_922, C_918, D_923))!=k2_partfun1(C_918, B_921, E_920, k9_subset_1(A_922, C_918, D_923)) | ~m1_subset_1(F_919, k1_zfmisc_1(k2_zfmisc_1(D_923, B_921))) | ~v1_funct_2(F_919, D_923, B_921) | ~v1_funct_1(F_919) | ~m1_subset_1(E_920, k1_zfmisc_1(k2_zfmisc_1(C_918, B_921))) | ~v1_funct_2(E_920, C_918, B_921) | ~v1_funct_1(E_920) | ~m1_subset_1(D_923, k1_zfmisc_1(A_922)) | v1_xboole_0(D_923) | ~m1_subset_1(C_918, k1_zfmisc_1(A_922)) | v1_xboole_0(C_918) | v1_xboole_0(B_921) | v1_xboole_0(A_922))), inference(resolution, [status(thm)], [c_34, c_3384])).
% 8.06/2.85  tff(c_4365, plain, (![C_992, A_996, D_997, B_995, F_993, E_994]: (k2_partfun1(k4_subset_1(A_996, C_992, D_997), B_995, k1_tmap_1(A_996, B_995, C_992, D_997, E_994, F_993), C_992)=E_994 | ~v1_funct_1(k1_tmap_1(A_996, B_995, C_992, D_997, E_994, F_993)) | k2_partfun1(D_997, B_995, F_993, k9_subset_1(A_996, C_992, D_997))!=k2_partfun1(C_992, B_995, E_994, k9_subset_1(A_996, C_992, D_997)) | ~m1_subset_1(F_993, k1_zfmisc_1(k2_zfmisc_1(D_997, B_995))) | ~v1_funct_2(F_993, D_997, B_995) | ~v1_funct_1(F_993) | ~m1_subset_1(E_994, k1_zfmisc_1(k2_zfmisc_1(C_992, B_995))) | ~v1_funct_2(E_994, C_992, B_995) | ~v1_funct_1(E_994) | ~m1_subset_1(D_997, k1_zfmisc_1(A_996)) | v1_xboole_0(D_997) | ~m1_subset_1(C_992, k1_zfmisc_1(A_996)) | v1_xboole_0(C_992) | v1_xboole_0(B_995) | v1_xboole_0(A_996))), inference(resolution, [status(thm)], [c_36, c_3858])).
% 8.06/2.85  tff(c_4371, plain, (![A_996, C_992, E_994]: (k2_partfun1(k4_subset_1(A_996, C_992, '#skF_4'), '#skF_2', k1_tmap_1(A_996, '#skF_2', C_992, '#skF_4', E_994, '#skF_6'), C_992)=E_994 | ~v1_funct_1(k1_tmap_1(A_996, '#skF_2', C_992, '#skF_4', E_994, '#skF_6')) | k2_partfun1(C_992, '#skF_2', E_994, k9_subset_1(A_996, C_992, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_996, C_992, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_994, k1_zfmisc_1(k2_zfmisc_1(C_992, '#skF_2'))) | ~v1_funct_2(E_994, C_992, '#skF_2') | ~v1_funct_1(E_994) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_996)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_992, k1_zfmisc_1(A_996)) | v1_xboole_0(C_992) | v1_xboole_0('#skF_2') | v1_xboole_0(A_996))), inference(resolution, [status(thm)], [c_42, c_4365])).
% 8.06/2.85  tff(c_4379, plain, (![A_996, C_992, E_994]: (k2_partfun1(k4_subset_1(A_996, C_992, '#skF_4'), '#skF_2', k1_tmap_1(A_996, '#skF_2', C_992, '#skF_4', E_994, '#skF_6'), C_992)=E_994 | ~v1_funct_1(k1_tmap_1(A_996, '#skF_2', C_992, '#skF_4', E_994, '#skF_6')) | k2_partfun1(C_992, '#skF_2', E_994, k9_subset_1(A_996, C_992, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_996, C_992, '#skF_4')) | ~m1_subset_1(E_994, k1_zfmisc_1(k2_zfmisc_1(C_992, '#skF_2'))) | ~v1_funct_2(E_994, C_992, '#skF_2') | ~v1_funct_1(E_994) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_996)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_992, k1_zfmisc_1(A_996)) | v1_xboole_0(C_992) | v1_xboole_0('#skF_2') | v1_xboole_0(A_996))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_979, c_4371])).
% 8.06/2.85  tff(c_4706, plain, (![A_1063, C_1064, E_1065]: (k2_partfun1(k4_subset_1(A_1063, C_1064, '#skF_4'), '#skF_2', k1_tmap_1(A_1063, '#skF_2', C_1064, '#skF_4', E_1065, '#skF_6'), C_1064)=E_1065 | ~v1_funct_1(k1_tmap_1(A_1063, '#skF_2', C_1064, '#skF_4', E_1065, '#skF_6')) | k2_partfun1(C_1064, '#skF_2', E_1065, k9_subset_1(A_1063, C_1064, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1063, C_1064, '#skF_4')) | ~m1_subset_1(E_1065, k1_zfmisc_1(k2_zfmisc_1(C_1064, '#skF_2'))) | ~v1_funct_2(E_1065, C_1064, '#skF_2') | ~v1_funct_1(E_1065) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1063)) | ~m1_subset_1(C_1064, k1_zfmisc_1(A_1063)) | v1_xboole_0(C_1064) | v1_xboole_0(A_1063))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_4379])).
% 8.06/2.85  tff(c_4711, plain, (![A_1063]: (k2_partfun1(k4_subset_1(A_1063, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1063, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1063, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_1063, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1063, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1063)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1063)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1063))), inference(resolution, [status(thm)], [c_48, c_4706])).
% 8.06/2.85  tff(c_4719, plain, (![A_1063]: (k2_partfun1(k4_subset_1(A_1063, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1063, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1063, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1063, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1063, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1063)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1063)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1063))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_976, c_4711])).
% 8.06/2.85  tff(c_4725, plain, (![A_1066]: (k2_partfun1(k4_subset_1(A_1066, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1066, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1066, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1066, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1066, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1066)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1066)) | v1_xboole_0(A_1066))), inference(negUnitSimplification, [status(thm)], [c_62, c_4719])).
% 8.06/2.85  tff(c_1086, plain, (![A_339, B_340]: (k3_xboole_0(A_339, B_340)=k1_xboole_0 | ~r1_subset_1(A_339, B_340) | v1_xboole_0(B_340) | v1_xboole_0(A_339))), inference(resolution, [status(thm)], [c_708, c_2])).
% 8.06/2.85  tff(c_1092, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_54, c_1086])).
% 8.06/2.85  tff(c_1096, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_62, c_58, c_1092])).
% 8.06/2.85  tff(c_1177, plain, (![A_361, C_357, F_358, D_362, B_360, E_359]: (v1_funct_1(k1_tmap_1(A_361, B_360, C_357, D_362, E_359, F_358)) | ~m1_subset_1(F_358, k1_zfmisc_1(k2_zfmisc_1(D_362, B_360))) | ~v1_funct_2(F_358, D_362, B_360) | ~v1_funct_1(F_358) | ~m1_subset_1(E_359, k1_zfmisc_1(k2_zfmisc_1(C_357, B_360))) | ~v1_funct_2(E_359, C_357, B_360) | ~v1_funct_1(E_359) | ~m1_subset_1(D_362, k1_zfmisc_1(A_361)) | v1_xboole_0(D_362) | ~m1_subset_1(C_357, k1_zfmisc_1(A_361)) | v1_xboole_0(C_357) | v1_xboole_0(B_360) | v1_xboole_0(A_361))), inference(cnfTransformation, [status(thm)], [f_160])).
% 8.06/2.85  tff(c_1181, plain, (![A_361, C_357, E_359]: (v1_funct_1(k1_tmap_1(A_361, '#skF_2', C_357, '#skF_4', E_359, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_359, k1_zfmisc_1(k2_zfmisc_1(C_357, '#skF_2'))) | ~v1_funct_2(E_359, C_357, '#skF_2') | ~v1_funct_1(E_359) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_361)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_357, k1_zfmisc_1(A_361)) | v1_xboole_0(C_357) | v1_xboole_0('#skF_2') | v1_xboole_0(A_361))), inference(resolution, [status(thm)], [c_42, c_1177])).
% 8.06/2.85  tff(c_1188, plain, (![A_361, C_357, E_359]: (v1_funct_1(k1_tmap_1(A_361, '#skF_2', C_357, '#skF_4', E_359, '#skF_6')) | ~m1_subset_1(E_359, k1_zfmisc_1(k2_zfmisc_1(C_357, '#skF_2'))) | ~v1_funct_2(E_359, C_357, '#skF_2') | ~v1_funct_1(E_359) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_361)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_357, k1_zfmisc_1(A_361)) | v1_xboole_0(C_357) | v1_xboole_0('#skF_2') | v1_xboole_0(A_361))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_1181])).
% 8.06/2.85  tff(c_1433, plain, (![A_404, C_405, E_406]: (v1_funct_1(k1_tmap_1(A_404, '#skF_2', C_405, '#skF_4', E_406, '#skF_6')) | ~m1_subset_1(E_406, k1_zfmisc_1(k2_zfmisc_1(C_405, '#skF_2'))) | ~v1_funct_2(E_406, C_405, '#skF_2') | ~v1_funct_1(E_406) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_404)) | ~m1_subset_1(C_405, k1_zfmisc_1(A_404)) | v1_xboole_0(C_405) | v1_xboole_0(A_404))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_1188])).
% 8.06/2.85  tff(c_1438, plain, (![A_404]: (v1_funct_1(k1_tmap_1(A_404, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_404)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_404)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_404))), inference(resolution, [status(thm)], [c_48, c_1433])).
% 8.06/2.85  tff(c_1446, plain, (![A_404]: (v1_funct_1(k1_tmap_1(A_404, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_404)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_404)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_404))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1438])).
% 8.06/2.85  tff(c_1459, plain, (![A_408]: (v1_funct_1(k1_tmap_1(A_408, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_408)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_408)) | v1_xboole_0(A_408))), inference(negUnitSimplification, [status(thm)], [c_62, c_1446])).
% 8.06/2.85  tff(c_1462, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_1459])).
% 8.06/2.85  tff(c_1465, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1462])).
% 8.06/2.85  tff(c_1466, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_66, c_1465])).
% 8.06/2.85  tff(c_1509, plain, (![C_423, E_424, D_420, B_421, A_419, F_422]: (k2_partfun1(k4_subset_1(A_419, C_423, D_420), B_421, k1_tmap_1(A_419, B_421, C_423, D_420, E_424, F_422), D_420)=F_422 | ~m1_subset_1(k1_tmap_1(A_419, B_421, C_423, D_420, E_424, F_422), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_419, C_423, D_420), B_421))) | ~v1_funct_2(k1_tmap_1(A_419, B_421, C_423, D_420, E_424, F_422), k4_subset_1(A_419, C_423, D_420), B_421) | ~v1_funct_1(k1_tmap_1(A_419, B_421, C_423, D_420, E_424, F_422)) | k2_partfun1(D_420, B_421, F_422, k9_subset_1(A_419, C_423, D_420))!=k2_partfun1(C_423, B_421, E_424, k9_subset_1(A_419, C_423, D_420)) | ~m1_subset_1(F_422, k1_zfmisc_1(k2_zfmisc_1(D_420, B_421))) | ~v1_funct_2(F_422, D_420, B_421) | ~v1_funct_1(F_422) | ~m1_subset_1(E_424, k1_zfmisc_1(k2_zfmisc_1(C_423, B_421))) | ~v1_funct_2(E_424, C_423, B_421) | ~v1_funct_1(E_424) | ~m1_subset_1(D_420, k1_zfmisc_1(A_419)) | v1_xboole_0(D_420) | ~m1_subset_1(C_423, k1_zfmisc_1(A_419)) | v1_xboole_0(C_423) | v1_xboole_0(B_421) | v1_xboole_0(A_419))), inference(cnfTransformation, [status(thm)], [f_126])).
% 8.06/2.85  tff(c_2027, plain, (![D_533, A_532, E_530, F_529, B_531, C_528]: (k2_partfun1(k4_subset_1(A_532, C_528, D_533), B_531, k1_tmap_1(A_532, B_531, C_528, D_533, E_530, F_529), D_533)=F_529 | ~v1_funct_2(k1_tmap_1(A_532, B_531, C_528, D_533, E_530, F_529), k4_subset_1(A_532, C_528, D_533), B_531) | ~v1_funct_1(k1_tmap_1(A_532, B_531, C_528, D_533, E_530, F_529)) | k2_partfun1(D_533, B_531, F_529, k9_subset_1(A_532, C_528, D_533))!=k2_partfun1(C_528, B_531, E_530, k9_subset_1(A_532, C_528, D_533)) | ~m1_subset_1(F_529, k1_zfmisc_1(k2_zfmisc_1(D_533, B_531))) | ~v1_funct_2(F_529, D_533, B_531) | ~v1_funct_1(F_529) | ~m1_subset_1(E_530, k1_zfmisc_1(k2_zfmisc_1(C_528, B_531))) | ~v1_funct_2(E_530, C_528, B_531) | ~v1_funct_1(E_530) | ~m1_subset_1(D_533, k1_zfmisc_1(A_532)) | v1_xboole_0(D_533) | ~m1_subset_1(C_528, k1_zfmisc_1(A_532)) | v1_xboole_0(C_528) | v1_xboole_0(B_531) | v1_xboole_0(A_532))), inference(resolution, [status(thm)], [c_34, c_1509])).
% 8.06/2.85  tff(c_2350, plain, (![E_587, D_590, F_586, A_589, B_588, C_585]: (k2_partfun1(k4_subset_1(A_589, C_585, D_590), B_588, k1_tmap_1(A_589, B_588, C_585, D_590, E_587, F_586), D_590)=F_586 | ~v1_funct_1(k1_tmap_1(A_589, B_588, C_585, D_590, E_587, F_586)) | k2_partfun1(D_590, B_588, F_586, k9_subset_1(A_589, C_585, D_590))!=k2_partfun1(C_585, B_588, E_587, k9_subset_1(A_589, C_585, D_590)) | ~m1_subset_1(F_586, k1_zfmisc_1(k2_zfmisc_1(D_590, B_588))) | ~v1_funct_2(F_586, D_590, B_588) | ~v1_funct_1(F_586) | ~m1_subset_1(E_587, k1_zfmisc_1(k2_zfmisc_1(C_585, B_588))) | ~v1_funct_2(E_587, C_585, B_588) | ~v1_funct_1(E_587) | ~m1_subset_1(D_590, k1_zfmisc_1(A_589)) | v1_xboole_0(D_590) | ~m1_subset_1(C_585, k1_zfmisc_1(A_589)) | v1_xboole_0(C_585) | v1_xboole_0(B_588) | v1_xboole_0(A_589))), inference(resolution, [status(thm)], [c_36, c_2027])).
% 8.06/2.85  tff(c_2356, plain, (![A_589, C_585, E_587]: (k2_partfun1(k4_subset_1(A_589, C_585, '#skF_4'), '#skF_2', k1_tmap_1(A_589, '#skF_2', C_585, '#skF_4', E_587, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_589, '#skF_2', C_585, '#skF_4', E_587, '#skF_6')) | k2_partfun1(C_585, '#skF_2', E_587, k9_subset_1(A_589, C_585, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_589, C_585, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_587, k1_zfmisc_1(k2_zfmisc_1(C_585, '#skF_2'))) | ~v1_funct_2(E_587, C_585, '#skF_2') | ~v1_funct_1(E_587) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_589)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_585, k1_zfmisc_1(A_589)) | v1_xboole_0(C_585) | v1_xboole_0('#skF_2') | v1_xboole_0(A_589))), inference(resolution, [status(thm)], [c_42, c_2350])).
% 8.06/2.85  tff(c_2364, plain, (![A_589, C_585, E_587]: (k2_partfun1(k4_subset_1(A_589, C_585, '#skF_4'), '#skF_2', k1_tmap_1(A_589, '#skF_2', C_585, '#skF_4', E_587, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_589, '#skF_2', C_585, '#skF_4', E_587, '#skF_6')) | k2_partfun1(C_585, '#skF_2', E_587, k9_subset_1(A_589, C_585, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_589, C_585, '#skF_4')) | ~m1_subset_1(E_587, k1_zfmisc_1(k2_zfmisc_1(C_585, '#skF_2'))) | ~v1_funct_2(E_587, C_585, '#skF_2') | ~v1_funct_1(E_587) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_589)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_585, k1_zfmisc_1(A_589)) | v1_xboole_0(C_585) | v1_xboole_0('#skF_2') | v1_xboole_0(A_589))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_979, c_2356])).
% 8.06/2.85  tff(c_2915, plain, (![A_724, C_725, E_726]: (k2_partfun1(k4_subset_1(A_724, C_725, '#skF_4'), '#skF_2', k1_tmap_1(A_724, '#skF_2', C_725, '#skF_4', E_726, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_724, '#skF_2', C_725, '#skF_4', E_726, '#skF_6')) | k2_partfun1(C_725, '#skF_2', E_726, k9_subset_1(A_724, C_725, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_724, C_725, '#skF_4')) | ~m1_subset_1(E_726, k1_zfmisc_1(k2_zfmisc_1(C_725, '#skF_2'))) | ~v1_funct_2(E_726, C_725, '#skF_2') | ~v1_funct_1(E_726) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_724)) | ~m1_subset_1(C_725, k1_zfmisc_1(A_724)) | v1_xboole_0(C_725) | v1_xboole_0(A_724))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_2364])).
% 8.06/2.85  tff(c_2920, plain, (![A_724]: (k2_partfun1(k4_subset_1(A_724, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_724, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_724, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_724, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_724, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_724)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_724)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_724))), inference(resolution, [status(thm)], [c_48, c_2915])).
% 8.06/2.85  tff(c_2928, plain, (![A_724]: (k2_partfun1(k4_subset_1(A_724, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_724, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_724, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_724, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_724, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_724)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_724)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_724))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_976, c_2920])).
% 8.06/2.85  tff(c_2943, plain, (![A_730]: (k2_partfun1(k4_subset_1(A_730, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_730, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_730, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_730, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_730, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_730)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_730)) | v1_xboole_0(A_730))), inference(negUnitSimplification, [status(thm)], [c_62, c_2928])).
% 8.06/2.85  tff(c_119, plain, (![C_231, A_232, B_233]: (v4_relat_1(C_231, A_232) | ~m1_subset_1(C_231, k1_zfmisc_1(k2_zfmisc_1(A_232, B_233))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.06/2.85  tff(c_127, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_119])).
% 8.06/2.85  tff(c_136, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_127, c_16])).
% 8.06/2.85  tff(c_139, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_136])).
% 8.06/2.85  tff(c_217, plain, (![C_245, A_246, B_247]: (k7_relat_1(k7_relat_1(C_245, A_246), B_247)=k1_xboole_0 | ~r1_xboole_0(A_246, B_247) | ~v1_relat_1(C_245))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.06/2.85  tff(c_232, plain, (![B_247]: (k7_relat_1('#skF_6', B_247)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_247) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_139, c_217])).
% 8.06/2.85  tff(c_253, plain, (![B_252]: (k7_relat_1('#skF_6', B_252)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_252))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_232])).
% 8.06/2.85  tff(c_270, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_253])).
% 8.06/2.85  tff(c_148, plain, (![A_234, B_235]: (r1_xboole_0(A_234, B_235) | ~r1_subset_1(A_234, B_235) | v1_xboole_0(B_235) | v1_xboole_0(A_234))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.06/2.85  tff(c_549, plain, (![A_279, B_280]: (k3_xboole_0(A_279, B_280)=k1_xboole_0 | ~r1_subset_1(A_279, B_280) | v1_xboole_0(B_280) | v1_xboole_0(A_279))), inference(resolution, [status(thm)], [c_148, c_2])).
% 8.06/2.85  tff(c_555, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_54, c_549])).
% 8.06/2.85  tff(c_559, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_62, c_58, c_555])).
% 8.06/2.85  tff(c_126, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_119])).
% 8.06/2.85  tff(c_130, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_126, c_16])).
% 8.06/2.85  tff(c_133, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_101, c_130])).
% 8.06/2.85  tff(c_235, plain, (![B_247]: (k7_relat_1('#skF_5', B_247)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_247) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_133, c_217])).
% 8.06/2.85  tff(c_280, plain, (![B_253]: (k7_relat_1('#skF_5', B_253)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_253))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_235])).
% 8.06/2.85  tff(c_297, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_280])).
% 8.06/2.85  tff(c_242, plain, (![A_248, B_249, C_250, D_251]: (k2_partfun1(A_248, B_249, C_250, D_251)=k7_relat_1(C_250, D_251) | ~m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(A_248, B_249))) | ~v1_funct_1(C_250))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.06/2.85  tff(c_246, plain, (![D_251]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_251)=k7_relat_1('#skF_6', D_251) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_42, c_242])).
% 8.06/2.85  tff(c_252, plain, (![D_251]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_251)=k7_relat_1('#skF_6', D_251))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_246])).
% 8.06/2.85  tff(c_244, plain, (![D_251]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_251)=k7_relat_1('#skF_5', D_251) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_48, c_242])).
% 8.06/2.85  tff(c_249, plain, (![D_251]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_251)=k7_relat_1('#skF_5', D_251))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_244])).
% 8.06/2.85  tff(c_167, plain, (![A_238, B_239, C_240]: (k9_subset_1(A_238, B_239, C_240)=k3_xboole_0(B_239, C_240) | ~m1_subset_1(C_240, k1_zfmisc_1(A_238)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.06/2.85  tff(c_179, plain, (![B_239]: (k9_subset_1('#skF_1', B_239, '#skF_4')=k3_xboole_0(B_239, '#skF_4'))), inference(resolution, [status(thm)], [c_56, c_167])).
% 8.06/2.85  tff(c_40, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_202])).
% 8.06/2.85  tff(c_107, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_40])).
% 8.06/2.85  tff(c_189, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_179, c_107])).
% 8.06/2.85  tff(c_650, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_270, c_559, c_297, c_559, c_252, c_249, c_189])).
% 8.06/2.85  tff(c_651, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_40])).
% 8.06/2.85  tff(c_1065, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_651])).
% 8.06/2.85  tff(c_2954, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2943, c_1065])).
% 8.06/2.85  tff(c_2968, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_759, c_1096, c_786, c_1096, c_848, c_848, c_1466, c_2954])).
% 8.06/2.85  tff(c_2970, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_2968])).
% 8.06/2.85  tff(c_2971, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_651])).
% 8.06/2.85  tff(c_4734, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4725, c_2971])).
% 8.06/2.85  tff(c_4745, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_759, c_3019, c_786, c_3019, c_848, c_848, c_3280, c_4734])).
% 8.06/2.85  tff(c_4747, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_4745])).
% 8.06/2.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.06/2.85  
% 8.06/2.85  Inference rules
% 8.06/2.85  ----------------------
% 8.06/2.85  #Ref     : 0
% 8.06/2.85  #Sup     : 986
% 8.06/2.85  #Fact    : 0
% 8.06/2.85  #Define  : 0
% 8.06/2.85  #Split   : 37
% 8.06/2.85  #Chain   : 0
% 8.06/2.85  #Close   : 0
% 8.06/2.85  
% 8.06/2.85  Ordering : KBO
% 8.06/2.85  
% 8.06/2.85  Simplification rules
% 8.06/2.85  ----------------------
% 8.06/2.85  #Subsume      : 225
% 8.06/2.85  #Demod        : 621
% 8.06/2.85  #Tautology    : 316
% 8.06/2.85  #SimpNegUnit  : 250
% 8.06/2.85  #BackRed      : 3
% 8.06/2.85  
% 8.06/2.85  #Partial instantiations: 0
% 8.06/2.85  #Strategies tried      : 1
% 8.06/2.85  
% 8.06/2.85  Timing (in seconds)
% 8.06/2.85  ----------------------
% 8.06/2.85  Preprocessing        : 0.43
% 8.06/2.85  Parsing              : 0.21
% 8.06/2.85  CNF conversion       : 0.06
% 8.06/2.85  Main loop            : 1.57
% 8.06/2.85  Inferencing          : 0.56
% 8.06/2.85  Reduction            : 0.50
% 8.06/2.85  Demodulation         : 0.35
% 8.06/2.85  BG Simplification    : 0.06
% 8.06/2.85  Subsumption          : 0.36
% 8.06/2.85  Abstraction          : 0.07
% 8.06/2.85  MUC search           : 0.00
% 8.06/2.85  Cooper               : 0.00
% 8.06/2.85  Total                : 2.06
% 8.06/2.85  Index Insertion      : 0.00
% 8.06/2.85  Index Deletion       : 0.00
% 8.06/2.85  Index Matching       : 0.00
% 8.06/2.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
