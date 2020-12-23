%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:18 EST 2020

% Result     : Theorem 21.65s
% Output     : CNFRefutation 22.00s
% Verified   : 
% Statistics : Number of formulae       :  215 ( 700 expanded)
%              Number of leaves         :   46 ( 267 expanded)
%              Depth                    :   15
%              Number of atoms          :  716 (3693 expanded)
%              Number of equality atoms :  127 ( 661 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_230,negated_conjecture,(
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

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
       => r1_subset_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_subset_1)).

tff(f_188,axiom,(
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

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_154,axiom,(
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

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_103,plain,(
    ! [C_229,A_230,B_231] :
      ( v1_relat_1(C_229)
      | ~ m1_subset_1(C_229,k1_zfmisc_1(k2_zfmisc_1(A_230,B_231))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_110,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_103])).

tff(c_6,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_83,plain,(
    ! [A_226,B_227] :
      ( k3_xboole_0(A_226,B_227) = A_226
      | ~ r1_tarski(A_226,B_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_87,plain,(
    ! [A_4] : k3_xboole_0(k1_xboole_0,A_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_83])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_62,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( r1_xboole_0(A_14,B_15)
      | ~ r1_subset_1(A_14,B_15)
      | v1_xboole_0(B_15)
      | v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_72,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_2124,plain,(
    ! [C_390,A_391,B_392] :
      ( v4_relat_1(C_390,A_391)
      | ~ m1_subset_1(C_390,k1_zfmisc_1(k2_zfmisc_1(A_391,B_392))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2131,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_2124])).

tff(c_2170,plain,(
    ! [B_405,A_406] :
      ( k1_relat_1(B_405) = A_406
      | ~ v1_partfun1(B_405,A_406)
      | ~ v4_relat_1(B_405,A_406)
      | ~ v1_relat_1(B_405) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2176,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2131,c_2170])).

tff(c_2182,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_2176])).

tff(c_2974,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2182])).

tff(c_54,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_52,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_3988,plain,(
    ! [C_515,A_516,B_517] :
      ( v1_partfun1(C_515,A_516)
      | ~ v1_funct_2(C_515,A_516,B_517)
      | ~ v1_funct_1(C_515)
      | ~ m1_subset_1(C_515,k1_zfmisc_1(k2_zfmisc_1(A_516,B_517)))
      | v1_xboole_0(B_517) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_3991,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_3988])).

tff(c_3997,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_3991])).

tff(c_3999,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2974,c_3997])).

tff(c_4000,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2182])).

tff(c_12,plain,(
    ! [A_11,B_13] :
      ( k7_relat_1(A_11,B_13) = k1_xboole_0
      | ~ r1_xboole_0(B_13,k1_relat_1(A_11))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4005,plain,(
    ! [B_13] :
      ( k7_relat_1('#skF_6',B_13) = k1_xboole_0
      | ~ r1_xboole_0(B_13,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4000,c_12])).

tff(c_4035,plain,(
    ! [B_520] :
      ( k7_relat_1('#skF_6',B_520) = k1_xboole_0
      | ~ r1_xboole_0(B_520,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_4005])).

tff(c_4039,plain,(
    ! [A_14] :
      ( k7_relat_1('#skF_6',A_14) = k1_xboole_0
      | ~ r1_subset_1(A_14,'#skF_4')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_14) ) ),
    inference(resolution,[status(thm)],[c_16,c_4035])).

tff(c_4125,plain,(
    ! [A_528] :
      ( k7_relat_1('#skF_6',A_528) = k1_xboole_0
      | ~ r1_subset_1(A_528,'#skF_4')
      | v1_xboole_0(A_528) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_4039])).

tff(c_4128,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_4125])).

tff(c_4131,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_4128])).

tff(c_10,plain,(
    ! [C_10,A_8,B_9] :
      ( k3_xboole_0(k7_relat_1(C_10,A_8),k7_relat_1(C_10,B_9)) = k7_relat_1(C_10,k3_xboole_0(A_8,B_9))
      | ~ v1_relat_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4135,plain,(
    ! [B_9] :
      ( k7_relat_1('#skF_6',k3_xboole_0('#skF_3',B_9)) = k3_xboole_0(k1_xboole_0,k7_relat_1('#skF_6',B_9))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4131,c_10])).

tff(c_4142,plain,(
    ! [B_9] : k7_relat_1('#skF_6',k3_xboole_0('#skF_3',B_9)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_87,c_4135])).

tff(c_2183,plain,(
    ! [A_407,B_408,C_409] :
      ( k9_subset_1(A_407,B_408,C_409) = k3_xboole_0(B_408,C_409)
      | ~ m1_subset_1(C_409,k1_zfmisc_1(A_407)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2195,plain,(
    ! [B_408] : k9_subset_1('#skF_1',B_408,'#skF_4') = k3_xboole_0(B_408,'#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_2183])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_111,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_103])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2148,plain,(
    ! [B_399,A_400] :
      ( r1_subset_1(B_399,A_400)
      | ~ r1_subset_1(A_400,B_399)
      | v1_xboole_0(B_399)
      | v1_xboole_0(A_400) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2150,plain,
    ( r1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_2148])).

tff(c_2153,plain,(
    r1_subset_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_66,c_2150])).

tff(c_2132,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_2124])).

tff(c_2173,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2132,c_2170])).

tff(c_2179,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_2173])).

tff(c_2196,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2179])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_58,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_2932,plain,(
    ! [C_465,A_466,B_467] :
      ( v1_partfun1(C_465,A_466)
      | ~ v1_funct_2(C_465,A_466,B_467)
      | ~ v1_funct_1(C_465)
      | ~ m1_subset_1(C_465,k1_zfmisc_1(k2_zfmisc_1(A_466,B_467)))
      | v1_xboole_0(B_467) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2938,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_2932])).

tff(c_2945,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_2938])).

tff(c_2947,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2196,c_2945])).

tff(c_2948,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2179])).

tff(c_2953,plain,(
    ! [B_13] :
      ( k7_relat_1('#skF_5',B_13) = k1_xboole_0
      | ~ r1_xboole_0(B_13,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2948,c_12])).

tff(c_4027,plain,(
    ! [B_519] :
      ( k7_relat_1('#skF_5',B_519) = k1_xboole_0
      | ~ r1_xboole_0(B_519,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_2953])).

tff(c_4031,plain,(
    ! [A_14] :
      ( k7_relat_1('#skF_5',A_14) = k1_xboole_0
      | ~ r1_subset_1(A_14,'#skF_3')
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_14) ) ),
    inference(resolution,[status(thm)],[c_16,c_4027])).

tff(c_4061,plain,(
    ! [A_523] :
      ( k7_relat_1('#skF_5',A_523) = k1_xboole_0
      | ~ r1_subset_1(A_523,'#skF_3')
      | v1_xboole_0(A_523) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_4031])).

tff(c_4064,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_2153,c_4061])).

tff(c_4067,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_4064])).

tff(c_4083,plain,(
    ! [A_8] :
      ( k7_relat_1('#skF_5',k3_xboole_0(A_8,'#skF_4')) = k3_xboole_0(k7_relat_1('#skF_5',A_8),k1_xboole_0)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4067,c_10])).

tff(c_4089,plain,(
    ! [A_8] : k7_relat_1('#skF_5',k3_xboole_0(A_8,'#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_4,c_4083])).

tff(c_126133,plain,(
    ! [E_2113,C_2111,D_2110,F_2114,A_2112,B_2109] :
      ( v1_funct_1(k1_tmap_1(A_2112,B_2109,C_2111,D_2110,E_2113,F_2114))
      | ~ m1_subset_1(F_2114,k1_zfmisc_1(k2_zfmisc_1(D_2110,B_2109)))
      | ~ v1_funct_2(F_2114,D_2110,B_2109)
      | ~ v1_funct_1(F_2114)
      | ~ m1_subset_1(E_2113,k1_zfmisc_1(k2_zfmisc_1(C_2111,B_2109)))
      | ~ v1_funct_2(E_2113,C_2111,B_2109)
      | ~ v1_funct_1(E_2113)
      | ~ m1_subset_1(D_2110,k1_zfmisc_1(A_2112))
      | v1_xboole_0(D_2110)
      | ~ m1_subset_1(C_2111,k1_zfmisc_1(A_2112))
      | v1_xboole_0(C_2111)
      | v1_xboole_0(B_2109)
      | v1_xboole_0(A_2112) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_126135,plain,(
    ! [A_2112,C_2111,E_2113] :
      ( v1_funct_1(k1_tmap_1(A_2112,'#skF_2',C_2111,'#skF_4',E_2113,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_2113,k1_zfmisc_1(k2_zfmisc_1(C_2111,'#skF_2')))
      | ~ v1_funct_2(E_2113,C_2111,'#skF_2')
      | ~ v1_funct_1(E_2113)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2112))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_2111,k1_zfmisc_1(A_2112))
      | v1_xboole_0(C_2111)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_2112) ) ),
    inference(resolution,[status(thm)],[c_50,c_126133])).

tff(c_126140,plain,(
    ! [A_2112,C_2111,E_2113] :
      ( v1_funct_1(k1_tmap_1(A_2112,'#skF_2',C_2111,'#skF_4',E_2113,'#skF_6'))
      | ~ m1_subset_1(E_2113,k1_zfmisc_1(k2_zfmisc_1(C_2111,'#skF_2')))
      | ~ v1_funct_2(E_2113,C_2111,'#skF_2')
      | ~ v1_funct_1(E_2113)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2112))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_2111,k1_zfmisc_1(A_2112))
      | v1_xboole_0(C_2111)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_2112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_126135])).

tff(c_126677,plain,(
    ! [A_2127,C_2128,E_2129] :
      ( v1_funct_1(k1_tmap_1(A_2127,'#skF_2',C_2128,'#skF_4',E_2129,'#skF_6'))
      | ~ m1_subset_1(E_2129,k1_zfmisc_1(k2_zfmisc_1(C_2128,'#skF_2')))
      | ~ v1_funct_2(E_2129,C_2128,'#skF_2')
      | ~ v1_funct_1(E_2129)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2127))
      | ~ m1_subset_1(C_2128,k1_zfmisc_1(A_2127))
      | v1_xboole_0(C_2128)
      | v1_xboole_0(A_2127) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_126140])).

tff(c_126681,plain,(
    ! [A_2127] :
      ( v1_funct_1(k1_tmap_1(A_2127,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2127))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_2127))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2127) ) ),
    inference(resolution,[status(thm)],[c_56,c_126677])).

tff(c_126688,plain,(
    ! [A_2127] :
      ( v1_funct_1(k1_tmap_1(A_2127,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2127))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_2127))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_126681])).

tff(c_129505,plain,(
    ! [A_2203] :
      ( v1_funct_1(k1_tmap_1(A_2203,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2203))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_2203))
      | v1_xboole_0(A_2203) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_126688])).

tff(c_129508,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_129505])).

tff(c_129511,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_129508])).

tff(c_129512,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_129511])).

tff(c_4238,plain,(
    ! [A_532,B_533,C_534,D_535] :
      ( k2_partfun1(A_532,B_533,C_534,D_535) = k7_relat_1(C_534,D_535)
      | ~ m1_subset_1(C_534,k1_zfmisc_1(k2_zfmisc_1(A_532,B_533)))
      | ~ v1_funct_1(C_534) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_4242,plain,(
    ! [D_535] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_535) = k7_relat_1('#skF_5',D_535)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_4238])).

tff(c_4248,plain,(
    ! [D_535] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_535) = k7_relat_1('#skF_5',D_535) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_4242])).

tff(c_4240,plain,(
    ! [D_535] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_535) = k7_relat_1('#skF_6',D_535)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_50,c_4238])).

tff(c_4245,plain,(
    ! [D_535] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_535) = k7_relat_1('#skF_6',D_535) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4240])).

tff(c_44,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_42,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_130421,plain,(
    ! [D_2225,A_2220,B_2223,F_2222,E_2224,C_2221] :
      ( k2_partfun1(k4_subset_1(A_2220,C_2221,D_2225),B_2223,k1_tmap_1(A_2220,B_2223,C_2221,D_2225,E_2224,F_2222),C_2221) = E_2224
      | ~ m1_subset_1(k1_tmap_1(A_2220,B_2223,C_2221,D_2225,E_2224,F_2222),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_2220,C_2221,D_2225),B_2223)))
      | ~ v1_funct_2(k1_tmap_1(A_2220,B_2223,C_2221,D_2225,E_2224,F_2222),k4_subset_1(A_2220,C_2221,D_2225),B_2223)
      | ~ v1_funct_1(k1_tmap_1(A_2220,B_2223,C_2221,D_2225,E_2224,F_2222))
      | k2_partfun1(D_2225,B_2223,F_2222,k9_subset_1(A_2220,C_2221,D_2225)) != k2_partfun1(C_2221,B_2223,E_2224,k9_subset_1(A_2220,C_2221,D_2225))
      | ~ m1_subset_1(F_2222,k1_zfmisc_1(k2_zfmisc_1(D_2225,B_2223)))
      | ~ v1_funct_2(F_2222,D_2225,B_2223)
      | ~ v1_funct_1(F_2222)
      | ~ m1_subset_1(E_2224,k1_zfmisc_1(k2_zfmisc_1(C_2221,B_2223)))
      | ~ v1_funct_2(E_2224,C_2221,B_2223)
      | ~ v1_funct_1(E_2224)
      | ~ m1_subset_1(D_2225,k1_zfmisc_1(A_2220))
      | v1_xboole_0(D_2225)
      | ~ m1_subset_1(C_2221,k1_zfmisc_1(A_2220))
      | v1_xboole_0(C_2221)
      | v1_xboole_0(B_2223)
      | v1_xboole_0(A_2220) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_161539,plain,(
    ! [A_2724,E_2725,B_2721,D_2722,F_2726,C_2723] :
      ( k2_partfun1(k4_subset_1(A_2724,C_2723,D_2722),B_2721,k1_tmap_1(A_2724,B_2721,C_2723,D_2722,E_2725,F_2726),C_2723) = E_2725
      | ~ v1_funct_2(k1_tmap_1(A_2724,B_2721,C_2723,D_2722,E_2725,F_2726),k4_subset_1(A_2724,C_2723,D_2722),B_2721)
      | ~ v1_funct_1(k1_tmap_1(A_2724,B_2721,C_2723,D_2722,E_2725,F_2726))
      | k2_partfun1(D_2722,B_2721,F_2726,k9_subset_1(A_2724,C_2723,D_2722)) != k2_partfun1(C_2723,B_2721,E_2725,k9_subset_1(A_2724,C_2723,D_2722))
      | ~ m1_subset_1(F_2726,k1_zfmisc_1(k2_zfmisc_1(D_2722,B_2721)))
      | ~ v1_funct_2(F_2726,D_2722,B_2721)
      | ~ v1_funct_1(F_2726)
      | ~ m1_subset_1(E_2725,k1_zfmisc_1(k2_zfmisc_1(C_2723,B_2721)))
      | ~ v1_funct_2(E_2725,C_2723,B_2721)
      | ~ v1_funct_1(E_2725)
      | ~ m1_subset_1(D_2722,k1_zfmisc_1(A_2724))
      | v1_xboole_0(D_2722)
      | ~ m1_subset_1(C_2723,k1_zfmisc_1(A_2724))
      | v1_xboole_0(C_2723)
      | v1_xboole_0(B_2721)
      | v1_xboole_0(A_2724) ) ),
    inference(resolution,[status(thm)],[c_42,c_130421])).

tff(c_189598,plain,(
    ! [C_3035,B_3033,E_3037,A_3036,F_3038,D_3034] :
      ( k2_partfun1(k4_subset_1(A_3036,C_3035,D_3034),B_3033,k1_tmap_1(A_3036,B_3033,C_3035,D_3034,E_3037,F_3038),C_3035) = E_3037
      | ~ v1_funct_1(k1_tmap_1(A_3036,B_3033,C_3035,D_3034,E_3037,F_3038))
      | k2_partfun1(D_3034,B_3033,F_3038,k9_subset_1(A_3036,C_3035,D_3034)) != k2_partfun1(C_3035,B_3033,E_3037,k9_subset_1(A_3036,C_3035,D_3034))
      | ~ m1_subset_1(F_3038,k1_zfmisc_1(k2_zfmisc_1(D_3034,B_3033)))
      | ~ v1_funct_2(F_3038,D_3034,B_3033)
      | ~ v1_funct_1(F_3038)
      | ~ m1_subset_1(E_3037,k1_zfmisc_1(k2_zfmisc_1(C_3035,B_3033)))
      | ~ v1_funct_2(E_3037,C_3035,B_3033)
      | ~ v1_funct_1(E_3037)
      | ~ m1_subset_1(D_3034,k1_zfmisc_1(A_3036))
      | v1_xboole_0(D_3034)
      | ~ m1_subset_1(C_3035,k1_zfmisc_1(A_3036))
      | v1_xboole_0(C_3035)
      | v1_xboole_0(B_3033)
      | v1_xboole_0(A_3036) ) ),
    inference(resolution,[status(thm)],[c_44,c_161539])).

tff(c_189602,plain,(
    ! [A_3036,C_3035,E_3037] :
      ( k2_partfun1(k4_subset_1(A_3036,C_3035,'#skF_4'),'#skF_2',k1_tmap_1(A_3036,'#skF_2',C_3035,'#skF_4',E_3037,'#skF_6'),C_3035) = E_3037
      | ~ v1_funct_1(k1_tmap_1(A_3036,'#skF_2',C_3035,'#skF_4',E_3037,'#skF_6'))
      | k2_partfun1(C_3035,'#skF_2',E_3037,k9_subset_1(A_3036,C_3035,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_3036,C_3035,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_3037,k1_zfmisc_1(k2_zfmisc_1(C_3035,'#skF_2')))
      | ~ v1_funct_2(E_3037,C_3035,'#skF_2')
      | ~ v1_funct_1(E_3037)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3036))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_3035,k1_zfmisc_1(A_3036))
      | v1_xboole_0(C_3035)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_3036) ) ),
    inference(resolution,[status(thm)],[c_50,c_189598])).

tff(c_189608,plain,(
    ! [A_3036,C_3035,E_3037] :
      ( k2_partfun1(k4_subset_1(A_3036,C_3035,'#skF_4'),'#skF_2',k1_tmap_1(A_3036,'#skF_2',C_3035,'#skF_4',E_3037,'#skF_6'),C_3035) = E_3037
      | ~ v1_funct_1(k1_tmap_1(A_3036,'#skF_2',C_3035,'#skF_4',E_3037,'#skF_6'))
      | k2_partfun1(C_3035,'#skF_2',E_3037,k9_subset_1(A_3036,C_3035,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_3036,C_3035,'#skF_4'))
      | ~ m1_subset_1(E_3037,k1_zfmisc_1(k2_zfmisc_1(C_3035,'#skF_2')))
      | ~ v1_funct_2(E_3037,C_3035,'#skF_2')
      | ~ v1_funct_1(E_3037)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3036))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_3035,k1_zfmisc_1(A_3036))
      | v1_xboole_0(C_3035)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_3036) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_4245,c_189602])).

tff(c_191825,plain,(
    ! [A_3057,C_3058,E_3059] :
      ( k2_partfun1(k4_subset_1(A_3057,C_3058,'#skF_4'),'#skF_2',k1_tmap_1(A_3057,'#skF_2',C_3058,'#skF_4',E_3059,'#skF_6'),C_3058) = E_3059
      | ~ v1_funct_1(k1_tmap_1(A_3057,'#skF_2',C_3058,'#skF_4',E_3059,'#skF_6'))
      | k2_partfun1(C_3058,'#skF_2',E_3059,k9_subset_1(A_3057,C_3058,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_3057,C_3058,'#skF_4'))
      | ~ m1_subset_1(E_3059,k1_zfmisc_1(k2_zfmisc_1(C_3058,'#skF_2')))
      | ~ v1_funct_2(E_3059,C_3058,'#skF_2')
      | ~ v1_funct_1(E_3059)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3057))
      | ~ m1_subset_1(C_3058,k1_zfmisc_1(A_3057))
      | v1_xboole_0(C_3058)
      | v1_xboole_0(A_3057) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_189608])).

tff(c_191832,plain,(
    ! [A_3057] :
      ( k2_partfun1(k4_subset_1(A_3057,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_3057,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_3057,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_3057,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_3057,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3057))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_3057))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_3057) ) ),
    inference(resolution,[status(thm)],[c_56,c_191825])).

tff(c_191842,plain,(
    ! [A_3057] :
      ( k2_partfun1(k4_subset_1(A_3057,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_3057,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_3057,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_3057,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_3057,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3057))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_3057))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_3057) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_4248,c_191832])).

tff(c_204027,plain,(
    ! [A_3172] :
      ( k2_partfun1(k4_subset_1(A_3172,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_3172,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_3172,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_3172,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_3172,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3172))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_3172))
      | v1_xboole_0(A_3172) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_191842])).

tff(c_5951,plain,(
    ! [C_604,A_605,E_606,D_603,F_607,B_602] :
      ( v1_funct_1(k1_tmap_1(A_605,B_602,C_604,D_603,E_606,F_607))
      | ~ m1_subset_1(F_607,k1_zfmisc_1(k2_zfmisc_1(D_603,B_602)))
      | ~ v1_funct_2(F_607,D_603,B_602)
      | ~ v1_funct_1(F_607)
      | ~ m1_subset_1(E_606,k1_zfmisc_1(k2_zfmisc_1(C_604,B_602)))
      | ~ v1_funct_2(E_606,C_604,B_602)
      | ~ v1_funct_1(E_606)
      | ~ m1_subset_1(D_603,k1_zfmisc_1(A_605))
      | v1_xboole_0(D_603)
      | ~ m1_subset_1(C_604,k1_zfmisc_1(A_605))
      | v1_xboole_0(C_604)
      | v1_xboole_0(B_602)
      | v1_xboole_0(A_605) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_5953,plain,(
    ! [A_605,C_604,E_606] :
      ( v1_funct_1(k1_tmap_1(A_605,'#skF_2',C_604,'#skF_4',E_606,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_606,k1_zfmisc_1(k2_zfmisc_1(C_604,'#skF_2')))
      | ~ v1_funct_2(E_606,C_604,'#skF_2')
      | ~ v1_funct_1(E_606)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_605))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_604,k1_zfmisc_1(A_605))
      | v1_xboole_0(C_604)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_605) ) ),
    inference(resolution,[status(thm)],[c_50,c_5951])).

tff(c_5958,plain,(
    ! [A_605,C_604,E_606] :
      ( v1_funct_1(k1_tmap_1(A_605,'#skF_2',C_604,'#skF_4',E_606,'#skF_6'))
      | ~ m1_subset_1(E_606,k1_zfmisc_1(k2_zfmisc_1(C_604,'#skF_2')))
      | ~ v1_funct_2(E_606,C_604,'#skF_2')
      | ~ v1_funct_1(E_606)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_605))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_604,k1_zfmisc_1(A_605))
      | v1_xboole_0(C_604)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_605) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_5953])).

tff(c_6331,plain,(
    ! [A_619,C_620,E_621] :
      ( v1_funct_1(k1_tmap_1(A_619,'#skF_2',C_620,'#skF_4',E_621,'#skF_6'))
      | ~ m1_subset_1(E_621,k1_zfmisc_1(k2_zfmisc_1(C_620,'#skF_2')))
      | ~ v1_funct_2(E_621,C_620,'#skF_2')
      | ~ v1_funct_1(E_621)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_619))
      | ~ m1_subset_1(C_620,k1_zfmisc_1(A_619))
      | v1_xboole_0(C_620)
      | v1_xboole_0(A_619) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_5958])).

tff(c_6335,plain,(
    ! [A_619] :
      ( v1_funct_1(k1_tmap_1(A_619,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_619))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_619))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_619) ) ),
    inference(resolution,[status(thm)],[c_56,c_6331])).

tff(c_6342,plain,(
    ! [A_619] :
      ( v1_funct_1(k1_tmap_1(A_619,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_619))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_619))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_619) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_6335])).

tff(c_8703,plain,(
    ! [A_695] :
      ( v1_funct_1(k1_tmap_1(A_695,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_695))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_695))
      | v1_xboole_0(A_695) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_6342])).

tff(c_8706,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_8703])).

tff(c_8709,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_8706])).

tff(c_8710,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_8709])).

tff(c_11258,plain,(
    ! [B_756,A_753,C_754,E_757,D_758,F_755] :
      ( k2_partfun1(k4_subset_1(A_753,C_754,D_758),B_756,k1_tmap_1(A_753,B_756,C_754,D_758,E_757,F_755),D_758) = F_755
      | ~ m1_subset_1(k1_tmap_1(A_753,B_756,C_754,D_758,E_757,F_755),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_753,C_754,D_758),B_756)))
      | ~ v1_funct_2(k1_tmap_1(A_753,B_756,C_754,D_758,E_757,F_755),k4_subset_1(A_753,C_754,D_758),B_756)
      | ~ v1_funct_1(k1_tmap_1(A_753,B_756,C_754,D_758,E_757,F_755))
      | k2_partfun1(D_758,B_756,F_755,k9_subset_1(A_753,C_754,D_758)) != k2_partfun1(C_754,B_756,E_757,k9_subset_1(A_753,C_754,D_758))
      | ~ m1_subset_1(F_755,k1_zfmisc_1(k2_zfmisc_1(D_758,B_756)))
      | ~ v1_funct_2(F_755,D_758,B_756)
      | ~ v1_funct_1(F_755)
      | ~ m1_subset_1(E_757,k1_zfmisc_1(k2_zfmisc_1(C_754,B_756)))
      | ~ v1_funct_2(E_757,C_754,B_756)
      | ~ v1_funct_1(E_757)
      | ~ m1_subset_1(D_758,k1_zfmisc_1(A_753))
      | v1_xboole_0(D_758)
      | ~ m1_subset_1(C_754,k1_zfmisc_1(A_753))
      | v1_xboole_0(C_754)
      | v1_xboole_0(B_756)
      | v1_xboole_0(A_753) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_38284,plain,(
    ! [E_1199,B_1195,F_1200,C_1197,A_1198,D_1196] :
      ( k2_partfun1(k4_subset_1(A_1198,C_1197,D_1196),B_1195,k1_tmap_1(A_1198,B_1195,C_1197,D_1196,E_1199,F_1200),D_1196) = F_1200
      | ~ v1_funct_2(k1_tmap_1(A_1198,B_1195,C_1197,D_1196,E_1199,F_1200),k4_subset_1(A_1198,C_1197,D_1196),B_1195)
      | ~ v1_funct_1(k1_tmap_1(A_1198,B_1195,C_1197,D_1196,E_1199,F_1200))
      | k2_partfun1(D_1196,B_1195,F_1200,k9_subset_1(A_1198,C_1197,D_1196)) != k2_partfun1(C_1197,B_1195,E_1199,k9_subset_1(A_1198,C_1197,D_1196))
      | ~ m1_subset_1(F_1200,k1_zfmisc_1(k2_zfmisc_1(D_1196,B_1195)))
      | ~ v1_funct_2(F_1200,D_1196,B_1195)
      | ~ v1_funct_1(F_1200)
      | ~ m1_subset_1(E_1199,k1_zfmisc_1(k2_zfmisc_1(C_1197,B_1195)))
      | ~ v1_funct_2(E_1199,C_1197,B_1195)
      | ~ v1_funct_1(E_1199)
      | ~ m1_subset_1(D_1196,k1_zfmisc_1(A_1198))
      | v1_xboole_0(D_1196)
      | ~ m1_subset_1(C_1197,k1_zfmisc_1(A_1198))
      | v1_xboole_0(C_1197)
      | v1_xboole_0(B_1195)
      | v1_xboole_0(A_1198) ) ),
    inference(resolution,[status(thm)],[c_42,c_11258])).

tff(c_66406,plain,(
    ! [D_1520,B_1519,C_1521,F_1524,A_1522,E_1523] :
      ( k2_partfun1(k4_subset_1(A_1522,C_1521,D_1520),B_1519,k1_tmap_1(A_1522,B_1519,C_1521,D_1520,E_1523,F_1524),D_1520) = F_1524
      | ~ v1_funct_1(k1_tmap_1(A_1522,B_1519,C_1521,D_1520,E_1523,F_1524))
      | k2_partfun1(D_1520,B_1519,F_1524,k9_subset_1(A_1522,C_1521,D_1520)) != k2_partfun1(C_1521,B_1519,E_1523,k9_subset_1(A_1522,C_1521,D_1520))
      | ~ m1_subset_1(F_1524,k1_zfmisc_1(k2_zfmisc_1(D_1520,B_1519)))
      | ~ v1_funct_2(F_1524,D_1520,B_1519)
      | ~ v1_funct_1(F_1524)
      | ~ m1_subset_1(E_1523,k1_zfmisc_1(k2_zfmisc_1(C_1521,B_1519)))
      | ~ v1_funct_2(E_1523,C_1521,B_1519)
      | ~ v1_funct_1(E_1523)
      | ~ m1_subset_1(D_1520,k1_zfmisc_1(A_1522))
      | v1_xboole_0(D_1520)
      | ~ m1_subset_1(C_1521,k1_zfmisc_1(A_1522))
      | v1_xboole_0(C_1521)
      | v1_xboole_0(B_1519)
      | v1_xboole_0(A_1522) ) ),
    inference(resolution,[status(thm)],[c_44,c_38284])).

tff(c_66410,plain,(
    ! [A_1522,C_1521,E_1523] :
      ( k2_partfun1(k4_subset_1(A_1522,C_1521,'#skF_4'),'#skF_2',k1_tmap_1(A_1522,'#skF_2',C_1521,'#skF_4',E_1523,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1522,'#skF_2',C_1521,'#skF_4',E_1523,'#skF_6'))
      | k2_partfun1(C_1521,'#skF_2',E_1523,k9_subset_1(A_1522,C_1521,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_1522,C_1521,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1523,k1_zfmisc_1(k2_zfmisc_1(C_1521,'#skF_2')))
      | ~ v1_funct_2(E_1523,C_1521,'#skF_2')
      | ~ v1_funct_1(E_1523)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1522))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1521,k1_zfmisc_1(A_1522))
      | v1_xboole_0(C_1521)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1522) ) ),
    inference(resolution,[status(thm)],[c_50,c_66406])).

tff(c_66416,plain,(
    ! [A_1522,C_1521,E_1523] :
      ( k2_partfun1(k4_subset_1(A_1522,C_1521,'#skF_4'),'#skF_2',k1_tmap_1(A_1522,'#skF_2',C_1521,'#skF_4',E_1523,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1522,'#skF_2',C_1521,'#skF_4',E_1523,'#skF_6'))
      | k2_partfun1(C_1521,'#skF_2',E_1523,k9_subset_1(A_1522,C_1521,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1522,C_1521,'#skF_4'))
      | ~ m1_subset_1(E_1523,k1_zfmisc_1(k2_zfmisc_1(C_1521,'#skF_2')))
      | ~ v1_funct_2(E_1523,C_1521,'#skF_2')
      | ~ v1_funct_1(E_1523)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1522))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1521,k1_zfmisc_1(A_1522))
      | v1_xboole_0(C_1521)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1522) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_4245,c_66410])).

tff(c_104489,plain,(
    ! [A_1865,C_1866,E_1867] :
      ( k2_partfun1(k4_subset_1(A_1865,C_1866,'#skF_4'),'#skF_2',k1_tmap_1(A_1865,'#skF_2',C_1866,'#skF_4',E_1867,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1865,'#skF_2',C_1866,'#skF_4',E_1867,'#skF_6'))
      | k2_partfun1(C_1866,'#skF_2',E_1867,k9_subset_1(A_1865,C_1866,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1865,C_1866,'#skF_4'))
      | ~ m1_subset_1(E_1867,k1_zfmisc_1(k2_zfmisc_1(C_1866,'#skF_2')))
      | ~ v1_funct_2(E_1867,C_1866,'#skF_2')
      | ~ v1_funct_1(E_1867)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1865))
      | ~ m1_subset_1(C_1866,k1_zfmisc_1(A_1865))
      | v1_xboole_0(C_1866)
      | v1_xboole_0(A_1865) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_66416])).

tff(c_104496,plain,(
    ! [A_1865] :
      ( k2_partfun1(k4_subset_1(A_1865,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1865,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1865,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1865,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1865,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1865))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1865))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1865) ) ),
    inference(resolution,[status(thm)],[c_56,c_104489])).

tff(c_104506,plain,(
    ! [A_1865] :
      ( k2_partfun1(k4_subset_1(A_1865,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1865,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1865,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1865,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1865,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1865))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1865))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1865) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_4248,c_104496])).

tff(c_123236,plain,(
    ! [A_2011] :
      ( k2_partfun1(k4_subset_1(A_2011,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_2011,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_2011,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_2011,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2011,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2011))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_2011))
      | v1_xboole_0(A_2011) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_104506])).

tff(c_132,plain,(
    ! [B_239,A_240] :
      ( r1_subset_1(B_239,A_240)
      | ~ r1_subset_1(A_240,B_239)
      | v1_xboole_0(B_239)
      | v1_xboole_0(A_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_134,plain,
    ( r1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_132])).

tff(c_137,plain,(
    r1_subset_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_66,c_134])).

tff(c_113,plain,(
    ! [C_232,A_233,B_234] :
      ( v4_relat_1(C_232,A_233)
      | ~ m1_subset_1(C_232,k1_zfmisc_1(k2_zfmisc_1(A_233,B_234))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_121,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_113])).

tff(c_155,plain,(
    ! [B_247,A_248] :
      ( k1_relat_1(B_247) = A_248
      | ~ v1_partfun1(B_247,A_248)
      | ~ v4_relat_1(B_247,A_248)
      | ~ v1_relat_1(B_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_158,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_121,c_155])).

tff(c_164,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_158])).

tff(c_168,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_164])).

tff(c_842,plain,(
    ! [C_304,A_305,B_306] :
      ( v1_partfun1(C_304,A_305)
      | ~ v1_funct_2(C_304,A_305,B_306)
      | ~ v1_funct_1(C_304)
      | ~ m1_subset_1(C_304,k1_zfmisc_1(k2_zfmisc_1(A_305,B_306)))
      | v1_xboole_0(B_306) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_848,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_842])).

tff(c_855,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_848])).

tff(c_857,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_168,c_855])).

tff(c_858,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_863,plain,(
    ! [B_13] :
      ( k7_relat_1('#skF_5',B_13) = k1_xboole_0
      | ~ r1_xboole_0(B_13,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_858,c_12])).

tff(c_1481,plain,(
    ! [B_348] :
      ( k7_relat_1('#skF_5',B_348) = k1_xboole_0
      | ~ r1_xboole_0(B_348,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_863])).

tff(c_1485,plain,(
    ! [A_14] :
      ( k7_relat_1('#skF_5',A_14) = k1_xboole_0
      | ~ r1_subset_1(A_14,'#skF_3')
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_14) ) ),
    inference(resolution,[status(thm)],[c_16,c_1481])).

tff(c_1500,plain,(
    ! [A_350] :
      ( k7_relat_1('#skF_5',A_350) = k1_xboole_0
      | ~ r1_subset_1(A_350,'#skF_3')
      | v1_xboole_0(A_350) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1485])).

tff(c_1503,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_137,c_1500])).

tff(c_1506,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1503])).

tff(c_1561,plain,(
    ! [C_358,A_359,B_360] :
      ( k3_xboole_0(k7_relat_1(C_358,A_359),k7_relat_1(C_358,B_360)) = k7_relat_1(C_358,k3_xboole_0(A_359,B_360))
      | ~ v1_relat_1(C_358) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1573,plain,(
    ! [A_359] :
      ( k7_relat_1('#skF_5',k3_xboole_0(A_359,'#skF_4')) = k3_xboole_0(k7_relat_1('#skF_5',A_359),k1_xboole_0)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1506,c_1561])).

tff(c_1585,plain,(
    ! [A_359] : k7_relat_1('#skF_5',k3_xboole_0(A_359,'#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_4,c_1573])).

tff(c_1673,plain,(
    ! [A_364,B_365,C_366,D_367] :
      ( k2_partfun1(A_364,B_365,C_366,D_367) = k7_relat_1(C_366,D_367)
      | ~ m1_subset_1(C_366,k1_zfmisc_1(k2_zfmisc_1(A_364,B_365)))
      | ~ v1_funct_1(C_366) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1677,plain,(
    ! [D_367] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_367) = k7_relat_1('#skF_5',D_367)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_1673])).

tff(c_1683,plain,(
    ! [D_367] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_367) = k7_relat_1('#skF_5',D_367) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1677])).

tff(c_120,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_113])).

tff(c_161,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_120,c_155])).

tff(c_167,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_161])).

tff(c_875,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_167])).

tff(c_1444,plain,(
    ! [C_344,A_345,B_346] :
      ( v1_partfun1(C_344,A_345)
      | ~ v1_funct_2(C_344,A_345,B_346)
      | ~ v1_funct_1(C_344)
      | ~ m1_subset_1(C_344,k1_zfmisc_1(k2_zfmisc_1(A_345,B_346)))
      | v1_xboole_0(B_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1447,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1444])).

tff(c_1453,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1447])).

tff(c_1455,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_875,c_1453])).

tff(c_1456,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_1461,plain,(
    ! [B_13] :
      ( k7_relat_1('#skF_6',B_13) = k1_xboole_0
      | ~ r1_xboole_0(B_13,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1456,c_12])).

tff(c_1473,plain,(
    ! [B_347] :
      ( k7_relat_1('#skF_6',B_347) = k1_xboole_0
      | ~ r1_xboole_0(B_347,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_1461])).

tff(c_1477,plain,(
    ! [A_14] :
      ( k7_relat_1('#skF_6',A_14) = k1_xboole_0
      | ~ r1_subset_1(A_14,'#skF_4')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_14) ) ),
    inference(resolution,[status(thm)],[c_16,c_1473])).

tff(c_1489,plain,(
    ! [A_349] :
      ( k7_relat_1('#skF_6',A_349) = k1_xboole_0
      | ~ r1_subset_1(A_349,'#skF_4')
      | v1_xboole_0(A_349) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1477])).

tff(c_1492,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_1489])).

tff(c_1495,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1492])).

tff(c_1576,plain,(
    ! [B_360] :
      ( k7_relat_1('#skF_6',k3_xboole_0('#skF_3',B_360)) = k3_xboole_0(k1_xboole_0,k7_relat_1('#skF_6',B_360))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1495,c_1561])).

tff(c_1587,plain,(
    ! [B_360] : k7_relat_1('#skF_6',k3_xboole_0('#skF_3',B_360)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_87,c_1576])).

tff(c_1675,plain,(
    ! [D_367] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_367) = k7_relat_1('#skF_6',D_367)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_50,c_1673])).

tff(c_1680,plain,(
    ! [D_367] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_367) = k7_relat_1('#skF_6',D_367) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1675])).

tff(c_1511,plain,(
    ! [A_351,B_352,C_353] :
      ( k9_subset_1(A_351,B_352,C_353) = k3_xboole_0(B_352,C_353)
      | ~ m1_subset_1(C_353,k1_zfmisc_1(A_351)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1523,plain,(
    ! [B_352] : k9_subset_1('#skF_1',B_352,'#skF_4') = k3_xboole_0(B_352,'#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_1511])).

tff(c_48,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_112,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_1533,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1523,c_1523,c_112])).

tff(c_2121,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1585,c_1683,c_1587,c_1680,c_1533])).

tff(c_2122,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_4300,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_2122])).

tff(c_123247,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_123236,c_4300])).

tff(c_123261,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_4142,c_4089,c_2195,c_2195,c_8710,c_123247])).

tff(c_123263,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_123261])).

tff(c_123264,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2122])).

tff(c_204036,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_204027,c_123264])).

tff(c_204047,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_4142,c_2195,c_4089,c_2195,c_129512,c_204036])).

tff(c_204049,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_204047])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:58:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 21.65/14.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.75/14.29  
% 21.75/14.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.75/14.29  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 21.75/14.29  
% 21.75/14.29  %Foreground sorts:
% 21.75/14.29  
% 21.75/14.29  
% 21.75/14.29  %Background operators:
% 21.75/14.29  
% 21.75/14.29  
% 21.75/14.29  %Foreground operators:
% 21.75/14.29  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 21.75/14.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 21.75/14.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 21.75/14.29  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 21.75/14.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 21.75/14.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 21.75/14.29  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 21.75/14.29  tff('#skF_5', type, '#skF_5': $i).
% 21.75/14.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 21.75/14.29  tff('#skF_6', type, '#skF_6': $i).
% 21.75/14.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 21.75/14.29  tff('#skF_2', type, '#skF_2': $i).
% 21.75/14.29  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 21.75/14.29  tff('#skF_3', type, '#skF_3': $i).
% 21.75/14.29  tff('#skF_1', type, '#skF_1': $i).
% 21.75/14.29  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 21.75/14.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 21.75/14.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 21.75/14.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 21.75/14.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 21.75/14.29  tff('#skF_4', type, '#skF_4': $i).
% 21.75/14.29  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 21.75/14.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 21.75/14.29  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 21.75/14.29  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 21.75/14.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 21.75/14.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 21.75/14.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 21.75/14.29  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 21.75/14.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 21.75/14.29  
% 22.00/14.32  tff(f_230, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 22.00/14.32  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 22.00/14.32  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 22.00/14.32  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 22.00/14.32  tff(f_58, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 22.00/14.32  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 22.00/14.32  tff(f_100, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 22.00/14.32  tff(f_92, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 22.00/14.32  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 22.00/14.32  tff(f_41, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_relat_1)).
% 22.00/14.32  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 22.00/14.32  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 22.00/14.32  tff(f_68, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) => r1_subset_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_subset_1)).
% 22.00/14.32  tff(f_188, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 22.00/14.32  tff(f_106, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 22.00/14.32  tff(f_154, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 22.00/14.32  tff(c_74, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_230])).
% 22.00/14.32  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_230])).
% 22.00/14.32  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_230])).
% 22.00/14.32  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_230])).
% 22.00/14.32  tff(c_103, plain, (![C_229, A_230, B_231]: (v1_relat_1(C_229) | ~m1_subset_1(C_229, k1_zfmisc_1(k2_zfmisc_1(A_230, B_231))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 22.00/14.32  tff(c_110, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_103])).
% 22.00/14.32  tff(c_6, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 22.00/14.32  tff(c_83, plain, (![A_226, B_227]: (k3_xboole_0(A_226, B_227)=A_226 | ~r1_tarski(A_226, B_227))), inference(cnfTransformation, [status(thm)], [f_29])).
% 22.00/14.32  tff(c_87, plain, (![A_4]: (k3_xboole_0(k1_xboole_0, A_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_83])).
% 22.00/14.32  tff(c_70, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_230])).
% 22.00/14.32  tff(c_62, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_230])).
% 22.00/14.32  tff(c_66, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_230])).
% 22.00/14.32  tff(c_16, plain, (![A_14, B_15]: (r1_xboole_0(A_14, B_15) | ~r1_subset_1(A_14, B_15) | v1_xboole_0(B_15) | v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 22.00/14.32  tff(c_72, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_230])).
% 22.00/14.32  tff(c_2124, plain, (![C_390, A_391, B_392]: (v4_relat_1(C_390, A_391) | ~m1_subset_1(C_390, k1_zfmisc_1(k2_zfmisc_1(A_391, B_392))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 22.00/14.32  tff(c_2131, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_2124])).
% 22.00/14.32  tff(c_2170, plain, (![B_405, A_406]: (k1_relat_1(B_405)=A_406 | ~v1_partfun1(B_405, A_406) | ~v4_relat_1(B_405, A_406) | ~v1_relat_1(B_405))), inference(cnfTransformation, [status(thm)], [f_100])).
% 22.00/14.32  tff(c_2176, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2131, c_2170])).
% 22.00/14.32  tff(c_2182, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_2176])).
% 22.00/14.32  tff(c_2974, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_2182])).
% 22.00/14.32  tff(c_54, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_230])).
% 22.00/14.32  tff(c_52, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_230])).
% 22.00/14.32  tff(c_3988, plain, (![C_515, A_516, B_517]: (v1_partfun1(C_515, A_516) | ~v1_funct_2(C_515, A_516, B_517) | ~v1_funct_1(C_515) | ~m1_subset_1(C_515, k1_zfmisc_1(k2_zfmisc_1(A_516, B_517))) | v1_xboole_0(B_517))), inference(cnfTransformation, [status(thm)], [f_92])).
% 22.00/14.32  tff(c_3991, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_3988])).
% 22.00/14.32  tff(c_3997, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_3991])).
% 22.00/14.32  tff(c_3999, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_2974, c_3997])).
% 22.00/14.32  tff(c_4000, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_2182])).
% 22.00/14.32  tff(c_12, plain, (![A_11, B_13]: (k7_relat_1(A_11, B_13)=k1_xboole_0 | ~r1_xboole_0(B_13, k1_relat_1(A_11)) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 22.00/14.32  tff(c_4005, plain, (![B_13]: (k7_relat_1('#skF_6', B_13)=k1_xboole_0 | ~r1_xboole_0(B_13, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_4000, c_12])).
% 22.00/14.32  tff(c_4035, plain, (![B_520]: (k7_relat_1('#skF_6', B_520)=k1_xboole_0 | ~r1_xboole_0(B_520, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_4005])).
% 22.00/14.32  tff(c_4039, plain, (![A_14]: (k7_relat_1('#skF_6', A_14)=k1_xboole_0 | ~r1_subset_1(A_14, '#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(A_14))), inference(resolution, [status(thm)], [c_16, c_4035])).
% 22.00/14.32  tff(c_4125, plain, (![A_528]: (k7_relat_1('#skF_6', A_528)=k1_xboole_0 | ~r1_subset_1(A_528, '#skF_4') | v1_xboole_0(A_528))), inference(negUnitSimplification, [status(thm)], [c_66, c_4039])).
% 22.00/14.32  tff(c_4128, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_62, c_4125])).
% 22.00/14.32  tff(c_4131, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_70, c_4128])).
% 22.00/14.32  tff(c_10, plain, (![C_10, A_8, B_9]: (k3_xboole_0(k7_relat_1(C_10, A_8), k7_relat_1(C_10, B_9))=k7_relat_1(C_10, k3_xboole_0(A_8, B_9)) | ~v1_relat_1(C_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 22.00/14.32  tff(c_4135, plain, (![B_9]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_3', B_9))=k3_xboole_0(k1_xboole_0, k7_relat_1('#skF_6', B_9)) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_4131, c_10])).
% 22.00/14.32  tff(c_4142, plain, (![B_9]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_3', B_9))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_110, c_87, c_4135])).
% 22.00/14.32  tff(c_2183, plain, (![A_407, B_408, C_409]: (k9_subset_1(A_407, B_408, C_409)=k3_xboole_0(B_408, C_409) | ~m1_subset_1(C_409, k1_zfmisc_1(A_407)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 22.00/14.32  tff(c_2195, plain, (![B_408]: (k9_subset_1('#skF_1', B_408, '#skF_4')=k3_xboole_0(B_408, '#skF_4'))), inference(resolution, [status(thm)], [c_64, c_2183])).
% 22.00/14.32  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_230])).
% 22.00/14.32  tff(c_111, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_103])).
% 22.00/14.32  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 22.00/14.32  tff(c_2148, plain, (![B_399, A_400]: (r1_subset_1(B_399, A_400) | ~r1_subset_1(A_400, B_399) | v1_xboole_0(B_399) | v1_xboole_0(A_400))), inference(cnfTransformation, [status(thm)], [f_68])).
% 22.00/14.32  tff(c_2150, plain, (r1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_62, c_2148])).
% 22.00/14.32  tff(c_2153, plain, (r1_subset_1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_70, c_66, c_2150])).
% 22.00/14.32  tff(c_2132, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_2124])).
% 22.00/14.32  tff(c_2173, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2132, c_2170])).
% 22.00/14.32  tff(c_2179, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_2173])).
% 22.00/14.32  tff(c_2196, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_2179])).
% 22.00/14.32  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_230])).
% 22.00/14.32  tff(c_58, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_230])).
% 22.00/14.32  tff(c_2932, plain, (![C_465, A_466, B_467]: (v1_partfun1(C_465, A_466) | ~v1_funct_2(C_465, A_466, B_467) | ~v1_funct_1(C_465) | ~m1_subset_1(C_465, k1_zfmisc_1(k2_zfmisc_1(A_466, B_467))) | v1_xboole_0(B_467))), inference(cnfTransformation, [status(thm)], [f_92])).
% 22.00/14.32  tff(c_2938, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_56, c_2932])).
% 22.00/14.32  tff(c_2945, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_2938])).
% 22.00/14.32  tff(c_2947, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_2196, c_2945])).
% 22.00/14.32  tff(c_2948, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_2179])).
% 22.00/14.32  tff(c_2953, plain, (![B_13]: (k7_relat_1('#skF_5', B_13)=k1_xboole_0 | ~r1_xboole_0(B_13, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2948, c_12])).
% 22.00/14.32  tff(c_4027, plain, (![B_519]: (k7_relat_1('#skF_5', B_519)=k1_xboole_0 | ~r1_xboole_0(B_519, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_2953])).
% 22.00/14.32  tff(c_4031, plain, (![A_14]: (k7_relat_1('#skF_5', A_14)=k1_xboole_0 | ~r1_subset_1(A_14, '#skF_3') | v1_xboole_0('#skF_3') | v1_xboole_0(A_14))), inference(resolution, [status(thm)], [c_16, c_4027])).
% 22.00/14.32  tff(c_4061, plain, (![A_523]: (k7_relat_1('#skF_5', A_523)=k1_xboole_0 | ~r1_subset_1(A_523, '#skF_3') | v1_xboole_0(A_523))), inference(negUnitSimplification, [status(thm)], [c_70, c_4031])).
% 22.00/14.32  tff(c_4064, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_2153, c_4061])).
% 22.00/14.32  tff(c_4067, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_66, c_4064])).
% 22.00/14.32  tff(c_4083, plain, (![A_8]: (k7_relat_1('#skF_5', k3_xboole_0(A_8, '#skF_4'))=k3_xboole_0(k7_relat_1('#skF_5', A_8), k1_xboole_0) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4067, c_10])).
% 22.00/14.32  tff(c_4089, plain, (![A_8]: (k7_relat_1('#skF_5', k3_xboole_0(A_8, '#skF_4'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_111, c_4, c_4083])).
% 22.00/14.32  tff(c_126133, plain, (![E_2113, C_2111, D_2110, F_2114, A_2112, B_2109]: (v1_funct_1(k1_tmap_1(A_2112, B_2109, C_2111, D_2110, E_2113, F_2114)) | ~m1_subset_1(F_2114, k1_zfmisc_1(k2_zfmisc_1(D_2110, B_2109))) | ~v1_funct_2(F_2114, D_2110, B_2109) | ~v1_funct_1(F_2114) | ~m1_subset_1(E_2113, k1_zfmisc_1(k2_zfmisc_1(C_2111, B_2109))) | ~v1_funct_2(E_2113, C_2111, B_2109) | ~v1_funct_1(E_2113) | ~m1_subset_1(D_2110, k1_zfmisc_1(A_2112)) | v1_xboole_0(D_2110) | ~m1_subset_1(C_2111, k1_zfmisc_1(A_2112)) | v1_xboole_0(C_2111) | v1_xboole_0(B_2109) | v1_xboole_0(A_2112))), inference(cnfTransformation, [status(thm)], [f_188])).
% 22.00/14.32  tff(c_126135, plain, (![A_2112, C_2111, E_2113]: (v1_funct_1(k1_tmap_1(A_2112, '#skF_2', C_2111, '#skF_4', E_2113, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_2113, k1_zfmisc_1(k2_zfmisc_1(C_2111, '#skF_2'))) | ~v1_funct_2(E_2113, C_2111, '#skF_2') | ~v1_funct_1(E_2113) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2112)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_2111, k1_zfmisc_1(A_2112)) | v1_xboole_0(C_2111) | v1_xboole_0('#skF_2') | v1_xboole_0(A_2112))), inference(resolution, [status(thm)], [c_50, c_126133])).
% 22.00/14.32  tff(c_126140, plain, (![A_2112, C_2111, E_2113]: (v1_funct_1(k1_tmap_1(A_2112, '#skF_2', C_2111, '#skF_4', E_2113, '#skF_6')) | ~m1_subset_1(E_2113, k1_zfmisc_1(k2_zfmisc_1(C_2111, '#skF_2'))) | ~v1_funct_2(E_2113, C_2111, '#skF_2') | ~v1_funct_1(E_2113) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2112)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_2111, k1_zfmisc_1(A_2112)) | v1_xboole_0(C_2111) | v1_xboole_0('#skF_2') | v1_xboole_0(A_2112))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_126135])).
% 22.00/14.32  tff(c_126677, plain, (![A_2127, C_2128, E_2129]: (v1_funct_1(k1_tmap_1(A_2127, '#skF_2', C_2128, '#skF_4', E_2129, '#skF_6')) | ~m1_subset_1(E_2129, k1_zfmisc_1(k2_zfmisc_1(C_2128, '#skF_2'))) | ~v1_funct_2(E_2129, C_2128, '#skF_2') | ~v1_funct_1(E_2129) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2127)) | ~m1_subset_1(C_2128, k1_zfmisc_1(A_2127)) | v1_xboole_0(C_2128) | v1_xboole_0(A_2127))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_126140])).
% 22.00/14.32  tff(c_126681, plain, (![A_2127]: (v1_funct_1(k1_tmap_1(A_2127, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2127)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_2127)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2127))), inference(resolution, [status(thm)], [c_56, c_126677])).
% 22.00/14.32  tff(c_126688, plain, (![A_2127]: (v1_funct_1(k1_tmap_1(A_2127, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2127)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_2127)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2127))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_126681])).
% 22.00/14.32  tff(c_129505, plain, (![A_2203]: (v1_funct_1(k1_tmap_1(A_2203, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2203)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_2203)) | v1_xboole_0(A_2203))), inference(negUnitSimplification, [status(thm)], [c_70, c_126688])).
% 22.00/14.32  tff(c_129508, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_68, c_129505])).
% 22.00/14.32  tff(c_129511, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_129508])).
% 22.00/14.32  tff(c_129512, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_74, c_129511])).
% 22.00/14.32  tff(c_4238, plain, (![A_532, B_533, C_534, D_535]: (k2_partfun1(A_532, B_533, C_534, D_535)=k7_relat_1(C_534, D_535) | ~m1_subset_1(C_534, k1_zfmisc_1(k2_zfmisc_1(A_532, B_533))) | ~v1_funct_1(C_534))), inference(cnfTransformation, [status(thm)], [f_106])).
% 22.00/14.32  tff(c_4242, plain, (![D_535]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_535)=k7_relat_1('#skF_5', D_535) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_4238])).
% 22.00/14.32  tff(c_4248, plain, (![D_535]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_535)=k7_relat_1('#skF_5', D_535))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_4242])).
% 22.00/14.32  tff(c_4240, plain, (![D_535]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_535)=k7_relat_1('#skF_6', D_535) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_50, c_4238])).
% 22.00/14.32  tff(c_4245, plain, (![D_535]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_535)=k7_relat_1('#skF_6', D_535))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_4240])).
% 22.00/14.32  tff(c_44, plain, (![E_165, C_163, F_166, A_161, B_162, D_164]: (v1_funct_2(k1_tmap_1(A_161, B_162, C_163, D_164, E_165, F_166), k4_subset_1(A_161, C_163, D_164), B_162) | ~m1_subset_1(F_166, k1_zfmisc_1(k2_zfmisc_1(D_164, B_162))) | ~v1_funct_2(F_166, D_164, B_162) | ~v1_funct_1(F_166) | ~m1_subset_1(E_165, k1_zfmisc_1(k2_zfmisc_1(C_163, B_162))) | ~v1_funct_2(E_165, C_163, B_162) | ~v1_funct_1(E_165) | ~m1_subset_1(D_164, k1_zfmisc_1(A_161)) | v1_xboole_0(D_164) | ~m1_subset_1(C_163, k1_zfmisc_1(A_161)) | v1_xboole_0(C_163) | v1_xboole_0(B_162) | v1_xboole_0(A_161))), inference(cnfTransformation, [status(thm)], [f_188])).
% 22.00/14.32  tff(c_42, plain, (![E_165, C_163, F_166, A_161, B_162, D_164]: (m1_subset_1(k1_tmap_1(A_161, B_162, C_163, D_164, E_165, F_166), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_161, C_163, D_164), B_162))) | ~m1_subset_1(F_166, k1_zfmisc_1(k2_zfmisc_1(D_164, B_162))) | ~v1_funct_2(F_166, D_164, B_162) | ~v1_funct_1(F_166) | ~m1_subset_1(E_165, k1_zfmisc_1(k2_zfmisc_1(C_163, B_162))) | ~v1_funct_2(E_165, C_163, B_162) | ~v1_funct_1(E_165) | ~m1_subset_1(D_164, k1_zfmisc_1(A_161)) | v1_xboole_0(D_164) | ~m1_subset_1(C_163, k1_zfmisc_1(A_161)) | v1_xboole_0(C_163) | v1_xboole_0(B_162) | v1_xboole_0(A_161))), inference(cnfTransformation, [status(thm)], [f_188])).
% 22.00/14.32  tff(c_130421, plain, (![D_2225, A_2220, B_2223, F_2222, E_2224, C_2221]: (k2_partfun1(k4_subset_1(A_2220, C_2221, D_2225), B_2223, k1_tmap_1(A_2220, B_2223, C_2221, D_2225, E_2224, F_2222), C_2221)=E_2224 | ~m1_subset_1(k1_tmap_1(A_2220, B_2223, C_2221, D_2225, E_2224, F_2222), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_2220, C_2221, D_2225), B_2223))) | ~v1_funct_2(k1_tmap_1(A_2220, B_2223, C_2221, D_2225, E_2224, F_2222), k4_subset_1(A_2220, C_2221, D_2225), B_2223) | ~v1_funct_1(k1_tmap_1(A_2220, B_2223, C_2221, D_2225, E_2224, F_2222)) | k2_partfun1(D_2225, B_2223, F_2222, k9_subset_1(A_2220, C_2221, D_2225))!=k2_partfun1(C_2221, B_2223, E_2224, k9_subset_1(A_2220, C_2221, D_2225)) | ~m1_subset_1(F_2222, k1_zfmisc_1(k2_zfmisc_1(D_2225, B_2223))) | ~v1_funct_2(F_2222, D_2225, B_2223) | ~v1_funct_1(F_2222) | ~m1_subset_1(E_2224, k1_zfmisc_1(k2_zfmisc_1(C_2221, B_2223))) | ~v1_funct_2(E_2224, C_2221, B_2223) | ~v1_funct_1(E_2224) | ~m1_subset_1(D_2225, k1_zfmisc_1(A_2220)) | v1_xboole_0(D_2225) | ~m1_subset_1(C_2221, k1_zfmisc_1(A_2220)) | v1_xboole_0(C_2221) | v1_xboole_0(B_2223) | v1_xboole_0(A_2220))), inference(cnfTransformation, [status(thm)], [f_154])).
% 22.00/14.32  tff(c_161539, plain, (![A_2724, E_2725, B_2721, D_2722, F_2726, C_2723]: (k2_partfun1(k4_subset_1(A_2724, C_2723, D_2722), B_2721, k1_tmap_1(A_2724, B_2721, C_2723, D_2722, E_2725, F_2726), C_2723)=E_2725 | ~v1_funct_2(k1_tmap_1(A_2724, B_2721, C_2723, D_2722, E_2725, F_2726), k4_subset_1(A_2724, C_2723, D_2722), B_2721) | ~v1_funct_1(k1_tmap_1(A_2724, B_2721, C_2723, D_2722, E_2725, F_2726)) | k2_partfun1(D_2722, B_2721, F_2726, k9_subset_1(A_2724, C_2723, D_2722))!=k2_partfun1(C_2723, B_2721, E_2725, k9_subset_1(A_2724, C_2723, D_2722)) | ~m1_subset_1(F_2726, k1_zfmisc_1(k2_zfmisc_1(D_2722, B_2721))) | ~v1_funct_2(F_2726, D_2722, B_2721) | ~v1_funct_1(F_2726) | ~m1_subset_1(E_2725, k1_zfmisc_1(k2_zfmisc_1(C_2723, B_2721))) | ~v1_funct_2(E_2725, C_2723, B_2721) | ~v1_funct_1(E_2725) | ~m1_subset_1(D_2722, k1_zfmisc_1(A_2724)) | v1_xboole_0(D_2722) | ~m1_subset_1(C_2723, k1_zfmisc_1(A_2724)) | v1_xboole_0(C_2723) | v1_xboole_0(B_2721) | v1_xboole_0(A_2724))), inference(resolution, [status(thm)], [c_42, c_130421])).
% 22.00/14.32  tff(c_189598, plain, (![C_3035, B_3033, E_3037, A_3036, F_3038, D_3034]: (k2_partfun1(k4_subset_1(A_3036, C_3035, D_3034), B_3033, k1_tmap_1(A_3036, B_3033, C_3035, D_3034, E_3037, F_3038), C_3035)=E_3037 | ~v1_funct_1(k1_tmap_1(A_3036, B_3033, C_3035, D_3034, E_3037, F_3038)) | k2_partfun1(D_3034, B_3033, F_3038, k9_subset_1(A_3036, C_3035, D_3034))!=k2_partfun1(C_3035, B_3033, E_3037, k9_subset_1(A_3036, C_3035, D_3034)) | ~m1_subset_1(F_3038, k1_zfmisc_1(k2_zfmisc_1(D_3034, B_3033))) | ~v1_funct_2(F_3038, D_3034, B_3033) | ~v1_funct_1(F_3038) | ~m1_subset_1(E_3037, k1_zfmisc_1(k2_zfmisc_1(C_3035, B_3033))) | ~v1_funct_2(E_3037, C_3035, B_3033) | ~v1_funct_1(E_3037) | ~m1_subset_1(D_3034, k1_zfmisc_1(A_3036)) | v1_xboole_0(D_3034) | ~m1_subset_1(C_3035, k1_zfmisc_1(A_3036)) | v1_xboole_0(C_3035) | v1_xboole_0(B_3033) | v1_xboole_0(A_3036))), inference(resolution, [status(thm)], [c_44, c_161539])).
% 22.00/14.32  tff(c_189602, plain, (![A_3036, C_3035, E_3037]: (k2_partfun1(k4_subset_1(A_3036, C_3035, '#skF_4'), '#skF_2', k1_tmap_1(A_3036, '#skF_2', C_3035, '#skF_4', E_3037, '#skF_6'), C_3035)=E_3037 | ~v1_funct_1(k1_tmap_1(A_3036, '#skF_2', C_3035, '#skF_4', E_3037, '#skF_6')) | k2_partfun1(C_3035, '#skF_2', E_3037, k9_subset_1(A_3036, C_3035, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_3036, C_3035, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_3037, k1_zfmisc_1(k2_zfmisc_1(C_3035, '#skF_2'))) | ~v1_funct_2(E_3037, C_3035, '#skF_2') | ~v1_funct_1(E_3037) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3036)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_3035, k1_zfmisc_1(A_3036)) | v1_xboole_0(C_3035) | v1_xboole_0('#skF_2') | v1_xboole_0(A_3036))), inference(resolution, [status(thm)], [c_50, c_189598])).
% 22.00/14.32  tff(c_189608, plain, (![A_3036, C_3035, E_3037]: (k2_partfun1(k4_subset_1(A_3036, C_3035, '#skF_4'), '#skF_2', k1_tmap_1(A_3036, '#skF_2', C_3035, '#skF_4', E_3037, '#skF_6'), C_3035)=E_3037 | ~v1_funct_1(k1_tmap_1(A_3036, '#skF_2', C_3035, '#skF_4', E_3037, '#skF_6')) | k2_partfun1(C_3035, '#skF_2', E_3037, k9_subset_1(A_3036, C_3035, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_3036, C_3035, '#skF_4')) | ~m1_subset_1(E_3037, k1_zfmisc_1(k2_zfmisc_1(C_3035, '#skF_2'))) | ~v1_funct_2(E_3037, C_3035, '#skF_2') | ~v1_funct_1(E_3037) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3036)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_3035, k1_zfmisc_1(A_3036)) | v1_xboole_0(C_3035) | v1_xboole_0('#skF_2') | v1_xboole_0(A_3036))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_4245, c_189602])).
% 22.00/14.32  tff(c_191825, plain, (![A_3057, C_3058, E_3059]: (k2_partfun1(k4_subset_1(A_3057, C_3058, '#skF_4'), '#skF_2', k1_tmap_1(A_3057, '#skF_2', C_3058, '#skF_4', E_3059, '#skF_6'), C_3058)=E_3059 | ~v1_funct_1(k1_tmap_1(A_3057, '#skF_2', C_3058, '#skF_4', E_3059, '#skF_6')) | k2_partfun1(C_3058, '#skF_2', E_3059, k9_subset_1(A_3057, C_3058, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_3057, C_3058, '#skF_4')) | ~m1_subset_1(E_3059, k1_zfmisc_1(k2_zfmisc_1(C_3058, '#skF_2'))) | ~v1_funct_2(E_3059, C_3058, '#skF_2') | ~v1_funct_1(E_3059) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3057)) | ~m1_subset_1(C_3058, k1_zfmisc_1(A_3057)) | v1_xboole_0(C_3058) | v1_xboole_0(A_3057))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_189608])).
% 22.00/14.32  tff(c_191832, plain, (![A_3057]: (k2_partfun1(k4_subset_1(A_3057, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_3057, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_3057, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_3057, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_3057, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3057)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_3057)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_3057))), inference(resolution, [status(thm)], [c_56, c_191825])).
% 22.00/14.32  tff(c_191842, plain, (![A_3057]: (k2_partfun1(k4_subset_1(A_3057, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_3057, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_3057, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_3057, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_3057, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3057)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_3057)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_3057))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_4248, c_191832])).
% 22.00/14.32  tff(c_204027, plain, (![A_3172]: (k2_partfun1(k4_subset_1(A_3172, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_3172, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_3172, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_3172, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_3172, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3172)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_3172)) | v1_xboole_0(A_3172))), inference(negUnitSimplification, [status(thm)], [c_70, c_191842])).
% 22.00/14.32  tff(c_5951, plain, (![C_604, A_605, E_606, D_603, F_607, B_602]: (v1_funct_1(k1_tmap_1(A_605, B_602, C_604, D_603, E_606, F_607)) | ~m1_subset_1(F_607, k1_zfmisc_1(k2_zfmisc_1(D_603, B_602))) | ~v1_funct_2(F_607, D_603, B_602) | ~v1_funct_1(F_607) | ~m1_subset_1(E_606, k1_zfmisc_1(k2_zfmisc_1(C_604, B_602))) | ~v1_funct_2(E_606, C_604, B_602) | ~v1_funct_1(E_606) | ~m1_subset_1(D_603, k1_zfmisc_1(A_605)) | v1_xboole_0(D_603) | ~m1_subset_1(C_604, k1_zfmisc_1(A_605)) | v1_xboole_0(C_604) | v1_xboole_0(B_602) | v1_xboole_0(A_605))), inference(cnfTransformation, [status(thm)], [f_188])).
% 22.00/14.32  tff(c_5953, plain, (![A_605, C_604, E_606]: (v1_funct_1(k1_tmap_1(A_605, '#skF_2', C_604, '#skF_4', E_606, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_606, k1_zfmisc_1(k2_zfmisc_1(C_604, '#skF_2'))) | ~v1_funct_2(E_606, C_604, '#skF_2') | ~v1_funct_1(E_606) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_605)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_604, k1_zfmisc_1(A_605)) | v1_xboole_0(C_604) | v1_xboole_0('#skF_2') | v1_xboole_0(A_605))), inference(resolution, [status(thm)], [c_50, c_5951])).
% 22.00/14.32  tff(c_5958, plain, (![A_605, C_604, E_606]: (v1_funct_1(k1_tmap_1(A_605, '#skF_2', C_604, '#skF_4', E_606, '#skF_6')) | ~m1_subset_1(E_606, k1_zfmisc_1(k2_zfmisc_1(C_604, '#skF_2'))) | ~v1_funct_2(E_606, C_604, '#skF_2') | ~v1_funct_1(E_606) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_605)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_604, k1_zfmisc_1(A_605)) | v1_xboole_0(C_604) | v1_xboole_0('#skF_2') | v1_xboole_0(A_605))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_5953])).
% 22.00/14.32  tff(c_6331, plain, (![A_619, C_620, E_621]: (v1_funct_1(k1_tmap_1(A_619, '#skF_2', C_620, '#skF_4', E_621, '#skF_6')) | ~m1_subset_1(E_621, k1_zfmisc_1(k2_zfmisc_1(C_620, '#skF_2'))) | ~v1_funct_2(E_621, C_620, '#skF_2') | ~v1_funct_1(E_621) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_619)) | ~m1_subset_1(C_620, k1_zfmisc_1(A_619)) | v1_xboole_0(C_620) | v1_xboole_0(A_619))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_5958])).
% 22.00/14.32  tff(c_6335, plain, (![A_619]: (v1_funct_1(k1_tmap_1(A_619, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_619)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_619)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_619))), inference(resolution, [status(thm)], [c_56, c_6331])).
% 22.00/14.32  tff(c_6342, plain, (![A_619]: (v1_funct_1(k1_tmap_1(A_619, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_619)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_619)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_619))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_6335])).
% 22.00/14.32  tff(c_8703, plain, (![A_695]: (v1_funct_1(k1_tmap_1(A_695, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_695)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_695)) | v1_xboole_0(A_695))), inference(negUnitSimplification, [status(thm)], [c_70, c_6342])).
% 22.00/14.32  tff(c_8706, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_68, c_8703])).
% 22.00/14.32  tff(c_8709, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_8706])).
% 22.00/14.32  tff(c_8710, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_74, c_8709])).
% 22.00/14.32  tff(c_11258, plain, (![B_756, A_753, C_754, E_757, D_758, F_755]: (k2_partfun1(k4_subset_1(A_753, C_754, D_758), B_756, k1_tmap_1(A_753, B_756, C_754, D_758, E_757, F_755), D_758)=F_755 | ~m1_subset_1(k1_tmap_1(A_753, B_756, C_754, D_758, E_757, F_755), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_753, C_754, D_758), B_756))) | ~v1_funct_2(k1_tmap_1(A_753, B_756, C_754, D_758, E_757, F_755), k4_subset_1(A_753, C_754, D_758), B_756) | ~v1_funct_1(k1_tmap_1(A_753, B_756, C_754, D_758, E_757, F_755)) | k2_partfun1(D_758, B_756, F_755, k9_subset_1(A_753, C_754, D_758))!=k2_partfun1(C_754, B_756, E_757, k9_subset_1(A_753, C_754, D_758)) | ~m1_subset_1(F_755, k1_zfmisc_1(k2_zfmisc_1(D_758, B_756))) | ~v1_funct_2(F_755, D_758, B_756) | ~v1_funct_1(F_755) | ~m1_subset_1(E_757, k1_zfmisc_1(k2_zfmisc_1(C_754, B_756))) | ~v1_funct_2(E_757, C_754, B_756) | ~v1_funct_1(E_757) | ~m1_subset_1(D_758, k1_zfmisc_1(A_753)) | v1_xboole_0(D_758) | ~m1_subset_1(C_754, k1_zfmisc_1(A_753)) | v1_xboole_0(C_754) | v1_xboole_0(B_756) | v1_xboole_0(A_753))), inference(cnfTransformation, [status(thm)], [f_154])).
% 22.00/14.32  tff(c_38284, plain, (![E_1199, B_1195, F_1200, C_1197, A_1198, D_1196]: (k2_partfun1(k4_subset_1(A_1198, C_1197, D_1196), B_1195, k1_tmap_1(A_1198, B_1195, C_1197, D_1196, E_1199, F_1200), D_1196)=F_1200 | ~v1_funct_2(k1_tmap_1(A_1198, B_1195, C_1197, D_1196, E_1199, F_1200), k4_subset_1(A_1198, C_1197, D_1196), B_1195) | ~v1_funct_1(k1_tmap_1(A_1198, B_1195, C_1197, D_1196, E_1199, F_1200)) | k2_partfun1(D_1196, B_1195, F_1200, k9_subset_1(A_1198, C_1197, D_1196))!=k2_partfun1(C_1197, B_1195, E_1199, k9_subset_1(A_1198, C_1197, D_1196)) | ~m1_subset_1(F_1200, k1_zfmisc_1(k2_zfmisc_1(D_1196, B_1195))) | ~v1_funct_2(F_1200, D_1196, B_1195) | ~v1_funct_1(F_1200) | ~m1_subset_1(E_1199, k1_zfmisc_1(k2_zfmisc_1(C_1197, B_1195))) | ~v1_funct_2(E_1199, C_1197, B_1195) | ~v1_funct_1(E_1199) | ~m1_subset_1(D_1196, k1_zfmisc_1(A_1198)) | v1_xboole_0(D_1196) | ~m1_subset_1(C_1197, k1_zfmisc_1(A_1198)) | v1_xboole_0(C_1197) | v1_xboole_0(B_1195) | v1_xboole_0(A_1198))), inference(resolution, [status(thm)], [c_42, c_11258])).
% 22.00/14.32  tff(c_66406, plain, (![D_1520, B_1519, C_1521, F_1524, A_1522, E_1523]: (k2_partfun1(k4_subset_1(A_1522, C_1521, D_1520), B_1519, k1_tmap_1(A_1522, B_1519, C_1521, D_1520, E_1523, F_1524), D_1520)=F_1524 | ~v1_funct_1(k1_tmap_1(A_1522, B_1519, C_1521, D_1520, E_1523, F_1524)) | k2_partfun1(D_1520, B_1519, F_1524, k9_subset_1(A_1522, C_1521, D_1520))!=k2_partfun1(C_1521, B_1519, E_1523, k9_subset_1(A_1522, C_1521, D_1520)) | ~m1_subset_1(F_1524, k1_zfmisc_1(k2_zfmisc_1(D_1520, B_1519))) | ~v1_funct_2(F_1524, D_1520, B_1519) | ~v1_funct_1(F_1524) | ~m1_subset_1(E_1523, k1_zfmisc_1(k2_zfmisc_1(C_1521, B_1519))) | ~v1_funct_2(E_1523, C_1521, B_1519) | ~v1_funct_1(E_1523) | ~m1_subset_1(D_1520, k1_zfmisc_1(A_1522)) | v1_xboole_0(D_1520) | ~m1_subset_1(C_1521, k1_zfmisc_1(A_1522)) | v1_xboole_0(C_1521) | v1_xboole_0(B_1519) | v1_xboole_0(A_1522))), inference(resolution, [status(thm)], [c_44, c_38284])).
% 22.00/14.32  tff(c_66410, plain, (![A_1522, C_1521, E_1523]: (k2_partfun1(k4_subset_1(A_1522, C_1521, '#skF_4'), '#skF_2', k1_tmap_1(A_1522, '#skF_2', C_1521, '#skF_4', E_1523, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1522, '#skF_2', C_1521, '#skF_4', E_1523, '#skF_6')) | k2_partfun1(C_1521, '#skF_2', E_1523, k9_subset_1(A_1522, C_1521, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_1522, C_1521, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1523, k1_zfmisc_1(k2_zfmisc_1(C_1521, '#skF_2'))) | ~v1_funct_2(E_1523, C_1521, '#skF_2') | ~v1_funct_1(E_1523) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1522)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1521, k1_zfmisc_1(A_1522)) | v1_xboole_0(C_1521) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1522))), inference(resolution, [status(thm)], [c_50, c_66406])).
% 22.00/14.32  tff(c_66416, plain, (![A_1522, C_1521, E_1523]: (k2_partfun1(k4_subset_1(A_1522, C_1521, '#skF_4'), '#skF_2', k1_tmap_1(A_1522, '#skF_2', C_1521, '#skF_4', E_1523, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1522, '#skF_2', C_1521, '#skF_4', E_1523, '#skF_6')) | k2_partfun1(C_1521, '#skF_2', E_1523, k9_subset_1(A_1522, C_1521, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1522, C_1521, '#skF_4')) | ~m1_subset_1(E_1523, k1_zfmisc_1(k2_zfmisc_1(C_1521, '#skF_2'))) | ~v1_funct_2(E_1523, C_1521, '#skF_2') | ~v1_funct_1(E_1523) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1522)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1521, k1_zfmisc_1(A_1522)) | v1_xboole_0(C_1521) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1522))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_4245, c_66410])).
% 22.00/14.32  tff(c_104489, plain, (![A_1865, C_1866, E_1867]: (k2_partfun1(k4_subset_1(A_1865, C_1866, '#skF_4'), '#skF_2', k1_tmap_1(A_1865, '#skF_2', C_1866, '#skF_4', E_1867, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1865, '#skF_2', C_1866, '#skF_4', E_1867, '#skF_6')) | k2_partfun1(C_1866, '#skF_2', E_1867, k9_subset_1(A_1865, C_1866, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1865, C_1866, '#skF_4')) | ~m1_subset_1(E_1867, k1_zfmisc_1(k2_zfmisc_1(C_1866, '#skF_2'))) | ~v1_funct_2(E_1867, C_1866, '#skF_2') | ~v1_funct_1(E_1867) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1865)) | ~m1_subset_1(C_1866, k1_zfmisc_1(A_1865)) | v1_xboole_0(C_1866) | v1_xboole_0(A_1865))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_66416])).
% 22.00/14.32  tff(c_104496, plain, (![A_1865]: (k2_partfun1(k4_subset_1(A_1865, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1865, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1865, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_1865, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1865, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1865)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1865)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1865))), inference(resolution, [status(thm)], [c_56, c_104489])).
% 22.00/14.32  tff(c_104506, plain, (![A_1865]: (k2_partfun1(k4_subset_1(A_1865, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1865, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1865, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1865, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1865, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1865)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1865)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1865))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_4248, c_104496])).
% 22.00/14.32  tff(c_123236, plain, (![A_2011]: (k2_partfun1(k4_subset_1(A_2011, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_2011, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_2011, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_2011, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2011, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2011)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_2011)) | v1_xboole_0(A_2011))), inference(negUnitSimplification, [status(thm)], [c_70, c_104506])).
% 22.00/14.32  tff(c_132, plain, (![B_239, A_240]: (r1_subset_1(B_239, A_240) | ~r1_subset_1(A_240, B_239) | v1_xboole_0(B_239) | v1_xboole_0(A_240))), inference(cnfTransformation, [status(thm)], [f_68])).
% 22.00/14.32  tff(c_134, plain, (r1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_62, c_132])).
% 22.00/14.32  tff(c_137, plain, (r1_subset_1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_70, c_66, c_134])).
% 22.00/14.32  tff(c_113, plain, (![C_232, A_233, B_234]: (v4_relat_1(C_232, A_233) | ~m1_subset_1(C_232, k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 22.00/14.32  tff(c_121, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_113])).
% 22.00/14.32  tff(c_155, plain, (![B_247, A_248]: (k1_relat_1(B_247)=A_248 | ~v1_partfun1(B_247, A_248) | ~v4_relat_1(B_247, A_248) | ~v1_relat_1(B_247))), inference(cnfTransformation, [status(thm)], [f_100])).
% 22.00/14.32  tff(c_158, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_121, c_155])).
% 22.00/14.32  tff(c_164, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_158])).
% 22.00/14.32  tff(c_168, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_164])).
% 22.00/14.32  tff(c_842, plain, (![C_304, A_305, B_306]: (v1_partfun1(C_304, A_305) | ~v1_funct_2(C_304, A_305, B_306) | ~v1_funct_1(C_304) | ~m1_subset_1(C_304, k1_zfmisc_1(k2_zfmisc_1(A_305, B_306))) | v1_xboole_0(B_306))), inference(cnfTransformation, [status(thm)], [f_92])).
% 22.00/14.32  tff(c_848, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_56, c_842])).
% 22.00/14.32  tff(c_855, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_848])).
% 22.00/14.32  tff(c_857, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_168, c_855])).
% 22.00/14.32  tff(c_858, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_164])).
% 22.00/14.32  tff(c_863, plain, (![B_13]: (k7_relat_1('#skF_5', B_13)=k1_xboole_0 | ~r1_xboole_0(B_13, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_858, c_12])).
% 22.00/14.32  tff(c_1481, plain, (![B_348]: (k7_relat_1('#skF_5', B_348)=k1_xboole_0 | ~r1_xboole_0(B_348, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_863])).
% 22.00/14.32  tff(c_1485, plain, (![A_14]: (k7_relat_1('#skF_5', A_14)=k1_xboole_0 | ~r1_subset_1(A_14, '#skF_3') | v1_xboole_0('#skF_3') | v1_xboole_0(A_14))), inference(resolution, [status(thm)], [c_16, c_1481])).
% 22.00/14.32  tff(c_1500, plain, (![A_350]: (k7_relat_1('#skF_5', A_350)=k1_xboole_0 | ~r1_subset_1(A_350, '#skF_3') | v1_xboole_0(A_350))), inference(negUnitSimplification, [status(thm)], [c_70, c_1485])).
% 22.00/14.32  tff(c_1503, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_137, c_1500])).
% 22.00/14.32  tff(c_1506, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_66, c_1503])).
% 22.00/14.32  tff(c_1561, plain, (![C_358, A_359, B_360]: (k3_xboole_0(k7_relat_1(C_358, A_359), k7_relat_1(C_358, B_360))=k7_relat_1(C_358, k3_xboole_0(A_359, B_360)) | ~v1_relat_1(C_358))), inference(cnfTransformation, [status(thm)], [f_41])).
% 22.00/14.32  tff(c_1573, plain, (![A_359]: (k7_relat_1('#skF_5', k3_xboole_0(A_359, '#skF_4'))=k3_xboole_0(k7_relat_1('#skF_5', A_359), k1_xboole_0) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1506, c_1561])).
% 22.00/14.32  tff(c_1585, plain, (![A_359]: (k7_relat_1('#skF_5', k3_xboole_0(A_359, '#skF_4'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_111, c_4, c_1573])).
% 22.00/14.32  tff(c_1673, plain, (![A_364, B_365, C_366, D_367]: (k2_partfun1(A_364, B_365, C_366, D_367)=k7_relat_1(C_366, D_367) | ~m1_subset_1(C_366, k1_zfmisc_1(k2_zfmisc_1(A_364, B_365))) | ~v1_funct_1(C_366))), inference(cnfTransformation, [status(thm)], [f_106])).
% 22.00/14.32  tff(c_1677, plain, (![D_367]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_367)=k7_relat_1('#skF_5', D_367) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_1673])).
% 22.00/14.32  tff(c_1683, plain, (![D_367]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_367)=k7_relat_1('#skF_5', D_367))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1677])).
% 22.00/14.32  tff(c_120, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_113])).
% 22.00/14.32  tff(c_161, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_120, c_155])).
% 22.00/14.32  tff(c_167, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_161])).
% 22.00/14.32  tff(c_875, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_167])).
% 22.00/14.32  tff(c_1444, plain, (![C_344, A_345, B_346]: (v1_partfun1(C_344, A_345) | ~v1_funct_2(C_344, A_345, B_346) | ~v1_funct_1(C_344) | ~m1_subset_1(C_344, k1_zfmisc_1(k2_zfmisc_1(A_345, B_346))) | v1_xboole_0(B_346))), inference(cnfTransformation, [status(thm)], [f_92])).
% 22.00/14.32  tff(c_1447, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1444])).
% 22.00/14.32  tff(c_1453, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1447])).
% 22.00/14.32  tff(c_1455, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_875, c_1453])).
% 22.00/14.32  tff(c_1456, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_167])).
% 22.00/14.32  tff(c_1461, plain, (![B_13]: (k7_relat_1('#skF_6', B_13)=k1_xboole_0 | ~r1_xboole_0(B_13, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1456, c_12])).
% 22.00/14.32  tff(c_1473, plain, (![B_347]: (k7_relat_1('#skF_6', B_347)=k1_xboole_0 | ~r1_xboole_0(B_347, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_1461])).
% 22.00/14.32  tff(c_1477, plain, (![A_14]: (k7_relat_1('#skF_6', A_14)=k1_xboole_0 | ~r1_subset_1(A_14, '#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(A_14))), inference(resolution, [status(thm)], [c_16, c_1473])).
% 22.00/14.32  tff(c_1489, plain, (![A_349]: (k7_relat_1('#skF_6', A_349)=k1_xboole_0 | ~r1_subset_1(A_349, '#skF_4') | v1_xboole_0(A_349))), inference(negUnitSimplification, [status(thm)], [c_66, c_1477])).
% 22.00/14.32  tff(c_1492, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_62, c_1489])).
% 22.00/14.32  tff(c_1495, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_70, c_1492])).
% 22.00/14.33  tff(c_1576, plain, (![B_360]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_3', B_360))=k3_xboole_0(k1_xboole_0, k7_relat_1('#skF_6', B_360)) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1495, c_1561])).
% 22.00/14.33  tff(c_1587, plain, (![B_360]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_3', B_360))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_110, c_87, c_1576])).
% 22.00/14.33  tff(c_1675, plain, (![D_367]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_367)=k7_relat_1('#skF_6', D_367) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_50, c_1673])).
% 22.00/14.33  tff(c_1680, plain, (![D_367]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_367)=k7_relat_1('#skF_6', D_367))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1675])).
% 22.00/14.33  tff(c_1511, plain, (![A_351, B_352, C_353]: (k9_subset_1(A_351, B_352, C_353)=k3_xboole_0(B_352, C_353) | ~m1_subset_1(C_353, k1_zfmisc_1(A_351)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 22.00/14.33  tff(c_1523, plain, (![B_352]: (k9_subset_1('#skF_1', B_352, '#skF_4')=k3_xboole_0(B_352, '#skF_4'))), inference(resolution, [status(thm)], [c_64, c_1511])).
% 22.00/14.33  tff(c_48, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_230])).
% 22.00/14.33  tff(c_112, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_48])).
% 22.00/14.33  tff(c_1533, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1523, c_1523, c_112])).
% 22.00/14.33  tff(c_2121, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1585, c_1683, c_1587, c_1680, c_1533])).
% 22.00/14.33  tff(c_2122, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_48])).
% 22.00/14.33  tff(c_4300, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_2122])).
% 22.00/14.33  tff(c_123247, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_123236, c_4300])).
% 22.00/14.33  tff(c_123261, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_4142, c_4089, c_2195, c_2195, c_8710, c_123247])).
% 22.00/14.33  tff(c_123263, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_123261])).
% 22.00/14.33  tff(c_123264, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_2122])).
% 22.00/14.33  tff(c_204036, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_204027, c_123264])).
% 22.00/14.33  tff(c_204047, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_4142, c_2195, c_4089, c_2195, c_129512, c_204036])).
% 22.00/14.33  tff(c_204049, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_204047])).
% 22.00/14.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.00/14.33  
% 22.00/14.33  Inference rules
% 22.00/14.33  ----------------------
% 22.00/14.33  #Ref     : 0
% 22.00/14.33  #Sup     : 50740
% 22.00/14.33  #Fact    : 0
% 22.00/14.33  #Define  : 0
% 22.00/14.33  #Split   : 11
% 22.00/14.33  #Chain   : 0
% 22.00/14.33  #Close   : 0
% 22.00/14.33  
% 22.00/14.33  Ordering : KBO
% 22.00/14.33  
% 22.00/14.33  Simplification rules
% 22.00/14.33  ----------------------
% 22.00/14.33  #Subsume      : 16
% 22.00/14.33  #Demod        : 9564
% 22.00/14.33  #Tautology    : 49433
% 22.00/14.33  #SimpNegUnit  : 167
% 22.00/14.33  #BackRed      : 8
% 22.00/14.33  
% 22.00/14.33  #Partial instantiations: 0
% 22.00/14.33  #Strategies tried      : 1
% 22.00/14.33  
% 22.00/14.33  Timing (in seconds)
% 22.00/14.33  ----------------------
% 22.00/14.33  Preprocessing        : 0.45
% 22.00/14.33  Parsing              : 0.23
% 22.00/14.33  CNF conversion       : 0.06
% 22.00/14.33  Main loop            : 13.01
% 22.00/14.33  Inferencing          : 2.46
% 22.00/14.33  Reduction            : 6.83
% 22.00/14.33  Demodulation         : 5.79
% 22.00/14.33  BG Simplification    : 0.16
% 22.00/14.33  Subsumption          : 3.02
% 22.00/14.33  Abstraction          : 0.19
% 22.00/14.33  MUC search           : 0.00
% 22.00/14.33  Cooper               : 0.00
% 22.00/14.33  Total                : 13.53
% 22.00/14.33  Index Insertion      : 0.00
% 22.00/14.33  Index Deletion       : 0.00
% 22.00/14.33  Index Matching       : 0.00
% 22.00/14.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
