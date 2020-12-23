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
% DateTime   : Thu Dec  3 10:26:10 EST 2020

% Result     : Theorem 11.61s
% Output     : CNFRefutation 11.97s
% Verified   : 
% Statistics : Number of formulae       :  358 (1860 expanded)
%              Number of leaves         :   57 ( 662 expanded)
%              Depth                    :   21
%              Number of atoms          :  966 (8465 expanded)
%              Number of equality atoms :  246 (1872 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_266,negated_conjecture,(
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

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_72,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_114,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_136,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_128,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_84,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_142,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_30,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_224,axiom,(
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

tff(f_190,axiom,(
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

tff(c_96,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_266])).

tff(c_90,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_266])).

tff(c_86,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_266])).

tff(c_78,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_266])).

tff(c_4231,plain,(
    ! [C_647,A_648,B_649] :
      ( v1_relat_1(C_647)
      | ~ m1_subset_1(C_647,k1_zfmisc_1(k2_zfmisc_1(A_648,B_649))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4239,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_78,c_4231])).

tff(c_72,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_266])).

tff(c_4238,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_72,c_4231])).

tff(c_3854,plain,(
    ! [C_596,A_597,B_598] :
      ( v1_relat_1(C_596)
      | ~ m1_subset_1(C_596,k1_zfmisc_1(k2_zfmisc_1(A_597,B_598))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3862,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_78,c_3854])).

tff(c_30,plain,(
    ! [A_24] :
      ( k1_relat_1(A_24) != k1_xboole_0
      | k1_xboole_0 = A_24
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3878,plain,
    ( k1_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3862,c_30])).

tff(c_3881,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3878])).

tff(c_24,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3819,plain,(
    ! [A_593] :
      ( k9_relat_1(A_593,k1_relat_1(A_593)) = k2_relat_1(A_593)
      | ~ v1_relat_1(A_593) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3828,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_3819])).

tff(c_3831,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_3828])).

tff(c_3851,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_3831])).

tff(c_44,plain,(
    ! [A_35] :
      ( r1_xboole_0('#skF_1'(A_35),A_35)
      | k1_xboole_0 = A_35 ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_3935,plain,(
    ! [A_614,B_615] :
      ( k7_relat_1(A_614,B_615) = k1_xboole_0
      | ~ r1_xboole_0(B_615,k1_relat_1(A_614))
      | ~ v1_relat_1(A_614) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4100,plain,(
    ! [A_645] :
      ( k7_relat_1(A_645,'#skF_1'(k1_relat_1(A_645))) = k1_xboole_0
      | ~ v1_relat_1(A_645)
      | k1_relat_1(A_645) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_44,c_3935])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( v1_relat_1(k7_relat_1(A_11,B_12))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4121,plain,(
    ! [A_645] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_645)
      | ~ v1_relat_1(A_645)
      | k1_relat_1(A_645) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4100,c_14])).

tff(c_4181,plain,(
    ! [A_646] :
      ( ~ v1_relat_1(A_646)
      | ~ v1_relat_1(A_646)
      | k1_relat_1(A_646) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_3851,c_4121])).

tff(c_4185,plain,
    ( ~ v1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3862,c_4181])).

tff(c_4195,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3862,c_4185])).

tff(c_4197,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3881,c_4195])).

tff(c_4198,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_3878])).

tff(c_4201,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4198,c_3851])).

tff(c_4214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3862,c_4201])).

tff(c_4215,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3831])).

tff(c_92,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_266])).

tff(c_84,plain,(
    r1_subset_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_266])).

tff(c_88,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_266])).

tff(c_36,plain,(
    ! [A_27,B_28] :
      ( r1_xboole_0(A_27,B_28)
      | ~ r1_subset_1(A_27,B_28)
      | v1_xboole_0(B_28)
      | v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_94,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_266])).

tff(c_4276,plain,(
    ! [C_655,A_656,B_657] :
      ( v4_relat_1(C_655,A_656)
      | ~ m1_subset_1(C_655,k1_zfmisc_1(k2_zfmisc_1(A_656,B_657))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_4283,plain,(
    v4_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_4276])).

tff(c_16532,plain,(
    ! [B_1161,A_1162] :
      ( k1_relat_1(B_1161) = A_1162
      | ~ v1_partfun1(B_1161,A_1162)
      | ~ v4_relat_1(B_1161,A_1162)
      | ~ v1_relat_1(B_1161) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_16538,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_4283,c_16532])).

tff(c_16544,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4238,c_16538])).

tff(c_17475,plain,(
    ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_16544])).

tff(c_76,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_266])).

tff(c_74,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_266])).

tff(c_17787,plain,(
    ! [C_1240,A_1241,B_1242] :
      ( v1_partfun1(C_1240,A_1241)
      | ~ v1_funct_2(C_1240,A_1241,B_1242)
      | ~ v1_funct_1(C_1240)
      | ~ m1_subset_1(C_1240,k1_zfmisc_1(k2_zfmisc_1(A_1241,B_1242)))
      | v1_xboole_0(B_1242) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_17790,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_17787])).

tff(c_17796,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_17790])).

tff(c_17798,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_17475,c_17796])).

tff(c_17799,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_16544])).

tff(c_22,plain,(
    ! [A_21,B_23] :
      ( k7_relat_1(A_21,B_23) = k1_xboole_0
      | ~ r1_xboole_0(B_23,k1_relat_1(A_21))
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_17808,plain,(
    ! [B_23] :
      ( k7_relat_1('#skF_7',B_23) = k1_xboole_0
      | ~ r1_xboole_0(B_23,'#skF_5')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17799,c_22])).

tff(c_17830,plain,(
    ! [B_1243] :
      ( k7_relat_1('#skF_7',B_1243) = k1_xboole_0
      | ~ r1_xboole_0(B_1243,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4238,c_17808])).

tff(c_17834,plain,(
    ! [A_27] :
      ( k7_relat_1('#skF_7',A_27) = k1_xboole_0
      | ~ r1_subset_1(A_27,'#skF_5')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_27) ) ),
    inference(resolution,[status(thm)],[c_36,c_17830])).

tff(c_17945,plain,(
    ! [A_1248] :
      ( k7_relat_1('#skF_7',A_1248) = k1_xboole_0
      | ~ r1_subset_1(A_1248,'#skF_5')
      | v1_xboole_0(A_1248) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_17834])).

tff(c_17948,plain,
    ( k7_relat_1('#skF_7','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_17945])).

tff(c_17951,plain,(
    k7_relat_1('#skF_7','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_17948])).

tff(c_32,plain,(
    ! [B_26,A_25] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_26,A_25)),A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_17961,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),'#skF_4')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_17951,c_32])).

tff(c_17972,plain,(
    r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4238,c_26,c_17961])).

tff(c_20,plain,(
    ! [A_16,C_20,B_19] :
      ( k9_relat_1(k7_relat_1(A_16,C_20),B_19) = k9_relat_1(A_16,B_19)
      | ~ r1_tarski(B_19,C_20)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_17955,plain,(
    ! [B_19] :
      ( k9_relat_1(k1_xboole_0,B_19) = k9_relat_1('#skF_7',B_19)
      | ~ r1_tarski(B_19,'#skF_4')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17951,c_20])).

tff(c_18142,plain,(
    ! [B_1261] :
      ( k9_relat_1(k1_xboole_0,B_1261) = k9_relat_1('#skF_7',B_1261)
      | ~ r1_tarski(B_1261,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4238,c_17955])).

tff(c_18153,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_17972,c_18142])).

tff(c_18167,plain,(
    k9_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4215,c_18153])).

tff(c_16435,plain,(
    ! [A_1151,B_1152] :
      ( r1_xboole_0(A_1151,B_1152)
      | ~ r1_subset_1(A_1151,B_1152)
      | v1_xboole_0(B_1152)
      | v1_xboole_0(A_1151) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18615,plain,(
    ! [A_1293,B_1294] :
      ( k3_xboole_0(A_1293,B_1294) = k1_xboole_0
      | ~ r1_subset_1(A_1293,B_1294)
      | v1_xboole_0(B_1294)
      | v1_xboole_0(A_1293) ) ),
    inference(resolution,[status(thm)],[c_16435,c_2])).

tff(c_18624,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_18615])).

tff(c_18629,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_88,c_18624])).

tff(c_82,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_266])).

tff(c_18112,plain,(
    ! [A_1255,B_1256,C_1257,D_1258] :
      ( k2_partfun1(A_1255,B_1256,C_1257,D_1258) = k7_relat_1(C_1257,D_1258)
      | ~ m1_subset_1(C_1257,k1_zfmisc_1(k2_zfmisc_1(A_1255,B_1256)))
      | ~ v1_funct_1(C_1257) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_18116,plain,(
    ! [D_1258] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_6',D_1258) = k7_relat_1('#skF_6',D_1258)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_78,c_18112])).

tff(c_18122,plain,(
    ! [D_1258] : k2_partfun1('#skF_4','#skF_3','#skF_6',D_1258) = k7_relat_1('#skF_6',D_1258) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_18116])).

tff(c_18114,plain,(
    ! [D_1258] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_7',D_1258) = k7_relat_1('#skF_7',D_1258)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_72,c_18112])).

tff(c_18119,plain,(
    ! [D_1258] : k2_partfun1('#skF_5','#skF_3','#skF_7',D_1258) = k7_relat_1('#skF_7',D_1258) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_18114])).

tff(c_16491,plain,(
    ! [A_1155,B_1156,C_1157] :
      ( k9_subset_1(A_1155,B_1156,C_1157) = k3_xboole_0(B_1156,C_1157)
      | ~ m1_subset_1(C_1157,k1_zfmisc_1(A_1155)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16502,plain,(
    ! [B_1156] : k9_subset_1('#skF_2',B_1156,'#skF_5') = k3_xboole_0(B_1156,'#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_16491])).

tff(c_516,plain,(
    ! [C_304,A_305,B_306] :
      ( v1_relat_1(C_304)
      | ~ m1_subset_1(C_304,k1_zfmisc_1(k2_zfmisc_1(A_305,B_306))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_524,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_78,c_516])).

tff(c_163,plain,(
    ! [C_253,A_254,B_255] :
      ( v1_relat_1(C_253)
      | ~ m1_subset_1(C_253,k1_zfmisc_1(k2_zfmisc_1(A_254,B_255))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_171,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_78,c_163])).

tff(c_187,plain,
    ( k1_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_171,c_30])).

tff(c_208,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_187])).

tff(c_149,plain,(
    ! [A_252] :
      ( k9_relat_1(A_252,k1_relat_1(A_252)) = k2_relat_1(A_252)
      | ~ v1_relat_1(A_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_158,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_149])).

tff(c_161,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_158])).

tff(c_162,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_161])).

tff(c_263,plain,(
    ! [A_271,B_272] :
      ( k7_relat_1(A_271,B_272) = k1_xboole_0
      | ~ r1_xboole_0(B_272,k1_relat_1(A_271))
      | ~ v1_relat_1(A_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_429,plain,(
    ! [A_302] :
      ( k7_relat_1(A_302,'#skF_1'(k1_relat_1(A_302))) = k1_xboole_0
      | ~ v1_relat_1(A_302)
      | k1_relat_1(A_302) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_44,c_263])).

tff(c_450,plain,(
    ! [A_302] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_302)
      | ~ v1_relat_1(A_302)
      | k1_relat_1(A_302) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_429,c_14])).

tff(c_467,plain,(
    ! [A_303] :
      ( ~ v1_relat_1(A_303)
      | ~ v1_relat_1(A_303)
      | k1_relat_1(A_303) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_450])).

tff(c_469,plain,
    ( ~ v1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_171,c_467])).

tff(c_476,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_469])).

tff(c_478,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_208,c_476])).

tff(c_479,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_482,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_479,c_162])).

tff(c_495,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_482])).

tff(c_496,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_161])).

tff(c_584,plain,(
    ! [C_314,A_315,B_316] :
      ( v4_relat_1(C_314,A_315)
      | ~ m1_subset_1(C_314,k1_zfmisc_1(k2_zfmisc_1(A_315,B_316))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_592,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_584])).

tff(c_711,plain,(
    ! [B_328,A_329] :
      ( k1_relat_1(B_328) = A_329
      | ~ v1_partfun1(B_328,A_329)
      | ~ v4_relat_1(B_328,A_329)
      | ~ v1_relat_1(B_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_714,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_592,c_711])).

tff(c_720,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_714])).

tff(c_724,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_720])).

tff(c_80,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_266])).

tff(c_1384,plain,(
    ! [C_388,A_389,B_390] :
      ( v1_partfun1(C_388,A_389)
      | ~ v1_funct_2(C_388,A_389,B_390)
      | ~ v1_funct_1(C_388)
      | ~ m1_subset_1(C_388,k1_zfmisc_1(k2_zfmisc_1(A_389,B_390)))
      | v1_xboole_0(B_390) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1390,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_1384])).

tff(c_1397,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_1390])).

tff(c_1399,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_724,c_1397])).

tff(c_1400,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_720])).

tff(c_540,plain,
    ( k1_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_524,c_30])).

tff(c_542,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_540])).

tff(c_1402,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1400,c_542])).

tff(c_1406,plain,(
    ! [B_23] :
      ( k7_relat_1('#skF_6',B_23) = k1_xboole_0
      | ~ r1_xboole_0(B_23,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1400,c_22])).

tff(c_1873,plain,(
    ! [B_426] :
      ( k7_relat_1('#skF_6',B_426) = k1_xboole_0
      | ~ r1_xboole_0(B_426,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_1406])).

tff(c_1885,plain,
    ( k7_relat_1('#skF_6','#skF_1'('#skF_4')) = k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44,c_1873])).

tff(c_1892,plain,(
    k7_relat_1('#skF_6','#skF_1'('#skF_4')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1402,c_1885])).

tff(c_1899,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),'#skF_1'('#skF_4'))
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1892,c_32])).

tff(c_1908,plain,(
    r1_tarski(k1_xboole_0,'#skF_1'('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_26,c_1899])).

tff(c_2023,plain,(
    ! [A_434,C_435,B_436] :
      ( k9_relat_1(k7_relat_1(A_434,C_435),B_436) = k9_relat_1(A_434,B_436)
      | ~ r1_tarski(B_436,C_435)
      | ~ v1_relat_1(A_434) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2042,plain,(
    ! [B_436] :
      ( k9_relat_1(k1_xboole_0,B_436) = k9_relat_1('#skF_6',B_436)
      | ~ r1_tarski(B_436,'#skF_1'('#skF_4'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1892,c_2023])).

tff(c_2352,plain,(
    ! [B_462] :
      ( k9_relat_1(k1_xboole_0,B_462) = k9_relat_1('#skF_6',B_462)
      | ~ r1_tarski(B_462,'#skF_1'('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_2042])).

tff(c_2363,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1908,c_2352])).

tff(c_2377,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_496,c_2363])).

tff(c_18,plain,(
    ! [B_15,A_14] :
      ( k2_relat_1(k7_relat_1(B_15,A_14)) = k9_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_124,plain,(
    ! [A_246] :
      ( k2_relat_1(A_246) != k1_xboole_0
      | k1_xboole_0 = A_246
      | ~ v1_relat_1(A_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2587,plain,(
    ! [A_481,B_482] :
      ( k2_relat_1(k7_relat_1(A_481,B_482)) != k1_xboole_0
      | k7_relat_1(A_481,B_482) = k1_xboole_0
      | ~ v1_relat_1(A_481) ) ),
    inference(resolution,[status(thm)],[c_14,c_124])).

tff(c_2725,plain,(
    ! [B_493,A_494] :
      ( k9_relat_1(B_493,A_494) != k1_xboole_0
      | k7_relat_1(B_493,A_494) = k1_xboole_0
      | ~ v1_relat_1(B_493)
      | ~ v1_relat_1(B_493) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2587])).

tff(c_2727,plain,
    ( k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2377,c_2725])).

tff(c_2754,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_2727])).

tff(c_652,plain,(
    ! [A_322,B_323] :
      ( r1_xboole_0(A_322,B_323)
      | ~ r1_subset_1(A_322,B_323)
      | v1_xboole_0(B_323)
      | v1_xboole_0(A_322) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2438,plain,(
    ! [A_467,B_468] :
      ( k3_xboole_0(A_467,B_468) = k1_xboole_0
      | ~ r1_subset_1(A_467,B_468)
      | v1_xboole_0(B_468)
      | v1_xboole_0(A_467) ) ),
    inference(resolution,[status(thm)],[c_652,c_2])).

tff(c_2441,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_2438])).

tff(c_2444,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_88,c_2441])).

tff(c_2148,plain,(
    ! [A_442,B_443,C_444,D_445] :
      ( k2_partfun1(A_442,B_443,C_444,D_445) = k7_relat_1(C_444,D_445)
      | ~ m1_subset_1(C_444,k1_zfmisc_1(k2_zfmisc_1(A_442,B_443)))
      | ~ v1_funct_1(C_444) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_2152,plain,(
    ! [D_445] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_6',D_445) = k7_relat_1('#skF_6',D_445)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_78,c_2148])).

tff(c_2158,plain,(
    ! [D_445] : k2_partfun1('#skF_4','#skF_3','#skF_6',D_445) = k7_relat_1('#skF_6',D_445) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2152])).

tff(c_2150,plain,(
    ! [D_445] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_7',D_445) = k7_relat_1('#skF_7',D_445)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_72,c_2148])).

tff(c_2155,plain,(
    ! [D_445] : k2_partfun1('#skF_5','#skF_3','#skF_7',D_445) = k7_relat_1('#skF_7',D_445) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2150])).

tff(c_1912,plain,(
    ! [A_427,B_428,C_429] :
      ( k9_subset_1(A_427,B_428,C_429) = k3_xboole_0(B_428,C_429)
      | ~ m1_subset_1(C_429,k1_zfmisc_1(A_427)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1923,plain,(
    ! [B_428] : k9_subset_1('#skF_2',B_428,'#skF_5') = k3_xboole_0(B_428,'#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_1912])).

tff(c_70,plain,
    ( k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') != '#skF_7'
    | k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') != '#skF_6'
    | k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_266])).

tff(c_108,plain,(
    k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_1929,plain,(
    k2_partfun1('#skF_5','#skF_3','#skF_7',k3_xboole_0('#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3','#skF_6',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1923,c_1923,c_108])).

tff(c_2280,plain,(
    k7_relat_1('#skF_7',k3_xboole_0('#skF_4','#skF_5')) != k7_relat_1('#skF_6',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2158,c_2155,c_1929])).

tff(c_2445,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) != k7_relat_1('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2444,c_2444,c_2280])).

tff(c_2826,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2754,c_2445])).

tff(c_523,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_72,c_516])).

tff(c_591,plain,(
    v4_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_584])).

tff(c_717,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_591,c_711])).

tff(c_723,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_523,c_717])).

tff(c_1422,plain,(
    ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_723])).

tff(c_1829,plain,(
    ! [C_423,A_424,B_425] :
      ( v1_partfun1(C_423,A_424)
      | ~ v1_funct_2(C_423,A_424,B_425)
      | ~ v1_funct_1(C_423)
      | ~ m1_subset_1(C_423,k1_zfmisc_1(k2_zfmisc_1(A_424,B_425)))
      | v1_xboole_0(B_425) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1832,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_1829])).

tff(c_1838,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_1832])).

tff(c_1840,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_1422,c_1838])).

tff(c_1841,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_723])).

tff(c_1847,plain,(
    ! [B_23] :
      ( k7_relat_1('#skF_7',B_23) = k1_xboole_0
      | ~ r1_xboole_0(B_23,'#skF_5')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1841,c_22])).

tff(c_1948,plain,(
    ! [B_432] :
      ( k7_relat_1('#skF_7',B_432) = k1_xboole_0
      | ~ r1_xboole_0(B_432,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_523,c_1847])).

tff(c_1952,plain,(
    ! [A_27] :
      ( k7_relat_1('#skF_7',A_27) = k1_xboole_0
      | ~ r1_subset_1(A_27,'#skF_5')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_27) ) ),
    inference(resolution,[status(thm)],[c_36,c_1948])).

tff(c_2241,plain,(
    ! [A_454] :
      ( k7_relat_1('#skF_7',A_454) = k1_xboole_0
      | ~ r1_subset_1(A_454,'#skF_5')
      | v1_xboole_0(A_454) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_1952])).

tff(c_2244,plain,
    ( k7_relat_1('#skF_7','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_2241])).

tff(c_2247,plain,(
    k7_relat_1('#skF_7','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_2244])).

tff(c_2260,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),'#skF_4')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2247,c_32])).

tff(c_2275,plain,(
    r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_523,c_26,c_2260])).

tff(c_2254,plain,(
    ! [B_19] :
      ( k9_relat_1(k1_xboole_0,B_19) = k9_relat_1('#skF_7',B_19)
      | ~ r1_tarski(B_19,'#skF_4')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2247,c_20])).

tff(c_2296,plain,(
    ! [B_455] :
      ( k9_relat_1(k1_xboole_0,B_455) = k9_relat_1('#skF_7',B_455)
      | ~ r1_tarski(B_455,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_523,c_2254])).

tff(c_2299,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2275,c_2296])).

tff(c_2317,plain,(
    k9_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_496,c_2299])).

tff(c_2729,plain,
    ( k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2317,c_2725])).

tff(c_2757,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_523,c_2729])).

tff(c_2877,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2826,c_2757])).

tff(c_2878,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_540])).

tff(c_2879,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_540])).

tff(c_2899,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2878,c_2879])).

tff(c_2979,plain,(
    ! [C_510,A_511,B_512] :
      ( v4_relat_1(C_510,A_511)
      | ~ m1_subset_1(C_510,k1_zfmisc_1(k2_zfmisc_1(A_511,B_512))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2987,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_2979])).

tff(c_3192,plain,(
    ! [B_538,A_539] :
      ( k1_relat_1(B_538) = A_539
      | ~ v1_partfun1(B_538,A_539)
      | ~ v4_relat_1(B_538,A_539)
      | ~ v1_relat_1(B_538) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_3195,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2987,c_3192])).

tff(c_3201,plain,
    ( '#skF_6' = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_2899,c_3195])).

tff(c_3205,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3201])).

tff(c_3727,plain,(
    ! [C_581,A_582,B_583] :
      ( v1_partfun1(C_581,A_582)
      | ~ v1_funct_2(C_581,A_582,B_583)
      | ~ v1_funct_1(C_581)
      | ~ m1_subset_1(C_581,k1_zfmisc_1(k2_zfmisc_1(A_582,B_583)))
      | v1_xboole_0(B_583) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_3733,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_3727])).

tff(c_3740,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_3733])).

tff(c_3742,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_3205,c_3740])).

tff(c_3743,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3201])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_2892,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2878,c_6])).

tff(c_3766,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3743,c_2892])).

tff(c_3773,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_3766])).

tff(c_3775,plain,(
    k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) = k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_16504,plain,(
    k2_partfun1('#skF_5','#skF_3','#skF_7',k3_xboole_0('#skF_4','#skF_5')) = k2_partfun1('#skF_4','#skF_3','#skF_6',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16502,c_16502,c_3775])).

tff(c_18123,plain,(
    k2_partfun1('#skF_4','#skF_3','#skF_6',k3_xboole_0('#skF_4','#skF_5')) = k7_relat_1('#skF_7',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18119,c_16504])).

tff(c_18247,plain,(
    k7_relat_1('#skF_7',k3_xboole_0('#skF_4','#skF_5')) = k7_relat_1('#skF_6',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18122,c_18123])).

tff(c_18632,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k7_relat_1('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18629,c_18629,c_18247])).

tff(c_18671,plain,
    ( k2_relat_1(k7_relat_1('#skF_6',k1_xboole_0)) = k9_relat_1('#skF_7',k1_xboole_0)
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_18632,c_18])).

tff(c_18690,plain,(
    k2_relat_1(k7_relat_1('#skF_6',k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4238,c_18167,c_18671])).

tff(c_3804,plain,(
    ! [A_591] :
      ( k2_relat_1(A_591) != k1_xboole_0
      | k1_xboole_0 = A_591
      | ~ v1_relat_1(A_591) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3808,plain,(
    ! [A_11,B_12] :
      ( k2_relat_1(k7_relat_1(A_11,B_12)) != k1_xboole_0
      | k7_relat_1(A_11,B_12) = k1_xboole_0
      | ~ v1_relat_1(A_11) ) ),
    inference(resolution,[status(thm)],[c_14,c_3804])).

tff(c_18699,plain,
    ( k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_18690,c_3808])).

tff(c_18713,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4239,c_18699])).

tff(c_18721,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18713,c_18632])).

tff(c_18364,plain,(
    ! [A_1269,D_1270,C_1271,F_1268,B_1273,E_1272] :
      ( v1_funct_1(k1_tmap_1(A_1269,B_1273,C_1271,D_1270,E_1272,F_1268))
      | ~ m1_subset_1(F_1268,k1_zfmisc_1(k2_zfmisc_1(D_1270,B_1273)))
      | ~ v1_funct_2(F_1268,D_1270,B_1273)
      | ~ v1_funct_1(F_1268)
      | ~ m1_subset_1(E_1272,k1_zfmisc_1(k2_zfmisc_1(C_1271,B_1273)))
      | ~ v1_funct_2(E_1272,C_1271,B_1273)
      | ~ v1_funct_1(E_1272)
      | ~ m1_subset_1(D_1270,k1_zfmisc_1(A_1269))
      | v1_xboole_0(D_1270)
      | ~ m1_subset_1(C_1271,k1_zfmisc_1(A_1269))
      | v1_xboole_0(C_1271)
      | v1_xboole_0(B_1273)
      | v1_xboole_0(A_1269) ) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_18366,plain,(
    ! [A_1269,C_1271,E_1272] :
      ( v1_funct_1(k1_tmap_1(A_1269,'#skF_3',C_1271,'#skF_5',E_1272,'#skF_7'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_1272,k1_zfmisc_1(k2_zfmisc_1(C_1271,'#skF_3')))
      | ~ v1_funct_2(E_1272,C_1271,'#skF_3')
      | ~ v1_funct_1(E_1272)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1269))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1271,k1_zfmisc_1(A_1269))
      | v1_xboole_0(C_1271)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1269) ) ),
    inference(resolution,[status(thm)],[c_72,c_18364])).

tff(c_18371,plain,(
    ! [A_1269,C_1271,E_1272] :
      ( v1_funct_1(k1_tmap_1(A_1269,'#skF_3',C_1271,'#skF_5',E_1272,'#skF_7'))
      | ~ m1_subset_1(E_1272,k1_zfmisc_1(k2_zfmisc_1(C_1271,'#skF_3')))
      | ~ v1_funct_2(E_1272,C_1271,'#skF_3')
      | ~ v1_funct_1(E_1272)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1269))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1271,k1_zfmisc_1(A_1269))
      | v1_xboole_0(C_1271)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1269) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_18366])).

tff(c_18380,plain,(
    ! [A_1274,C_1275,E_1276] :
      ( v1_funct_1(k1_tmap_1(A_1274,'#skF_3',C_1275,'#skF_5',E_1276,'#skF_7'))
      | ~ m1_subset_1(E_1276,k1_zfmisc_1(k2_zfmisc_1(C_1275,'#skF_3')))
      | ~ v1_funct_2(E_1276,C_1275,'#skF_3')
      | ~ v1_funct_1(E_1276)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1274))
      | ~ m1_subset_1(C_1275,k1_zfmisc_1(A_1274))
      | v1_xboole_0(C_1275)
      | v1_xboole_0(A_1274) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_88,c_18371])).

tff(c_18384,plain,(
    ! [A_1274] :
      ( v1_funct_1(k1_tmap_1(A_1274,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1274))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1274))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1274) ) ),
    inference(resolution,[status(thm)],[c_78,c_18380])).

tff(c_18391,plain,(
    ! [A_1274] :
      ( v1_funct_1(k1_tmap_1(A_1274,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1274))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1274))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1274) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_18384])).

tff(c_18919,plain,(
    ! [A_1310] :
      ( v1_funct_1(k1_tmap_1(A_1310,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1310))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1310))
      | v1_xboole_0(A_1310) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_18391])).

tff(c_18922,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_86,c_18919])).

tff(c_18925,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_18922])).

tff(c_18926,plain,(
    v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_18925])).

tff(c_66,plain,(
    ! [C_176,A_174,D_177,E_178,B_175,F_179] :
      ( v1_funct_2(k1_tmap_1(A_174,B_175,C_176,D_177,E_178,F_179),k4_subset_1(A_174,C_176,D_177),B_175)
      | ~ m1_subset_1(F_179,k1_zfmisc_1(k2_zfmisc_1(D_177,B_175)))
      | ~ v1_funct_2(F_179,D_177,B_175)
      | ~ v1_funct_1(F_179)
      | ~ m1_subset_1(E_178,k1_zfmisc_1(k2_zfmisc_1(C_176,B_175)))
      | ~ v1_funct_2(E_178,C_176,B_175)
      | ~ v1_funct_1(E_178)
      | ~ m1_subset_1(D_177,k1_zfmisc_1(A_174))
      | v1_xboole_0(D_177)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(A_174))
      | v1_xboole_0(C_176)
      | v1_xboole_0(B_175)
      | v1_xboole_0(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_64,plain,(
    ! [C_176,A_174,D_177,E_178,B_175,F_179] :
      ( m1_subset_1(k1_tmap_1(A_174,B_175,C_176,D_177,E_178,F_179),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_174,C_176,D_177),B_175)))
      | ~ m1_subset_1(F_179,k1_zfmisc_1(k2_zfmisc_1(D_177,B_175)))
      | ~ v1_funct_2(F_179,D_177,B_175)
      | ~ v1_funct_1(F_179)
      | ~ m1_subset_1(E_178,k1_zfmisc_1(k2_zfmisc_1(C_176,B_175)))
      | ~ v1_funct_2(E_178,C_176,B_175)
      | ~ v1_funct_1(E_178)
      | ~ m1_subset_1(D_177,k1_zfmisc_1(A_174))
      | v1_xboole_0(D_177)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(A_174))
      | v1_xboole_0(C_176)
      | v1_xboole_0(B_175)
      | v1_xboole_0(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_18855,plain,(
    ! [F_1303,C_1304,E_1307,B_1305,D_1306,A_1302] :
      ( k2_partfun1(k4_subset_1(A_1302,C_1304,D_1306),B_1305,k1_tmap_1(A_1302,B_1305,C_1304,D_1306,E_1307,F_1303),C_1304) = E_1307
      | ~ m1_subset_1(k1_tmap_1(A_1302,B_1305,C_1304,D_1306,E_1307,F_1303),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1302,C_1304,D_1306),B_1305)))
      | ~ v1_funct_2(k1_tmap_1(A_1302,B_1305,C_1304,D_1306,E_1307,F_1303),k4_subset_1(A_1302,C_1304,D_1306),B_1305)
      | ~ v1_funct_1(k1_tmap_1(A_1302,B_1305,C_1304,D_1306,E_1307,F_1303))
      | k2_partfun1(D_1306,B_1305,F_1303,k9_subset_1(A_1302,C_1304,D_1306)) != k2_partfun1(C_1304,B_1305,E_1307,k9_subset_1(A_1302,C_1304,D_1306))
      | ~ m1_subset_1(F_1303,k1_zfmisc_1(k2_zfmisc_1(D_1306,B_1305)))
      | ~ v1_funct_2(F_1303,D_1306,B_1305)
      | ~ v1_funct_1(F_1303)
      | ~ m1_subset_1(E_1307,k1_zfmisc_1(k2_zfmisc_1(C_1304,B_1305)))
      | ~ v1_funct_2(E_1307,C_1304,B_1305)
      | ~ v1_funct_1(E_1307)
      | ~ m1_subset_1(D_1306,k1_zfmisc_1(A_1302))
      | v1_xboole_0(D_1306)
      | ~ m1_subset_1(C_1304,k1_zfmisc_1(A_1302))
      | v1_xboole_0(C_1304)
      | v1_xboole_0(B_1305)
      | v1_xboole_0(A_1302) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_22022,plain,(
    ! [E_1456,A_1453,F_1452,B_1457,C_1455,D_1454] :
      ( k2_partfun1(k4_subset_1(A_1453,C_1455,D_1454),B_1457,k1_tmap_1(A_1453,B_1457,C_1455,D_1454,E_1456,F_1452),C_1455) = E_1456
      | ~ v1_funct_2(k1_tmap_1(A_1453,B_1457,C_1455,D_1454,E_1456,F_1452),k4_subset_1(A_1453,C_1455,D_1454),B_1457)
      | ~ v1_funct_1(k1_tmap_1(A_1453,B_1457,C_1455,D_1454,E_1456,F_1452))
      | k2_partfun1(D_1454,B_1457,F_1452,k9_subset_1(A_1453,C_1455,D_1454)) != k2_partfun1(C_1455,B_1457,E_1456,k9_subset_1(A_1453,C_1455,D_1454))
      | ~ m1_subset_1(F_1452,k1_zfmisc_1(k2_zfmisc_1(D_1454,B_1457)))
      | ~ v1_funct_2(F_1452,D_1454,B_1457)
      | ~ v1_funct_1(F_1452)
      | ~ m1_subset_1(E_1456,k1_zfmisc_1(k2_zfmisc_1(C_1455,B_1457)))
      | ~ v1_funct_2(E_1456,C_1455,B_1457)
      | ~ v1_funct_1(E_1456)
      | ~ m1_subset_1(D_1454,k1_zfmisc_1(A_1453))
      | v1_xboole_0(D_1454)
      | ~ m1_subset_1(C_1455,k1_zfmisc_1(A_1453))
      | v1_xboole_0(C_1455)
      | v1_xboole_0(B_1457)
      | v1_xboole_0(A_1453) ) ),
    inference(resolution,[status(thm)],[c_64,c_18855])).

tff(c_24821,plain,(
    ! [C_1533,F_1530,A_1531,D_1532,B_1535,E_1534] :
      ( k2_partfun1(k4_subset_1(A_1531,C_1533,D_1532),B_1535,k1_tmap_1(A_1531,B_1535,C_1533,D_1532,E_1534,F_1530),C_1533) = E_1534
      | ~ v1_funct_1(k1_tmap_1(A_1531,B_1535,C_1533,D_1532,E_1534,F_1530))
      | k2_partfun1(D_1532,B_1535,F_1530,k9_subset_1(A_1531,C_1533,D_1532)) != k2_partfun1(C_1533,B_1535,E_1534,k9_subset_1(A_1531,C_1533,D_1532))
      | ~ m1_subset_1(F_1530,k1_zfmisc_1(k2_zfmisc_1(D_1532,B_1535)))
      | ~ v1_funct_2(F_1530,D_1532,B_1535)
      | ~ v1_funct_1(F_1530)
      | ~ m1_subset_1(E_1534,k1_zfmisc_1(k2_zfmisc_1(C_1533,B_1535)))
      | ~ v1_funct_2(E_1534,C_1533,B_1535)
      | ~ v1_funct_1(E_1534)
      | ~ m1_subset_1(D_1532,k1_zfmisc_1(A_1531))
      | v1_xboole_0(D_1532)
      | ~ m1_subset_1(C_1533,k1_zfmisc_1(A_1531))
      | v1_xboole_0(C_1533)
      | v1_xboole_0(B_1535)
      | v1_xboole_0(A_1531) ) ),
    inference(resolution,[status(thm)],[c_66,c_22022])).

tff(c_24825,plain,(
    ! [A_1531,C_1533,E_1534] :
      ( k2_partfun1(k4_subset_1(A_1531,C_1533,'#skF_5'),'#skF_3',k1_tmap_1(A_1531,'#skF_3',C_1533,'#skF_5',E_1534,'#skF_7'),C_1533) = E_1534
      | ~ v1_funct_1(k1_tmap_1(A_1531,'#skF_3',C_1533,'#skF_5',E_1534,'#skF_7'))
      | k2_partfun1(C_1533,'#skF_3',E_1534,k9_subset_1(A_1531,C_1533,'#skF_5')) != k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1(A_1531,C_1533,'#skF_5'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_1534,k1_zfmisc_1(k2_zfmisc_1(C_1533,'#skF_3')))
      | ~ v1_funct_2(E_1534,C_1533,'#skF_3')
      | ~ v1_funct_1(E_1534)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1531))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1533,k1_zfmisc_1(A_1531))
      | v1_xboole_0(C_1533)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1531) ) ),
    inference(resolution,[status(thm)],[c_72,c_24821])).

tff(c_24831,plain,(
    ! [A_1531,C_1533,E_1534] :
      ( k2_partfun1(k4_subset_1(A_1531,C_1533,'#skF_5'),'#skF_3',k1_tmap_1(A_1531,'#skF_3',C_1533,'#skF_5',E_1534,'#skF_7'),C_1533) = E_1534
      | ~ v1_funct_1(k1_tmap_1(A_1531,'#skF_3',C_1533,'#skF_5',E_1534,'#skF_7'))
      | k2_partfun1(C_1533,'#skF_3',E_1534,k9_subset_1(A_1531,C_1533,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_1531,C_1533,'#skF_5'))
      | ~ m1_subset_1(E_1534,k1_zfmisc_1(k2_zfmisc_1(C_1533,'#skF_3')))
      | ~ v1_funct_2(E_1534,C_1533,'#skF_3')
      | ~ v1_funct_1(E_1534)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1531))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1533,k1_zfmisc_1(A_1531))
      | v1_xboole_0(C_1533)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1531) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_18119,c_24825])).

tff(c_24923,plain,(
    ! [A_1538,C_1539,E_1540] :
      ( k2_partfun1(k4_subset_1(A_1538,C_1539,'#skF_5'),'#skF_3',k1_tmap_1(A_1538,'#skF_3',C_1539,'#skF_5',E_1540,'#skF_7'),C_1539) = E_1540
      | ~ v1_funct_1(k1_tmap_1(A_1538,'#skF_3',C_1539,'#skF_5',E_1540,'#skF_7'))
      | k2_partfun1(C_1539,'#skF_3',E_1540,k9_subset_1(A_1538,C_1539,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_1538,C_1539,'#skF_5'))
      | ~ m1_subset_1(E_1540,k1_zfmisc_1(k2_zfmisc_1(C_1539,'#skF_3')))
      | ~ v1_funct_2(E_1540,C_1539,'#skF_3')
      | ~ v1_funct_1(E_1540)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1538))
      | ~ m1_subset_1(C_1539,k1_zfmisc_1(A_1538))
      | v1_xboole_0(C_1539)
      | v1_xboole_0(A_1538) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_88,c_24831])).

tff(c_24930,plain,(
    ! [A_1538] :
      ( k2_partfun1(k4_subset_1(A_1538,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_1538,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1538,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1(A_1538,'#skF_4','#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_1538,'#skF_4','#skF_5'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1538))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1538))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1538) ) ),
    inference(resolution,[status(thm)],[c_78,c_24923])).

tff(c_24940,plain,(
    ! [A_1538] :
      ( k2_partfun1(k4_subset_1(A_1538,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_1538,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1538,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_1538,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_1538,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1538))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1538))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1538) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_18122,c_24930])).

tff(c_26211,plain,(
    ! [A_1563] :
      ( k2_partfun1(k4_subset_1(A_1563,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_1563,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1563,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_1563,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_1563,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1563))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1563))
      | v1_xboole_0(A_1563) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_24940])).

tff(c_4413,plain,(
    ! [B_671,A_672] :
      ( k1_relat_1(B_671) = A_672
      | ~ v1_partfun1(B_671,A_672)
      | ~ v4_relat_1(B_671,A_672)
      | ~ v1_relat_1(B_671) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_4419,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_4283,c_4413])).

tff(c_4425,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4238,c_4419])).

tff(c_5265,plain,(
    ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_4425])).

tff(c_5692,plain,(
    ! [C_763,A_764,B_765] :
      ( v1_partfun1(C_763,A_764)
      | ~ v1_funct_2(C_763,A_764,B_765)
      | ~ v1_funct_1(C_763)
      | ~ m1_subset_1(C_763,k1_zfmisc_1(k2_zfmisc_1(A_764,B_765)))
      | v1_xboole_0(B_765) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_5695,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_5692])).

tff(c_5701,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_5695])).

tff(c_5703,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_5265,c_5701])).

tff(c_5704,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_4425])).

tff(c_5713,plain,(
    ! [B_23] :
      ( k7_relat_1('#skF_7',B_23) = k1_xboole_0
      | ~ r1_xboole_0(B_23,'#skF_5')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5704,c_22])).

tff(c_5811,plain,(
    ! [B_772] :
      ( k7_relat_1('#skF_7',B_772) = k1_xboole_0
      | ~ r1_xboole_0(B_772,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4238,c_5713])).

tff(c_5815,plain,(
    ! [A_27] :
      ( k7_relat_1('#skF_7',A_27) = k1_xboole_0
      | ~ r1_subset_1(A_27,'#skF_5')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_27) ) ),
    inference(resolution,[status(thm)],[c_36,c_5811])).

tff(c_6104,plain,(
    ! [A_794] :
      ( k7_relat_1('#skF_7',A_794) = k1_xboole_0
      | ~ r1_subset_1(A_794,'#skF_5')
      | v1_xboole_0(A_794) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_5815])).

tff(c_6107,plain,
    ( k7_relat_1('#skF_7','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_6104])).

tff(c_6110,plain,(
    k7_relat_1('#skF_7','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_6107])).

tff(c_6123,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),'#skF_4')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_6110,c_32])).

tff(c_6138,plain,(
    r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4238,c_26,c_6123])).

tff(c_6117,plain,(
    ! [B_19] :
      ( k9_relat_1(k1_xboole_0,B_19) = k9_relat_1('#skF_7',B_19)
      | ~ r1_tarski(B_19,'#skF_4')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6110,c_20])).

tff(c_6198,plain,(
    ! [B_795] :
      ( k9_relat_1(k1_xboole_0,B_795) = k9_relat_1('#skF_7',B_795)
      | ~ r1_tarski(B_795,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4238,c_6117])).

tff(c_6201,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6138,c_6198])).

tff(c_6219,plain,(
    k9_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4215,c_6201])).

tff(c_4357,plain,(
    ! [A_667,B_668] :
      ( r1_xboole_0(A_667,B_668)
      | ~ r1_subset_1(A_667,B_668)
      | v1_xboole_0(B_668)
      | v1_xboole_0(A_667) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_6358,plain,(
    ! [A_815,B_816] :
      ( k3_xboole_0(A_815,B_816) = k1_xboole_0
      | ~ r1_subset_1(A_815,B_816)
      | v1_xboole_0(B_816)
      | v1_xboole_0(A_815) ) ),
    inference(resolution,[status(thm)],[c_4357,c_2])).

tff(c_6364,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_6358])).

tff(c_6368,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_88,c_6364])).

tff(c_6011,plain,(
    ! [A_782,B_783,C_784,D_785] :
      ( k2_partfun1(A_782,B_783,C_784,D_785) = k7_relat_1(C_784,D_785)
      | ~ m1_subset_1(C_784,k1_zfmisc_1(k2_zfmisc_1(A_782,B_783)))
      | ~ v1_funct_1(C_784) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_6015,plain,(
    ! [D_785] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_6',D_785) = k7_relat_1('#skF_6',D_785)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_78,c_6011])).

tff(c_6021,plain,(
    ! [D_785] : k2_partfun1('#skF_4','#skF_3','#skF_6',D_785) = k7_relat_1('#skF_6',D_785) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_6015])).

tff(c_6013,plain,(
    ! [D_785] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_7',D_785) = k7_relat_1('#skF_7',D_785)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_72,c_6011])).

tff(c_6018,plain,(
    ! [D_785] : k2_partfun1('#skF_5','#skF_3','#skF_7',D_785) = k7_relat_1('#skF_7',D_785) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_6013])).

tff(c_5775,plain,(
    ! [A_767,B_768,C_769] :
      ( k9_subset_1(A_767,B_768,C_769) = k3_xboole_0(B_768,C_769)
      | ~ m1_subset_1(C_769,k1_zfmisc_1(A_767)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_5786,plain,(
    ! [B_768] : k9_subset_1('#skF_2',B_768,'#skF_5') = k3_xboole_0(B_768,'#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_5775])).

tff(c_5792,plain,(
    k2_partfun1('#skF_5','#skF_3','#skF_7',k3_xboole_0('#skF_4','#skF_5')) = k2_partfun1('#skF_4','#skF_3','#skF_6',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5786,c_5786,c_3775])).

tff(c_6143,plain,(
    k7_relat_1('#skF_7',k3_xboole_0('#skF_4','#skF_5')) = k7_relat_1('#skF_6',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6021,c_6018,c_5792])).

tff(c_6371,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k7_relat_1('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6368,c_6368,c_6143])).

tff(c_6404,plain,
    ( k2_relat_1(k7_relat_1('#skF_6',k1_xboole_0)) = k9_relat_1('#skF_7',k1_xboole_0)
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_6371,c_18])).

tff(c_6419,plain,(
    k2_relat_1(k7_relat_1('#skF_6',k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4238,c_6219,c_6404])).

tff(c_6159,plain,
    ( v1_relat_1(k7_relat_1('#skF_6',k3_xboole_0('#skF_4','#skF_5')))
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_6143,c_14])).

tff(c_6172,plain,(
    v1_relat_1(k7_relat_1('#skF_6',k3_xboole_0('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4238,c_6159])).

tff(c_6370,plain,(
    v1_relat_1(k7_relat_1('#skF_6',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6368,c_6172])).

tff(c_28,plain,(
    ! [A_24] :
      ( k2_relat_1(A_24) != k1_xboole_0
      | k1_xboole_0 = A_24
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6392,plain,
    ( k2_relat_1(k7_relat_1('#skF_6',k1_xboole_0)) != k1_xboole_0
    | k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6370,c_28])).

tff(c_6504,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6419,c_6392])).

tff(c_6393,plain,
    ( k1_relat_1(k7_relat_1('#skF_6',k1_xboole_0)) != k1_xboole_0
    | k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6370,c_30])).

tff(c_6493,plain,(
    k1_relat_1(k7_relat_1('#skF_6',k1_xboole_0)) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_6393])).

tff(c_6505,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6504,c_6493])).

tff(c_6512,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_6505])).

tff(c_6513,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_6393])).

tff(c_6517,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6513,c_6371])).

tff(c_6240,plain,(
    ! [D_798,E_800,F_796,B_801,A_797,C_799] :
      ( v1_funct_1(k1_tmap_1(A_797,B_801,C_799,D_798,E_800,F_796))
      | ~ m1_subset_1(F_796,k1_zfmisc_1(k2_zfmisc_1(D_798,B_801)))
      | ~ v1_funct_2(F_796,D_798,B_801)
      | ~ v1_funct_1(F_796)
      | ~ m1_subset_1(E_800,k1_zfmisc_1(k2_zfmisc_1(C_799,B_801)))
      | ~ v1_funct_2(E_800,C_799,B_801)
      | ~ v1_funct_1(E_800)
      | ~ m1_subset_1(D_798,k1_zfmisc_1(A_797))
      | v1_xboole_0(D_798)
      | ~ m1_subset_1(C_799,k1_zfmisc_1(A_797))
      | v1_xboole_0(C_799)
      | v1_xboole_0(B_801)
      | v1_xboole_0(A_797) ) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_6242,plain,(
    ! [A_797,C_799,E_800] :
      ( v1_funct_1(k1_tmap_1(A_797,'#skF_3',C_799,'#skF_5',E_800,'#skF_7'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_800,k1_zfmisc_1(k2_zfmisc_1(C_799,'#skF_3')))
      | ~ v1_funct_2(E_800,C_799,'#skF_3')
      | ~ v1_funct_1(E_800)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_797))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_799,k1_zfmisc_1(A_797))
      | v1_xboole_0(C_799)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_797) ) ),
    inference(resolution,[status(thm)],[c_72,c_6240])).

tff(c_6247,plain,(
    ! [A_797,C_799,E_800] :
      ( v1_funct_1(k1_tmap_1(A_797,'#skF_3',C_799,'#skF_5',E_800,'#skF_7'))
      | ~ m1_subset_1(E_800,k1_zfmisc_1(k2_zfmisc_1(C_799,'#skF_3')))
      | ~ v1_funct_2(E_800,C_799,'#skF_3')
      | ~ v1_funct_1(E_800)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_797))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_799,k1_zfmisc_1(A_797))
      | v1_xboole_0(C_799)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_797) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_6242])).

tff(c_6287,plain,(
    ! [A_803,C_804,E_805] :
      ( v1_funct_1(k1_tmap_1(A_803,'#skF_3',C_804,'#skF_5',E_805,'#skF_7'))
      | ~ m1_subset_1(E_805,k1_zfmisc_1(k2_zfmisc_1(C_804,'#skF_3')))
      | ~ v1_funct_2(E_805,C_804,'#skF_3')
      | ~ v1_funct_1(E_805)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_803))
      | ~ m1_subset_1(C_804,k1_zfmisc_1(A_803))
      | v1_xboole_0(C_804)
      | v1_xboole_0(A_803) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_88,c_6247])).

tff(c_6291,plain,(
    ! [A_803] :
      ( v1_funct_1(k1_tmap_1(A_803,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_803))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_803))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_803) ) ),
    inference(resolution,[status(thm)],[c_78,c_6287])).

tff(c_6298,plain,(
    ! [A_803] :
      ( v1_funct_1(k1_tmap_1(A_803,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_803))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_803))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_803) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_6291])).

tff(c_6485,plain,(
    ! [A_824] :
      ( v1_funct_1(k1_tmap_1(A_824,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_824))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_824))
      | v1_xboole_0(A_824) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_6298])).

tff(c_6488,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_86,c_6485])).

tff(c_6491,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_6488])).

tff(c_6492,plain,(
    v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_6491])).

tff(c_6636,plain,(
    ! [A_835,F_836,E_840,B_838,C_837,D_839] :
      ( k2_partfun1(k4_subset_1(A_835,C_837,D_839),B_838,k1_tmap_1(A_835,B_838,C_837,D_839,E_840,F_836),D_839) = F_836
      | ~ m1_subset_1(k1_tmap_1(A_835,B_838,C_837,D_839,E_840,F_836),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_835,C_837,D_839),B_838)))
      | ~ v1_funct_2(k1_tmap_1(A_835,B_838,C_837,D_839,E_840,F_836),k4_subset_1(A_835,C_837,D_839),B_838)
      | ~ v1_funct_1(k1_tmap_1(A_835,B_838,C_837,D_839,E_840,F_836))
      | k2_partfun1(D_839,B_838,F_836,k9_subset_1(A_835,C_837,D_839)) != k2_partfun1(C_837,B_838,E_840,k9_subset_1(A_835,C_837,D_839))
      | ~ m1_subset_1(F_836,k1_zfmisc_1(k2_zfmisc_1(D_839,B_838)))
      | ~ v1_funct_2(F_836,D_839,B_838)
      | ~ v1_funct_1(F_836)
      | ~ m1_subset_1(E_840,k1_zfmisc_1(k2_zfmisc_1(C_837,B_838)))
      | ~ v1_funct_2(E_840,C_837,B_838)
      | ~ v1_funct_1(E_840)
      | ~ m1_subset_1(D_839,k1_zfmisc_1(A_835))
      | v1_xboole_0(D_839)
      | ~ m1_subset_1(C_837,k1_zfmisc_1(A_835))
      | v1_xboole_0(C_837)
      | v1_xboole_0(B_838)
      | v1_xboole_0(A_835) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_10044,plain,(
    ! [D_991,F_989,C_992,B_994,A_990,E_993] :
      ( k2_partfun1(k4_subset_1(A_990,C_992,D_991),B_994,k1_tmap_1(A_990,B_994,C_992,D_991,E_993,F_989),D_991) = F_989
      | ~ v1_funct_2(k1_tmap_1(A_990,B_994,C_992,D_991,E_993,F_989),k4_subset_1(A_990,C_992,D_991),B_994)
      | ~ v1_funct_1(k1_tmap_1(A_990,B_994,C_992,D_991,E_993,F_989))
      | k2_partfun1(D_991,B_994,F_989,k9_subset_1(A_990,C_992,D_991)) != k2_partfun1(C_992,B_994,E_993,k9_subset_1(A_990,C_992,D_991))
      | ~ m1_subset_1(F_989,k1_zfmisc_1(k2_zfmisc_1(D_991,B_994)))
      | ~ v1_funct_2(F_989,D_991,B_994)
      | ~ v1_funct_1(F_989)
      | ~ m1_subset_1(E_993,k1_zfmisc_1(k2_zfmisc_1(C_992,B_994)))
      | ~ v1_funct_2(E_993,C_992,B_994)
      | ~ v1_funct_1(E_993)
      | ~ m1_subset_1(D_991,k1_zfmisc_1(A_990))
      | v1_xboole_0(D_991)
      | ~ m1_subset_1(C_992,k1_zfmisc_1(A_990))
      | v1_xboole_0(C_992)
      | v1_xboole_0(B_994)
      | v1_xboole_0(A_990) ) ),
    inference(resolution,[status(thm)],[c_64,c_6636])).

tff(c_12754,plain,(
    ! [A_1064,C_1066,F_1063,B_1068,E_1067,D_1065] :
      ( k2_partfun1(k4_subset_1(A_1064,C_1066,D_1065),B_1068,k1_tmap_1(A_1064,B_1068,C_1066,D_1065,E_1067,F_1063),D_1065) = F_1063
      | ~ v1_funct_1(k1_tmap_1(A_1064,B_1068,C_1066,D_1065,E_1067,F_1063))
      | k2_partfun1(D_1065,B_1068,F_1063,k9_subset_1(A_1064,C_1066,D_1065)) != k2_partfun1(C_1066,B_1068,E_1067,k9_subset_1(A_1064,C_1066,D_1065))
      | ~ m1_subset_1(F_1063,k1_zfmisc_1(k2_zfmisc_1(D_1065,B_1068)))
      | ~ v1_funct_2(F_1063,D_1065,B_1068)
      | ~ v1_funct_1(F_1063)
      | ~ m1_subset_1(E_1067,k1_zfmisc_1(k2_zfmisc_1(C_1066,B_1068)))
      | ~ v1_funct_2(E_1067,C_1066,B_1068)
      | ~ v1_funct_1(E_1067)
      | ~ m1_subset_1(D_1065,k1_zfmisc_1(A_1064))
      | v1_xboole_0(D_1065)
      | ~ m1_subset_1(C_1066,k1_zfmisc_1(A_1064))
      | v1_xboole_0(C_1066)
      | v1_xboole_0(B_1068)
      | v1_xboole_0(A_1064) ) ),
    inference(resolution,[status(thm)],[c_66,c_10044])).

tff(c_12758,plain,(
    ! [A_1064,C_1066,E_1067] :
      ( k2_partfun1(k4_subset_1(A_1064,C_1066,'#skF_5'),'#skF_3',k1_tmap_1(A_1064,'#skF_3',C_1066,'#skF_5',E_1067,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1064,'#skF_3',C_1066,'#skF_5',E_1067,'#skF_7'))
      | k2_partfun1(C_1066,'#skF_3',E_1067,k9_subset_1(A_1064,C_1066,'#skF_5')) != k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1(A_1064,C_1066,'#skF_5'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_1067,k1_zfmisc_1(k2_zfmisc_1(C_1066,'#skF_3')))
      | ~ v1_funct_2(E_1067,C_1066,'#skF_3')
      | ~ v1_funct_1(E_1067)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1064))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1066,k1_zfmisc_1(A_1064))
      | v1_xboole_0(C_1066)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1064) ) ),
    inference(resolution,[status(thm)],[c_72,c_12754])).

tff(c_12764,plain,(
    ! [A_1064,C_1066,E_1067] :
      ( k2_partfun1(k4_subset_1(A_1064,C_1066,'#skF_5'),'#skF_3',k1_tmap_1(A_1064,'#skF_3',C_1066,'#skF_5',E_1067,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1064,'#skF_3',C_1066,'#skF_5',E_1067,'#skF_7'))
      | k2_partfun1(C_1066,'#skF_3',E_1067,k9_subset_1(A_1064,C_1066,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_1064,C_1066,'#skF_5'))
      | ~ m1_subset_1(E_1067,k1_zfmisc_1(k2_zfmisc_1(C_1066,'#skF_3')))
      | ~ v1_funct_2(E_1067,C_1066,'#skF_3')
      | ~ v1_funct_1(E_1067)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1064))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1066,k1_zfmisc_1(A_1064))
      | v1_xboole_0(C_1066)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1064) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_6018,c_12758])).

tff(c_14448,plain,(
    ! [A_1115,C_1116,E_1117] :
      ( k2_partfun1(k4_subset_1(A_1115,C_1116,'#skF_5'),'#skF_3',k1_tmap_1(A_1115,'#skF_3',C_1116,'#skF_5',E_1117,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1115,'#skF_3',C_1116,'#skF_5',E_1117,'#skF_7'))
      | k2_partfun1(C_1116,'#skF_3',E_1117,k9_subset_1(A_1115,C_1116,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_1115,C_1116,'#skF_5'))
      | ~ m1_subset_1(E_1117,k1_zfmisc_1(k2_zfmisc_1(C_1116,'#skF_3')))
      | ~ v1_funct_2(E_1117,C_1116,'#skF_3')
      | ~ v1_funct_1(E_1117)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1115))
      | ~ m1_subset_1(C_1116,k1_zfmisc_1(A_1115))
      | v1_xboole_0(C_1116)
      | v1_xboole_0(A_1115) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_88,c_12764])).

tff(c_14455,plain,(
    ! [A_1115] :
      ( k2_partfun1(k4_subset_1(A_1115,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_1115,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1115,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1(A_1115,'#skF_4','#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_1115,'#skF_4','#skF_5'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1115))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1115))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1115) ) ),
    inference(resolution,[status(thm)],[c_78,c_14448])).

tff(c_14465,plain,(
    ! [A_1115] :
      ( k2_partfun1(k4_subset_1(A_1115,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_1115,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1115,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_1115,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_1115,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1115))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1115))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_6021,c_14455])).

tff(c_16343,plain,(
    ! [A_1143] :
      ( k2_partfun1(k4_subset_1(A_1143,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_1143,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1143,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_1143,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_1143,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1143))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1143))
      | v1_xboole_0(A_1143) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_14465])).

tff(c_3774,plain,
    ( k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_4294,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_3774])).

tff(c_16354,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_16343,c_4294])).

tff(c_16368,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_6513,c_6368,c_5786,c_6517,c_6368,c_5786,c_6492,c_16354])).

tff(c_16370,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_16368])).

tff(c_16371,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_3774])).

tff(c_26220,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_26211,c_16371])).

tff(c_26231,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_18713,c_18629,c_16502,c_18721,c_18629,c_16502,c_18926,c_26220])).

tff(c_26233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_26231])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:47:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.61/4.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.78/4.75  
% 11.78/4.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.78/4.75  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 11.78/4.75  
% 11.78/4.75  %Foreground sorts:
% 11.78/4.75  
% 11.78/4.75  
% 11.78/4.75  %Background operators:
% 11.78/4.75  
% 11.78/4.75  
% 11.78/4.75  %Foreground operators:
% 11.78/4.75  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 11.78/4.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.78/4.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.78/4.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.78/4.75  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 11.78/4.75  tff('#skF_1', type, '#skF_1': $i > $i).
% 11.78/4.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.78/4.75  tff('#skF_7', type, '#skF_7': $i).
% 11.78/4.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.78/4.75  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.78/4.75  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.78/4.75  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 11.78/4.75  tff('#skF_5', type, '#skF_5': $i).
% 11.78/4.75  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.78/4.75  tff('#skF_6', type, '#skF_6': $i).
% 11.78/4.75  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.78/4.75  tff('#skF_2', type, '#skF_2': $i).
% 11.78/4.75  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 11.78/4.75  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 11.78/4.75  tff('#skF_3', type, '#skF_3': $i).
% 11.78/4.75  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 11.78/4.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.78/4.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.78/4.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.78/4.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.78/4.75  tff('#skF_4', type, '#skF_4': $i).
% 11.78/4.75  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.78/4.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.78/4.75  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 11.78/4.75  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 11.78/4.75  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.78/4.75  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.78/4.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.78/4.75  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 11.78/4.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.78/4.75  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 11.78/4.75  
% 11.97/4.80  tff(f_266, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 11.97/4.80  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 11.97/4.80  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 11.97/4.80  tff(f_72, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 11.97/4.80  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 11.97/4.80  tff(f_114, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_mcart_1)).
% 11.97/4.80  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 11.97/4.80  tff(f_47, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 11.97/4.80  tff(f_94, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 11.97/4.80  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 11.97/4.80  tff(f_136, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 11.97/4.80  tff(f_128, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 11.97/4.80  tff(f_84, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 11.97/4.80  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 11.97/4.80  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 11.97/4.80  tff(f_142, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 11.97/4.80  tff(f_34, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 11.97/4.80  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 11.97/4.80  tff(f_30, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 11.97/4.80  tff(f_224, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 11.97/4.80  tff(f_190, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 11.97/4.80  tff(c_96, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_266])).
% 11.97/4.80  tff(c_90, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_266])).
% 11.97/4.80  tff(c_86, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_266])).
% 11.97/4.80  tff(c_78, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_266])).
% 11.97/4.80  tff(c_4231, plain, (![C_647, A_648, B_649]: (v1_relat_1(C_647) | ~m1_subset_1(C_647, k1_zfmisc_1(k2_zfmisc_1(A_648, B_649))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.97/4.80  tff(c_4239, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_78, c_4231])).
% 11.97/4.80  tff(c_72, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_266])).
% 11.97/4.80  tff(c_4238, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_72, c_4231])).
% 11.97/4.80  tff(c_3854, plain, (![C_596, A_597, B_598]: (v1_relat_1(C_596) | ~m1_subset_1(C_596, k1_zfmisc_1(k2_zfmisc_1(A_597, B_598))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.97/4.80  tff(c_3862, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_78, c_3854])).
% 11.97/4.80  tff(c_30, plain, (![A_24]: (k1_relat_1(A_24)!=k1_xboole_0 | k1_xboole_0=A_24 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.97/4.80  tff(c_3878, plain, (k1_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_3862, c_30])).
% 11.97/4.80  tff(c_3881, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3878])).
% 11.97/4.80  tff(c_24, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.97/4.80  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.97/4.80  tff(c_3819, plain, (![A_593]: (k9_relat_1(A_593, k1_relat_1(A_593))=k2_relat_1(A_593) | ~v1_relat_1(A_593))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.97/4.80  tff(c_3828, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_3819])).
% 11.97/4.80  tff(c_3831, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_3828])).
% 11.97/4.80  tff(c_3851, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_3831])).
% 11.97/4.80  tff(c_44, plain, (![A_35]: (r1_xboole_0('#skF_1'(A_35), A_35) | k1_xboole_0=A_35)), inference(cnfTransformation, [status(thm)], [f_114])).
% 11.97/4.80  tff(c_3935, plain, (![A_614, B_615]: (k7_relat_1(A_614, B_615)=k1_xboole_0 | ~r1_xboole_0(B_615, k1_relat_1(A_614)) | ~v1_relat_1(A_614))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.97/4.80  tff(c_4100, plain, (![A_645]: (k7_relat_1(A_645, '#skF_1'(k1_relat_1(A_645)))=k1_xboole_0 | ~v1_relat_1(A_645) | k1_relat_1(A_645)=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_3935])).
% 11.97/4.80  tff(c_14, plain, (![A_11, B_12]: (v1_relat_1(k7_relat_1(A_11, B_12)) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.97/4.80  tff(c_4121, plain, (![A_645]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_645) | ~v1_relat_1(A_645) | k1_relat_1(A_645)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4100, c_14])).
% 11.97/4.80  tff(c_4181, plain, (![A_646]: (~v1_relat_1(A_646) | ~v1_relat_1(A_646) | k1_relat_1(A_646)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_3851, c_4121])).
% 11.97/4.80  tff(c_4185, plain, (~v1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_3862, c_4181])).
% 11.97/4.80  tff(c_4195, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3862, c_4185])).
% 11.97/4.80  tff(c_4197, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3881, c_4195])).
% 11.97/4.80  tff(c_4198, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_3878])).
% 11.97/4.80  tff(c_4201, plain, (~v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4198, c_3851])).
% 11.97/4.80  tff(c_4214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3862, c_4201])).
% 11.97/4.80  tff(c_4215, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_3831])).
% 11.97/4.80  tff(c_92, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_266])).
% 11.97/4.80  tff(c_84, plain, (r1_subset_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_266])).
% 11.97/4.80  tff(c_88, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_266])).
% 11.97/4.80  tff(c_36, plain, (![A_27, B_28]: (r1_xboole_0(A_27, B_28) | ~r1_subset_1(A_27, B_28) | v1_xboole_0(B_28) | v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_94])).
% 11.97/4.80  tff(c_94, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_266])).
% 11.97/4.80  tff(c_4276, plain, (![C_655, A_656, B_657]: (v4_relat_1(C_655, A_656) | ~m1_subset_1(C_655, k1_zfmisc_1(k2_zfmisc_1(A_656, B_657))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.97/4.80  tff(c_4283, plain, (v4_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_72, c_4276])).
% 11.97/4.80  tff(c_16532, plain, (![B_1161, A_1162]: (k1_relat_1(B_1161)=A_1162 | ~v1_partfun1(B_1161, A_1162) | ~v4_relat_1(B_1161, A_1162) | ~v1_relat_1(B_1161))), inference(cnfTransformation, [status(thm)], [f_136])).
% 11.97/4.80  tff(c_16538, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_4283, c_16532])).
% 11.97/4.80  tff(c_16544, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4238, c_16538])).
% 11.97/4.80  tff(c_17475, plain, (~v1_partfun1('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_16544])).
% 11.97/4.80  tff(c_76, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_266])).
% 11.97/4.80  tff(c_74, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_266])).
% 11.97/4.80  tff(c_17787, plain, (![C_1240, A_1241, B_1242]: (v1_partfun1(C_1240, A_1241) | ~v1_funct_2(C_1240, A_1241, B_1242) | ~v1_funct_1(C_1240) | ~m1_subset_1(C_1240, k1_zfmisc_1(k2_zfmisc_1(A_1241, B_1242))) | v1_xboole_0(B_1242))), inference(cnfTransformation, [status(thm)], [f_128])).
% 11.97/4.80  tff(c_17790, plain, (v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_72, c_17787])).
% 11.97/4.80  tff(c_17796, plain, (v1_partfun1('#skF_7', '#skF_5') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_17790])).
% 11.97/4.80  tff(c_17798, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_17475, c_17796])).
% 11.97/4.80  tff(c_17799, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitRight, [status(thm)], [c_16544])).
% 11.97/4.80  tff(c_22, plain, (![A_21, B_23]: (k7_relat_1(A_21, B_23)=k1_xboole_0 | ~r1_xboole_0(B_23, k1_relat_1(A_21)) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.97/4.80  tff(c_17808, plain, (![B_23]: (k7_relat_1('#skF_7', B_23)=k1_xboole_0 | ~r1_xboole_0(B_23, '#skF_5') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_17799, c_22])).
% 11.97/4.80  tff(c_17830, plain, (![B_1243]: (k7_relat_1('#skF_7', B_1243)=k1_xboole_0 | ~r1_xboole_0(B_1243, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4238, c_17808])).
% 11.97/4.80  tff(c_17834, plain, (![A_27]: (k7_relat_1('#skF_7', A_27)=k1_xboole_0 | ~r1_subset_1(A_27, '#skF_5') | v1_xboole_0('#skF_5') | v1_xboole_0(A_27))), inference(resolution, [status(thm)], [c_36, c_17830])).
% 11.97/4.80  tff(c_17945, plain, (![A_1248]: (k7_relat_1('#skF_7', A_1248)=k1_xboole_0 | ~r1_subset_1(A_1248, '#skF_5') | v1_xboole_0(A_1248))), inference(negUnitSimplification, [status(thm)], [c_88, c_17834])).
% 11.97/4.80  tff(c_17948, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_84, c_17945])).
% 11.97/4.80  tff(c_17951, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_92, c_17948])).
% 11.97/4.80  tff(c_32, plain, (![B_26, A_25]: (r1_tarski(k1_relat_1(k7_relat_1(B_26, A_25)), A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_84])).
% 11.97/4.80  tff(c_17961, plain, (r1_tarski(k1_relat_1(k1_xboole_0), '#skF_4') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_17951, c_32])).
% 11.97/4.80  tff(c_17972, plain, (r1_tarski(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4238, c_26, c_17961])).
% 11.97/4.80  tff(c_20, plain, (![A_16, C_20, B_19]: (k9_relat_1(k7_relat_1(A_16, C_20), B_19)=k9_relat_1(A_16, B_19) | ~r1_tarski(B_19, C_20) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.97/4.80  tff(c_17955, plain, (![B_19]: (k9_relat_1(k1_xboole_0, B_19)=k9_relat_1('#skF_7', B_19) | ~r1_tarski(B_19, '#skF_4') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_17951, c_20])).
% 11.97/4.80  tff(c_18142, plain, (![B_1261]: (k9_relat_1(k1_xboole_0, B_1261)=k9_relat_1('#skF_7', B_1261) | ~r1_tarski(B_1261, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4238, c_17955])).
% 11.97/4.80  tff(c_18153, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k9_relat_1('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_17972, c_18142])).
% 11.97/4.80  tff(c_18167, plain, (k9_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4215, c_18153])).
% 11.97/4.80  tff(c_16435, plain, (![A_1151, B_1152]: (r1_xboole_0(A_1151, B_1152) | ~r1_subset_1(A_1151, B_1152) | v1_xboole_0(B_1152) | v1_xboole_0(A_1151))), inference(cnfTransformation, [status(thm)], [f_94])).
% 11.97/4.80  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.97/4.80  tff(c_18615, plain, (![A_1293, B_1294]: (k3_xboole_0(A_1293, B_1294)=k1_xboole_0 | ~r1_subset_1(A_1293, B_1294) | v1_xboole_0(B_1294) | v1_xboole_0(A_1293))), inference(resolution, [status(thm)], [c_16435, c_2])).
% 11.97/4.80  tff(c_18624, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0 | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_84, c_18615])).
% 11.97/4.80  tff(c_18629, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_92, c_88, c_18624])).
% 11.97/4.80  tff(c_82, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_266])).
% 11.97/4.80  tff(c_18112, plain, (![A_1255, B_1256, C_1257, D_1258]: (k2_partfun1(A_1255, B_1256, C_1257, D_1258)=k7_relat_1(C_1257, D_1258) | ~m1_subset_1(C_1257, k1_zfmisc_1(k2_zfmisc_1(A_1255, B_1256))) | ~v1_funct_1(C_1257))), inference(cnfTransformation, [status(thm)], [f_142])).
% 11.97/4.80  tff(c_18116, plain, (![D_1258]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_1258)=k7_relat_1('#skF_6', D_1258) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_78, c_18112])).
% 11.97/4.80  tff(c_18122, plain, (![D_1258]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_1258)=k7_relat_1('#skF_6', D_1258))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_18116])).
% 11.97/4.80  tff(c_18114, plain, (![D_1258]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_1258)=k7_relat_1('#skF_7', D_1258) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_72, c_18112])).
% 11.97/4.80  tff(c_18119, plain, (![D_1258]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_1258)=k7_relat_1('#skF_7', D_1258))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_18114])).
% 11.97/4.80  tff(c_16491, plain, (![A_1155, B_1156, C_1157]: (k9_subset_1(A_1155, B_1156, C_1157)=k3_xboole_0(B_1156, C_1157) | ~m1_subset_1(C_1157, k1_zfmisc_1(A_1155)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.97/4.80  tff(c_16502, plain, (![B_1156]: (k9_subset_1('#skF_2', B_1156, '#skF_5')=k3_xboole_0(B_1156, '#skF_5'))), inference(resolution, [status(thm)], [c_86, c_16491])).
% 11.97/4.80  tff(c_516, plain, (![C_304, A_305, B_306]: (v1_relat_1(C_304) | ~m1_subset_1(C_304, k1_zfmisc_1(k2_zfmisc_1(A_305, B_306))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.97/4.80  tff(c_524, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_78, c_516])).
% 11.97/4.80  tff(c_163, plain, (![C_253, A_254, B_255]: (v1_relat_1(C_253) | ~m1_subset_1(C_253, k1_zfmisc_1(k2_zfmisc_1(A_254, B_255))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.97/4.80  tff(c_171, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_78, c_163])).
% 11.97/4.80  tff(c_187, plain, (k1_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_171, c_30])).
% 11.97/4.80  tff(c_208, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_187])).
% 11.97/4.80  tff(c_149, plain, (![A_252]: (k9_relat_1(A_252, k1_relat_1(A_252))=k2_relat_1(A_252) | ~v1_relat_1(A_252))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.97/4.80  tff(c_158, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_149])).
% 11.97/4.80  tff(c_161, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_158])).
% 11.97/4.80  tff(c_162, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_161])).
% 11.97/4.80  tff(c_263, plain, (![A_271, B_272]: (k7_relat_1(A_271, B_272)=k1_xboole_0 | ~r1_xboole_0(B_272, k1_relat_1(A_271)) | ~v1_relat_1(A_271))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.97/4.80  tff(c_429, plain, (![A_302]: (k7_relat_1(A_302, '#skF_1'(k1_relat_1(A_302)))=k1_xboole_0 | ~v1_relat_1(A_302) | k1_relat_1(A_302)=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_263])).
% 11.97/4.80  tff(c_450, plain, (![A_302]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_302) | ~v1_relat_1(A_302) | k1_relat_1(A_302)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_429, c_14])).
% 11.97/4.80  tff(c_467, plain, (![A_303]: (~v1_relat_1(A_303) | ~v1_relat_1(A_303) | k1_relat_1(A_303)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_162, c_450])).
% 11.97/4.80  tff(c_469, plain, (~v1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_171, c_467])).
% 11.97/4.80  tff(c_476, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_171, c_469])).
% 11.97/4.80  tff(c_478, plain, $false, inference(negUnitSimplification, [status(thm)], [c_208, c_476])).
% 11.97/4.80  tff(c_479, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_187])).
% 11.97/4.80  tff(c_482, plain, (~v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_479, c_162])).
% 11.97/4.80  tff(c_495, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_171, c_482])).
% 11.97/4.80  tff(c_496, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_161])).
% 11.97/4.80  tff(c_584, plain, (![C_314, A_315, B_316]: (v4_relat_1(C_314, A_315) | ~m1_subset_1(C_314, k1_zfmisc_1(k2_zfmisc_1(A_315, B_316))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.97/4.80  tff(c_592, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_78, c_584])).
% 11.97/4.80  tff(c_711, plain, (![B_328, A_329]: (k1_relat_1(B_328)=A_329 | ~v1_partfun1(B_328, A_329) | ~v4_relat_1(B_328, A_329) | ~v1_relat_1(B_328))), inference(cnfTransformation, [status(thm)], [f_136])).
% 11.97/4.80  tff(c_714, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_592, c_711])).
% 11.97/4.80  tff(c_720, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_524, c_714])).
% 11.97/4.80  tff(c_724, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_720])).
% 11.97/4.80  tff(c_80, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_266])).
% 11.97/4.80  tff(c_1384, plain, (![C_388, A_389, B_390]: (v1_partfun1(C_388, A_389) | ~v1_funct_2(C_388, A_389, B_390) | ~v1_funct_1(C_388) | ~m1_subset_1(C_388, k1_zfmisc_1(k2_zfmisc_1(A_389, B_390))) | v1_xboole_0(B_390))), inference(cnfTransformation, [status(thm)], [f_128])).
% 11.97/4.80  tff(c_1390, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_78, c_1384])).
% 11.97/4.80  tff(c_1397, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_1390])).
% 11.97/4.80  tff(c_1399, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_724, c_1397])).
% 11.97/4.80  tff(c_1400, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_720])).
% 11.97/4.80  tff(c_540, plain, (k1_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_524, c_30])).
% 11.97/4.80  tff(c_542, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_540])).
% 11.97/4.80  tff(c_1402, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1400, c_542])).
% 11.97/4.80  tff(c_1406, plain, (![B_23]: (k7_relat_1('#skF_6', B_23)=k1_xboole_0 | ~r1_xboole_0(B_23, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1400, c_22])).
% 11.97/4.80  tff(c_1873, plain, (![B_426]: (k7_relat_1('#skF_6', B_426)=k1_xboole_0 | ~r1_xboole_0(B_426, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_524, c_1406])).
% 11.97/4.80  tff(c_1885, plain, (k7_relat_1('#skF_6', '#skF_1'('#skF_4'))=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_44, c_1873])).
% 11.97/4.80  tff(c_1892, plain, (k7_relat_1('#skF_6', '#skF_1'('#skF_4'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_1402, c_1885])).
% 11.97/4.80  tff(c_1899, plain, (r1_tarski(k1_relat_1(k1_xboole_0), '#skF_1'('#skF_4')) | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1892, c_32])).
% 11.97/4.80  tff(c_1908, plain, (r1_tarski(k1_xboole_0, '#skF_1'('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_524, c_26, c_1899])).
% 11.97/4.80  tff(c_2023, plain, (![A_434, C_435, B_436]: (k9_relat_1(k7_relat_1(A_434, C_435), B_436)=k9_relat_1(A_434, B_436) | ~r1_tarski(B_436, C_435) | ~v1_relat_1(A_434))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.97/4.80  tff(c_2042, plain, (![B_436]: (k9_relat_1(k1_xboole_0, B_436)=k9_relat_1('#skF_6', B_436) | ~r1_tarski(B_436, '#skF_1'('#skF_4')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1892, c_2023])).
% 11.97/4.80  tff(c_2352, plain, (![B_462]: (k9_relat_1(k1_xboole_0, B_462)=k9_relat_1('#skF_6', B_462) | ~r1_tarski(B_462, '#skF_1'('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_524, c_2042])).
% 11.97/4.80  tff(c_2363, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k9_relat_1('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_1908, c_2352])).
% 11.97/4.80  tff(c_2377, plain, (k9_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_496, c_2363])).
% 11.97/4.80  tff(c_18, plain, (![B_15, A_14]: (k2_relat_1(k7_relat_1(B_15, A_14))=k9_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.97/4.80  tff(c_124, plain, (![A_246]: (k2_relat_1(A_246)!=k1_xboole_0 | k1_xboole_0=A_246 | ~v1_relat_1(A_246))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.97/4.80  tff(c_2587, plain, (![A_481, B_482]: (k2_relat_1(k7_relat_1(A_481, B_482))!=k1_xboole_0 | k7_relat_1(A_481, B_482)=k1_xboole_0 | ~v1_relat_1(A_481))), inference(resolution, [status(thm)], [c_14, c_124])).
% 11.97/4.80  tff(c_2725, plain, (![B_493, A_494]: (k9_relat_1(B_493, A_494)!=k1_xboole_0 | k7_relat_1(B_493, A_494)=k1_xboole_0 | ~v1_relat_1(B_493) | ~v1_relat_1(B_493))), inference(superposition, [status(thm), theory('equality')], [c_18, c_2587])).
% 11.97/4.80  tff(c_2727, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2377, c_2725])).
% 11.97/4.80  tff(c_2754, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_524, c_2727])).
% 11.97/4.80  tff(c_652, plain, (![A_322, B_323]: (r1_xboole_0(A_322, B_323) | ~r1_subset_1(A_322, B_323) | v1_xboole_0(B_323) | v1_xboole_0(A_322))), inference(cnfTransformation, [status(thm)], [f_94])).
% 11.97/4.80  tff(c_2438, plain, (![A_467, B_468]: (k3_xboole_0(A_467, B_468)=k1_xboole_0 | ~r1_subset_1(A_467, B_468) | v1_xboole_0(B_468) | v1_xboole_0(A_467))), inference(resolution, [status(thm)], [c_652, c_2])).
% 11.97/4.80  tff(c_2441, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0 | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_84, c_2438])).
% 11.97/4.80  tff(c_2444, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_92, c_88, c_2441])).
% 11.97/4.80  tff(c_2148, plain, (![A_442, B_443, C_444, D_445]: (k2_partfun1(A_442, B_443, C_444, D_445)=k7_relat_1(C_444, D_445) | ~m1_subset_1(C_444, k1_zfmisc_1(k2_zfmisc_1(A_442, B_443))) | ~v1_funct_1(C_444))), inference(cnfTransformation, [status(thm)], [f_142])).
% 11.97/4.80  tff(c_2152, plain, (![D_445]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_445)=k7_relat_1('#skF_6', D_445) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_78, c_2148])).
% 11.97/4.80  tff(c_2158, plain, (![D_445]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_445)=k7_relat_1('#skF_6', D_445))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_2152])).
% 11.97/4.80  tff(c_2150, plain, (![D_445]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_445)=k7_relat_1('#skF_7', D_445) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_72, c_2148])).
% 11.97/4.80  tff(c_2155, plain, (![D_445]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_445)=k7_relat_1('#skF_7', D_445))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_2150])).
% 11.97/4.80  tff(c_1912, plain, (![A_427, B_428, C_429]: (k9_subset_1(A_427, B_428, C_429)=k3_xboole_0(B_428, C_429) | ~m1_subset_1(C_429, k1_zfmisc_1(A_427)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.97/4.80  tff(c_1923, plain, (![B_428]: (k9_subset_1('#skF_2', B_428, '#skF_5')=k3_xboole_0(B_428, '#skF_5'))), inference(resolution, [status(thm)], [c_86, c_1912])).
% 11.97/4.80  tff(c_70, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')!='#skF_7' | k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')!='#skF_6' | k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_266])).
% 11.97/4.80  tff(c_108, plain, (k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_70])).
% 11.97/4.80  tff(c_1929, plain, (k2_partfun1('#skF_5', '#skF_3', '#skF_7', k3_xboole_0('#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1923, c_1923, c_108])).
% 11.97/4.80  tff(c_2280, plain, (k7_relat_1('#skF_7', k3_xboole_0('#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2158, c_2155, c_1929])).
% 11.97/4.80  tff(c_2445, plain, (k7_relat_1('#skF_7', k1_xboole_0)!=k7_relat_1('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2444, c_2444, c_2280])).
% 11.97/4.80  tff(c_2826, plain, (k7_relat_1('#skF_7', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2754, c_2445])).
% 11.97/4.80  tff(c_523, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_72, c_516])).
% 11.97/4.80  tff(c_591, plain, (v4_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_72, c_584])).
% 11.97/4.80  tff(c_717, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_591, c_711])).
% 11.97/4.80  tff(c_723, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_523, c_717])).
% 11.97/4.80  tff(c_1422, plain, (~v1_partfun1('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_723])).
% 11.97/4.80  tff(c_1829, plain, (![C_423, A_424, B_425]: (v1_partfun1(C_423, A_424) | ~v1_funct_2(C_423, A_424, B_425) | ~v1_funct_1(C_423) | ~m1_subset_1(C_423, k1_zfmisc_1(k2_zfmisc_1(A_424, B_425))) | v1_xboole_0(B_425))), inference(cnfTransformation, [status(thm)], [f_128])).
% 11.97/4.80  tff(c_1832, plain, (v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_72, c_1829])).
% 11.97/4.80  tff(c_1838, plain, (v1_partfun1('#skF_7', '#skF_5') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_1832])).
% 11.97/4.80  tff(c_1840, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_1422, c_1838])).
% 11.97/4.80  tff(c_1841, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitRight, [status(thm)], [c_723])).
% 11.97/4.80  tff(c_1847, plain, (![B_23]: (k7_relat_1('#skF_7', B_23)=k1_xboole_0 | ~r1_xboole_0(B_23, '#skF_5') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1841, c_22])).
% 11.97/4.80  tff(c_1948, plain, (![B_432]: (k7_relat_1('#skF_7', B_432)=k1_xboole_0 | ~r1_xboole_0(B_432, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_523, c_1847])).
% 11.97/4.80  tff(c_1952, plain, (![A_27]: (k7_relat_1('#skF_7', A_27)=k1_xboole_0 | ~r1_subset_1(A_27, '#skF_5') | v1_xboole_0('#skF_5') | v1_xboole_0(A_27))), inference(resolution, [status(thm)], [c_36, c_1948])).
% 11.97/4.80  tff(c_2241, plain, (![A_454]: (k7_relat_1('#skF_7', A_454)=k1_xboole_0 | ~r1_subset_1(A_454, '#skF_5') | v1_xboole_0(A_454))), inference(negUnitSimplification, [status(thm)], [c_88, c_1952])).
% 11.97/4.80  tff(c_2244, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_84, c_2241])).
% 11.97/4.80  tff(c_2247, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_92, c_2244])).
% 11.97/4.80  tff(c_2260, plain, (r1_tarski(k1_relat_1(k1_xboole_0), '#skF_4') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2247, c_32])).
% 11.97/4.80  tff(c_2275, plain, (r1_tarski(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_523, c_26, c_2260])).
% 11.97/4.80  tff(c_2254, plain, (![B_19]: (k9_relat_1(k1_xboole_0, B_19)=k9_relat_1('#skF_7', B_19) | ~r1_tarski(B_19, '#skF_4') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2247, c_20])).
% 11.97/4.80  tff(c_2296, plain, (![B_455]: (k9_relat_1(k1_xboole_0, B_455)=k9_relat_1('#skF_7', B_455) | ~r1_tarski(B_455, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_523, c_2254])).
% 11.97/4.80  tff(c_2299, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k9_relat_1('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_2275, c_2296])).
% 11.97/4.80  tff(c_2317, plain, (k9_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_496, c_2299])).
% 11.97/4.80  tff(c_2729, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0 | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2317, c_2725])).
% 11.97/4.80  tff(c_2757, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_523, c_2729])).
% 11.97/4.80  tff(c_2877, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2826, c_2757])).
% 11.97/4.80  tff(c_2878, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_540])).
% 11.97/4.80  tff(c_2879, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_540])).
% 11.97/4.80  tff(c_2899, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2878, c_2879])).
% 11.97/4.80  tff(c_2979, plain, (![C_510, A_511, B_512]: (v4_relat_1(C_510, A_511) | ~m1_subset_1(C_510, k1_zfmisc_1(k2_zfmisc_1(A_511, B_512))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.97/4.80  tff(c_2987, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_78, c_2979])).
% 11.97/4.80  tff(c_3192, plain, (![B_538, A_539]: (k1_relat_1(B_538)=A_539 | ~v1_partfun1(B_538, A_539) | ~v4_relat_1(B_538, A_539) | ~v1_relat_1(B_538))), inference(cnfTransformation, [status(thm)], [f_136])).
% 11.97/4.80  tff(c_3195, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2987, c_3192])).
% 11.97/4.80  tff(c_3201, plain, ('#skF_6'='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_524, c_2899, c_3195])).
% 11.97/4.80  tff(c_3205, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_3201])).
% 11.97/4.80  tff(c_3727, plain, (![C_581, A_582, B_583]: (v1_partfun1(C_581, A_582) | ~v1_funct_2(C_581, A_582, B_583) | ~v1_funct_1(C_581) | ~m1_subset_1(C_581, k1_zfmisc_1(k2_zfmisc_1(A_582, B_583))) | v1_xboole_0(B_583))), inference(cnfTransformation, [status(thm)], [f_128])).
% 11.97/4.80  tff(c_3733, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_78, c_3727])).
% 11.97/4.80  tff(c_3740, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_3733])).
% 11.97/4.80  tff(c_3742, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_3205, c_3740])).
% 11.97/4.80  tff(c_3743, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_3201])).
% 11.97/4.80  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 11.97/4.80  tff(c_2892, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2878, c_6])).
% 11.97/4.80  tff(c_3766, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3743, c_2892])).
% 11.97/4.80  tff(c_3773, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_3766])).
% 11.97/4.80  tff(c_3775, plain, (k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_70])).
% 11.97/4.80  tff(c_16504, plain, (k2_partfun1('#skF_5', '#skF_3', '#skF_7', k3_xboole_0('#skF_4', '#skF_5'))=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_16502, c_16502, c_3775])).
% 11.97/4.80  tff(c_18123, plain, (k2_partfun1('#skF_4', '#skF_3', '#skF_6', k3_xboole_0('#skF_4', '#skF_5'))=k7_relat_1('#skF_7', k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_18119, c_16504])).
% 11.97/4.80  tff(c_18247, plain, (k7_relat_1('#skF_7', k3_xboole_0('#skF_4', '#skF_5'))=k7_relat_1('#skF_6', k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_18122, c_18123])).
% 11.97/4.80  tff(c_18632, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k7_relat_1('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18629, c_18629, c_18247])).
% 11.97/4.80  tff(c_18671, plain, (k2_relat_1(k7_relat_1('#skF_6', k1_xboole_0))=k9_relat_1('#skF_7', k1_xboole_0) | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_18632, c_18])).
% 11.97/4.80  tff(c_18690, plain, (k2_relat_1(k7_relat_1('#skF_6', k1_xboole_0))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4238, c_18167, c_18671])).
% 11.97/4.80  tff(c_3804, plain, (![A_591]: (k2_relat_1(A_591)!=k1_xboole_0 | k1_xboole_0=A_591 | ~v1_relat_1(A_591))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.97/4.80  tff(c_3808, plain, (![A_11, B_12]: (k2_relat_1(k7_relat_1(A_11, B_12))!=k1_xboole_0 | k7_relat_1(A_11, B_12)=k1_xboole_0 | ~v1_relat_1(A_11))), inference(resolution, [status(thm)], [c_14, c_3804])).
% 11.97/4.80  tff(c_18699, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_18690, c_3808])).
% 11.97/4.80  tff(c_18713, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4239, c_18699])).
% 11.97/4.80  tff(c_18721, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_18713, c_18632])).
% 11.97/4.80  tff(c_18364, plain, (![A_1269, D_1270, C_1271, F_1268, B_1273, E_1272]: (v1_funct_1(k1_tmap_1(A_1269, B_1273, C_1271, D_1270, E_1272, F_1268)) | ~m1_subset_1(F_1268, k1_zfmisc_1(k2_zfmisc_1(D_1270, B_1273))) | ~v1_funct_2(F_1268, D_1270, B_1273) | ~v1_funct_1(F_1268) | ~m1_subset_1(E_1272, k1_zfmisc_1(k2_zfmisc_1(C_1271, B_1273))) | ~v1_funct_2(E_1272, C_1271, B_1273) | ~v1_funct_1(E_1272) | ~m1_subset_1(D_1270, k1_zfmisc_1(A_1269)) | v1_xboole_0(D_1270) | ~m1_subset_1(C_1271, k1_zfmisc_1(A_1269)) | v1_xboole_0(C_1271) | v1_xboole_0(B_1273) | v1_xboole_0(A_1269))), inference(cnfTransformation, [status(thm)], [f_224])).
% 11.97/4.80  tff(c_18366, plain, (![A_1269, C_1271, E_1272]: (v1_funct_1(k1_tmap_1(A_1269, '#skF_3', C_1271, '#skF_5', E_1272, '#skF_7')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_1272, k1_zfmisc_1(k2_zfmisc_1(C_1271, '#skF_3'))) | ~v1_funct_2(E_1272, C_1271, '#skF_3') | ~v1_funct_1(E_1272) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1269)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1271, k1_zfmisc_1(A_1269)) | v1_xboole_0(C_1271) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1269))), inference(resolution, [status(thm)], [c_72, c_18364])).
% 11.97/4.80  tff(c_18371, plain, (![A_1269, C_1271, E_1272]: (v1_funct_1(k1_tmap_1(A_1269, '#skF_3', C_1271, '#skF_5', E_1272, '#skF_7')) | ~m1_subset_1(E_1272, k1_zfmisc_1(k2_zfmisc_1(C_1271, '#skF_3'))) | ~v1_funct_2(E_1272, C_1271, '#skF_3') | ~v1_funct_1(E_1272) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1269)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1271, k1_zfmisc_1(A_1269)) | v1_xboole_0(C_1271) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1269))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_18366])).
% 11.97/4.80  tff(c_18380, plain, (![A_1274, C_1275, E_1276]: (v1_funct_1(k1_tmap_1(A_1274, '#skF_3', C_1275, '#skF_5', E_1276, '#skF_7')) | ~m1_subset_1(E_1276, k1_zfmisc_1(k2_zfmisc_1(C_1275, '#skF_3'))) | ~v1_funct_2(E_1276, C_1275, '#skF_3') | ~v1_funct_1(E_1276) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1274)) | ~m1_subset_1(C_1275, k1_zfmisc_1(A_1274)) | v1_xboole_0(C_1275) | v1_xboole_0(A_1274))), inference(negUnitSimplification, [status(thm)], [c_94, c_88, c_18371])).
% 11.97/4.80  tff(c_18384, plain, (![A_1274]: (v1_funct_1(k1_tmap_1(A_1274, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1274)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1274)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1274))), inference(resolution, [status(thm)], [c_78, c_18380])).
% 11.97/4.80  tff(c_18391, plain, (![A_1274]: (v1_funct_1(k1_tmap_1(A_1274, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1274)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1274)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1274))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_18384])).
% 11.97/4.80  tff(c_18919, plain, (![A_1310]: (v1_funct_1(k1_tmap_1(A_1310, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1310)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1310)) | v1_xboole_0(A_1310))), inference(negUnitSimplification, [status(thm)], [c_92, c_18391])).
% 11.97/4.80  tff(c_18922, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_86, c_18919])).
% 11.97/4.80  tff(c_18925, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_18922])).
% 11.97/4.80  tff(c_18926, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_96, c_18925])).
% 11.97/4.80  tff(c_66, plain, (![C_176, A_174, D_177, E_178, B_175, F_179]: (v1_funct_2(k1_tmap_1(A_174, B_175, C_176, D_177, E_178, F_179), k4_subset_1(A_174, C_176, D_177), B_175) | ~m1_subset_1(F_179, k1_zfmisc_1(k2_zfmisc_1(D_177, B_175))) | ~v1_funct_2(F_179, D_177, B_175) | ~v1_funct_1(F_179) | ~m1_subset_1(E_178, k1_zfmisc_1(k2_zfmisc_1(C_176, B_175))) | ~v1_funct_2(E_178, C_176, B_175) | ~v1_funct_1(E_178) | ~m1_subset_1(D_177, k1_zfmisc_1(A_174)) | v1_xboole_0(D_177) | ~m1_subset_1(C_176, k1_zfmisc_1(A_174)) | v1_xboole_0(C_176) | v1_xboole_0(B_175) | v1_xboole_0(A_174))), inference(cnfTransformation, [status(thm)], [f_224])).
% 11.97/4.80  tff(c_64, plain, (![C_176, A_174, D_177, E_178, B_175, F_179]: (m1_subset_1(k1_tmap_1(A_174, B_175, C_176, D_177, E_178, F_179), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_174, C_176, D_177), B_175))) | ~m1_subset_1(F_179, k1_zfmisc_1(k2_zfmisc_1(D_177, B_175))) | ~v1_funct_2(F_179, D_177, B_175) | ~v1_funct_1(F_179) | ~m1_subset_1(E_178, k1_zfmisc_1(k2_zfmisc_1(C_176, B_175))) | ~v1_funct_2(E_178, C_176, B_175) | ~v1_funct_1(E_178) | ~m1_subset_1(D_177, k1_zfmisc_1(A_174)) | v1_xboole_0(D_177) | ~m1_subset_1(C_176, k1_zfmisc_1(A_174)) | v1_xboole_0(C_176) | v1_xboole_0(B_175) | v1_xboole_0(A_174))), inference(cnfTransformation, [status(thm)], [f_224])).
% 11.97/4.80  tff(c_18855, plain, (![F_1303, C_1304, E_1307, B_1305, D_1306, A_1302]: (k2_partfun1(k4_subset_1(A_1302, C_1304, D_1306), B_1305, k1_tmap_1(A_1302, B_1305, C_1304, D_1306, E_1307, F_1303), C_1304)=E_1307 | ~m1_subset_1(k1_tmap_1(A_1302, B_1305, C_1304, D_1306, E_1307, F_1303), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1302, C_1304, D_1306), B_1305))) | ~v1_funct_2(k1_tmap_1(A_1302, B_1305, C_1304, D_1306, E_1307, F_1303), k4_subset_1(A_1302, C_1304, D_1306), B_1305) | ~v1_funct_1(k1_tmap_1(A_1302, B_1305, C_1304, D_1306, E_1307, F_1303)) | k2_partfun1(D_1306, B_1305, F_1303, k9_subset_1(A_1302, C_1304, D_1306))!=k2_partfun1(C_1304, B_1305, E_1307, k9_subset_1(A_1302, C_1304, D_1306)) | ~m1_subset_1(F_1303, k1_zfmisc_1(k2_zfmisc_1(D_1306, B_1305))) | ~v1_funct_2(F_1303, D_1306, B_1305) | ~v1_funct_1(F_1303) | ~m1_subset_1(E_1307, k1_zfmisc_1(k2_zfmisc_1(C_1304, B_1305))) | ~v1_funct_2(E_1307, C_1304, B_1305) | ~v1_funct_1(E_1307) | ~m1_subset_1(D_1306, k1_zfmisc_1(A_1302)) | v1_xboole_0(D_1306) | ~m1_subset_1(C_1304, k1_zfmisc_1(A_1302)) | v1_xboole_0(C_1304) | v1_xboole_0(B_1305) | v1_xboole_0(A_1302))), inference(cnfTransformation, [status(thm)], [f_190])).
% 11.97/4.80  tff(c_22022, plain, (![E_1456, A_1453, F_1452, B_1457, C_1455, D_1454]: (k2_partfun1(k4_subset_1(A_1453, C_1455, D_1454), B_1457, k1_tmap_1(A_1453, B_1457, C_1455, D_1454, E_1456, F_1452), C_1455)=E_1456 | ~v1_funct_2(k1_tmap_1(A_1453, B_1457, C_1455, D_1454, E_1456, F_1452), k4_subset_1(A_1453, C_1455, D_1454), B_1457) | ~v1_funct_1(k1_tmap_1(A_1453, B_1457, C_1455, D_1454, E_1456, F_1452)) | k2_partfun1(D_1454, B_1457, F_1452, k9_subset_1(A_1453, C_1455, D_1454))!=k2_partfun1(C_1455, B_1457, E_1456, k9_subset_1(A_1453, C_1455, D_1454)) | ~m1_subset_1(F_1452, k1_zfmisc_1(k2_zfmisc_1(D_1454, B_1457))) | ~v1_funct_2(F_1452, D_1454, B_1457) | ~v1_funct_1(F_1452) | ~m1_subset_1(E_1456, k1_zfmisc_1(k2_zfmisc_1(C_1455, B_1457))) | ~v1_funct_2(E_1456, C_1455, B_1457) | ~v1_funct_1(E_1456) | ~m1_subset_1(D_1454, k1_zfmisc_1(A_1453)) | v1_xboole_0(D_1454) | ~m1_subset_1(C_1455, k1_zfmisc_1(A_1453)) | v1_xboole_0(C_1455) | v1_xboole_0(B_1457) | v1_xboole_0(A_1453))), inference(resolution, [status(thm)], [c_64, c_18855])).
% 11.97/4.80  tff(c_24821, plain, (![C_1533, F_1530, A_1531, D_1532, B_1535, E_1534]: (k2_partfun1(k4_subset_1(A_1531, C_1533, D_1532), B_1535, k1_tmap_1(A_1531, B_1535, C_1533, D_1532, E_1534, F_1530), C_1533)=E_1534 | ~v1_funct_1(k1_tmap_1(A_1531, B_1535, C_1533, D_1532, E_1534, F_1530)) | k2_partfun1(D_1532, B_1535, F_1530, k9_subset_1(A_1531, C_1533, D_1532))!=k2_partfun1(C_1533, B_1535, E_1534, k9_subset_1(A_1531, C_1533, D_1532)) | ~m1_subset_1(F_1530, k1_zfmisc_1(k2_zfmisc_1(D_1532, B_1535))) | ~v1_funct_2(F_1530, D_1532, B_1535) | ~v1_funct_1(F_1530) | ~m1_subset_1(E_1534, k1_zfmisc_1(k2_zfmisc_1(C_1533, B_1535))) | ~v1_funct_2(E_1534, C_1533, B_1535) | ~v1_funct_1(E_1534) | ~m1_subset_1(D_1532, k1_zfmisc_1(A_1531)) | v1_xboole_0(D_1532) | ~m1_subset_1(C_1533, k1_zfmisc_1(A_1531)) | v1_xboole_0(C_1533) | v1_xboole_0(B_1535) | v1_xboole_0(A_1531))), inference(resolution, [status(thm)], [c_66, c_22022])).
% 11.97/4.80  tff(c_24825, plain, (![A_1531, C_1533, E_1534]: (k2_partfun1(k4_subset_1(A_1531, C_1533, '#skF_5'), '#skF_3', k1_tmap_1(A_1531, '#skF_3', C_1533, '#skF_5', E_1534, '#skF_7'), C_1533)=E_1534 | ~v1_funct_1(k1_tmap_1(A_1531, '#skF_3', C_1533, '#skF_5', E_1534, '#skF_7')) | k2_partfun1(C_1533, '#skF_3', E_1534, k9_subset_1(A_1531, C_1533, '#skF_5'))!=k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1(A_1531, C_1533, '#skF_5')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_1534, k1_zfmisc_1(k2_zfmisc_1(C_1533, '#skF_3'))) | ~v1_funct_2(E_1534, C_1533, '#skF_3') | ~v1_funct_1(E_1534) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1531)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1533, k1_zfmisc_1(A_1531)) | v1_xboole_0(C_1533) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1531))), inference(resolution, [status(thm)], [c_72, c_24821])).
% 11.97/4.80  tff(c_24831, plain, (![A_1531, C_1533, E_1534]: (k2_partfun1(k4_subset_1(A_1531, C_1533, '#skF_5'), '#skF_3', k1_tmap_1(A_1531, '#skF_3', C_1533, '#skF_5', E_1534, '#skF_7'), C_1533)=E_1534 | ~v1_funct_1(k1_tmap_1(A_1531, '#skF_3', C_1533, '#skF_5', E_1534, '#skF_7')) | k2_partfun1(C_1533, '#skF_3', E_1534, k9_subset_1(A_1531, C_1533, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_1531, C_1533, '#skF_5')) | ~m1_subset_1(E_1534, k1_zfmisc_1(k2_zfmisc_1(C_1533, '#skF_3'))) | ~v1_funct_2(E_1534, C_1533, '#skF_3') | ~v1_funct_1(E_1534) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1531)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1533, k1_zfmisc_1(A_1531)) | v1_xboole_0(C_1533) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1531))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_18119, c_24825])).
% 11.97/4.80  tff(c_24923, plain, (![A_1538, C_1539, E_1540]: (k2_partfun1(k4_subset_1(A_1538, C_1539, '#skF_5'), '#skF_3', k1_tmap_1(A_1538, '#skF_3', C_1539, '#skF_5', E_1540, '#skF_7'), C_1539)=E_1540 | ~v1_funct_1(k1_tmap_1(A_1538, '#skF_3', C_1539, '#skF_5', E_1540, '#skF_7')) | k2_partfun1(C_1539, '#skF_3', E_1540, k9_subset_1(A_1538, C_1539, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_1538, C_1539, '#skF_5')) | ~m1_subset_1(E_1540, k1_zfmisc_1(k2_zfmisc_1(C_1539, '#skF_3'))) | ~v1_funct_2(E_1540, C_1539, '#skF_3') | ~v1_funct_1(E_1540) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1538)) | ~m1_subset_1(C_1539, k1_zfmisc_1(A_1538)) | v1_xboole_0(C_1539) | v1_xboole_0(A_1538))), inference(negUnitSimplification, [status(thm)], [c_94, c_88, c_24831])).
% 11.97/4.80  tff(c_24930, plain, (![A_1538]: (k2_partfun1(k4_subset_1(A_1538, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_1538, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1538, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1(A_1538, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_1538, '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1538)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1538)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1538))), inference(resolution, [status(thm)], [c_78, c_24923])).
% 11.97/4.80  tff(c_24940, plain, (![A_1538]: (k2_partfun1(k4_subset_1(A_1538, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_1538, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1538, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_1538, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_1538, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1538)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1538)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1538))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_18122, c_24930])).
% 11.97/4.80  tff(c_26211, plain, (![A_1563]: (k2_partfun1(k4_subset_1(A_1563, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_1563, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1563, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_1563, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_1563, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1563)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1563)) | v1_xboole_0(A_1563))), inference(negUnitSimplification, [status(thm)], [c_92, c_24940])).
% 11.97/4.80  tff(c_4413, plain, (![B_671, A_672]: (k1_relat_1(B_671)=A_672 | ~v1_partfun1(B_671, A_672) | ~v4_relat_1(B_671, A_672) | ~v1_relat_1(B_671))), inference(cnfTransformation, [status(thm)], [f_136])).
% 11.97/4.80  tff(c_4419, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_4283, c_4413])).
% 11.97/4.80  tff(c_4425, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4238, c_4419])).
% 11.97/4.80  tff(c_5265, plain, (~v1_partfun1('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_4425])).
% 11.97/4.80  tff(c_5692, plain, (![C_763, A_764, B_765]: (v1_partfun1(C_763, A_764) | ~v1_funct_2(C_763, A_764, B_765) | ~v1_funct_1(C_763) | ~m1_subset_1(C_763, k1_zfmisc_1(k2_zfmisc_1(A_764, B_765))) | v1_xboole_0(B_765))), inference(cnfTransformation, [status(thm)], [f_128])).
% 11.97/4.80  tff(c_5695, plain, (v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_72, c_5692])).
% 11.97/4.80  tff(c_5701, plain, (v1_partfun1('#skF_7', '#skF_5') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_5695])).
% 11.97/4.80  tff(c_5703, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_5265, c_5701])).
% 11.97/4.80  tff(c_5704, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitRight, [status(thm)], [c_4425])).
% 11.97/4.80  tff(c_5713, plain, (![B_23]: (k7_relat_1('#skF_7', B_23)=k1_xboole_0 | ~r1_xboole_0(B_23, '#skF_5') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_5704, c_22])).
% 11.97/4.80  tff(c_5811, plain, (![B_772]: (k7_relat_1('#skF_7', B_772)=k1_xboole_0 | ~r1_xboole_0(B_772, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4238, c_5713])).
% 11.97/4.80  tff(c_5815, plain, (![A_27]: (k7_relat_1('#skF_7', A_27)=k1_xboole_0 | ~r1_subset_1(A_27, '#skF_5') | v1_xboole_0('#skF_5') | v1_xboole_0(A_27))), inference(resolution, [status(thm)], [c_36, c_5811])).
% 11.97/4.80  tff(c_6104, plain, (![A_794]: (k7_relat_1('#skF_7', A_794)=k1_xboole_0 | ~r1_subset_1(A_794, '#skF_5') | v1_xboole_0(A_794))), inference(negUnitSimplification, [status(thm)], [c_88, c_5815])).
% 11.97/4.80  tff(c_6107, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_84, c_6104])).
% 11.97/4.80  tff(c_6110, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_92, c_6107])).
% 11.97/4.80  tff(c_6123, plain, (r1_tarski(k1_relat_1(k1_xboole_0), '#skF_4') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_6110, c_32])).
% 11.97/4.80  tff(c_6138, plain, (r1_tarski(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4238, c_26, c_6123])).
% 11.97/4.80  tff(c_6117, plain, (![B_19]: (k9_relat_1(k1_xboole_0, B_19)=k9_relat_1('#skF_7', B_19) | ~r1_tarski(B_19, '#skF_4') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_6110, c_20])).
% 11.97/4.80  tff(c_6198, plain, (![B_795]: (k9_relat_1(k1_xboole_0, B_795)=k9_relat_1('#skF_7', B_795) | ~r1_tarski(B_795, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4238, c_6117])).
% 11.97/4.80  tff(c_6201, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k9_relat_1('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_6138, c_6198])).
% 11.97/4.80  tff(c_6219, plain, (k9_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4215, c_6201])).
% 11.97/4.80  tff(c_4357, plain, (![A_667, B_668]: (r1_xboole_0(A_667, B_668) | ~r1_subset_1(A_667, B_668) | v1_xboole_0(B_668) | v1_xboole_0(A_667))), inference(cnfTransformation, [status(thm)], [f_94])).
% 11.97/4.80  tff(c_6358, plain, (![A_815, B_816]: (k3_xboole_0(A_815, B_816)=k1_xboole_0 | ~r1_subset_1(A_815, B_816) | v1_xboole_0(B_816) | v1_xboole_0(A_815))), inference(resolution, [status(thm)], [c_4357, c_2])).
% 11.97/4.80  tff(c_6364, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0 | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_84, c_6358])).
% 11.97/4.80  tff(c_6368, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_92, c_88, c_6364])).
% 11.97/4.80  tff(c_6011, plain, (![A_782, B_783, C_784, D_785]: (k2_partfun1(A_782, B_783, C_784, D_785)=k7_relat_1(C_784, D_785) | ~m1_subset_1(C_784, k1_zfmisc_1(k2_zfmisc_1(A_782, B_783))) | ~v1_funct_1(C_784))), inference(cnfTransformation, [status(thm)], [f_142])).
% 11.97/4.80  tff(c_6015, plain, (![D_785]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_785)=k7_relat_1('#skF_6', D_785) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_78, c_6011])).
% 11.97/4.80  tff(c_6021, plain, (![D_785]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_785)=k7_relat_1('#skF_6', D_785))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_6015])).
% 11.97/4.80  tff(c_6013, plain, (![D_785]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_785)=k7_relat_1('#skF_7', D_785) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_72, c_6011])).
% 11.97/4.80  tff(c_6018, plain, (![D_785]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_785)=k7_relat_1('#skF_7', D_785))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_6013])).
% 11.97/4.80  tff(c_5775, plain, (![A_767, B_768, C_769]: (k9_subset_1(A_767, B_768, C_769)=k3_xboole_0(B_768, C_769) | ~m1_subset_1(C_769, k1_zfmisc_1(A_767)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.97/4.80  tff(c_5786, plain, (![B_768]: (k9_subset_1('#skF_2', B_768, '#skF_5')=k3_xboole_0(B_768, '#skF_5'))), inference(resolution, [status(thm)], [c_86, c_5775])).
% 11.97/4.80  tff(c_5792, plain, (k2_partfun1('#skF_5', '#skF_3', '#skF_7', k3_xboole_0('#skF_4', '#skF_5'))=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_5786, c_5786, c_3775])).
% 11.97/4.80  tff(c_6143, plain, (k7_relat_1('#skF_7', k3_xboole_0('#skF_4', '#skF_5'))=k7_relat_1('#skF_6', k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_6021, c_6018, c_5792])).
% 11.97/4.80  tff(c_6371, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k7_relat_1('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6368, c_6368, c_6143])).
% 11.97/4.80  tff(c_6404, plain, (k2_relat_1(k7_relat_1('#skF_6', k1_xboole_0))=k9_relat_1('#skF_7', k1_xboole_0) | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_6371, c_18])).
% 11.97/4.80  tff(c_6419, plain, (k2_relat_1(k7_relat_1('#skF_6', k1_xboole_0))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4238, c_6219, c_6404])).
% 11.97/4.80  tff(c_6159, plain, (v1_relat_1(k7_relat_1('#skF_6', k3_xboole_0('#skF_4', '#skF_5'))) | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_6143, c_14])).
% 11.97/4.80  tff(c_6172, plain, (v1_relat_1(k7_relat_1('#skF_6', k3_xboole_0('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_4238, c_6159])).
% 11.97/4.80  tff(c_6370, plain, (v1_relat_1(k7_relat_1('#skF_6', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_6368, c_6172])).
% 11.97/4.80  tff(c_28, plain, (![A_24]: (k2_relat_1(A_24)!=k1_xboole_0 | k1_xboole_0=A_24 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.97/4.80  tff(c_6392, plain, (k2_relat_1(k7_relat_1('#skF_6', k1_xboole_0))!=k1_xboole_0 | k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6370, c_28])).
% 11.97/4.80  tff(c_6504, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6419, c_6392])).
% 11.97/4.80  tff(c_6393, plain, (k1_relat_1(k7_relat_1('#skF_6', k1_xboole_0))!=k1_xboole_0 | k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6370, c_30])).
% 11.97/4.80  tff(c_6493, plain, (k1_relat_1(k7_relat_1('#skF_6', k1_xboole_0))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_6393])).
% 11.97/4.80  tff(c_6505, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6504, c_6493])).
% 11.97/4.80  tff(c_6512, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_6505])).
% 11.97/4.80  tff(c_6513, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_6393])).
% 11.97/4.80  tff(c_6517, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6513, c_6371])).
% 11.97/4.80  tff(c_6240, plain, (![D_798, E_800, F_796, B_801, A_797, C_799]: (v1_funct_1(k1_tmap_1(A_797, B_801, C_799, D_798, E_800, F_796)) | ~m1_subset_1(F_796, k1_zfmisc_1(k2_zfmisc_1(D_798, B_801))) | ~v1_funct_2(F_796, D_798, B_801) | ~v1_funct_1(F_796) | ~m1_subset_1(E_800, k1_zfmisc_1(k2_zfmisc_1(C_799, B_801))) | ~v1_funct_2(E_800, C_799, B_801) | ~v1_funct_1(E_800) | ~m1_subset_1(D_798, k1_zfmisc_1(A_797)) | v1_xboole_0(D_798) | ~m1_subset_1(C_799, k1_zfmisc_1(A_797)) | v1_xboole_0(C_799) | v1_xboole_0(B_801) | v1_xboole_0(A_797))), inference(cnfTransformation, [status(thm)], [f_224])).
% 11.97/4.80  tff(c_6242, plain, (![A_797, C_799, E_800]: (v1_funct_1(k1_tmap_1(A_797, '#skF_3', C_799, '#skF_5', E_800, '#skF_7')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_800, k1_zfmisc_1(k2_zfmisc_1(C_799, '#skF_3'))) | ~v1_funct_2(E_800, C_799, '#skF_3') | ~v1_funct_1(E_800) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_797)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_799, k1_zfmisc_1(A_797)) | v1_xboole_0(C_799) | v1_xboole_0('#skF_3') | v1_xboole_0(A_797))), inference(resolution, [status(thm)], [c_72, c_6240])).
% 11.97/4.80  tff(c_6247, plain, (![A_797, C_799, E_800]: (v1_funct_1(k1_tmap_1(A_797, '#skF_3', C_799, '#skF_5', E_800, '#skF_7')) | ~m1_subset_1(E_800, k1_zfmisc_1(k2_zfmisc_1(C_799, '#skF_3'))) | ~v1_funct_2(E_800, C_799, '#skF_3') | ~v1_funct_1(E_800) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_797)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_799, k1_zfmisc_1(A_797)) | v1_xboole_0(C_799) | v1_xboole_0('#skF_3') | v1_xboole_0(A_797))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_6242])).
% 11.97/4.80  tff(c_6287, plain, (![A_803, C_804, E_805]: (v1_funct_1(k1_tmap_1(A_803, '#skF_3', C_804, '#skF_5', E_805, '#skF_7')) | ~m1_subset_1(E_805, k1_zfmisc_1(k2_zfmisc_1(C_804, '#skF_3'))) | ~v1_funct_2(E_805, C_804, '#skF_3') | ~v1_funct_1(E_805) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_803)) | ~m1_subset_1(C_804, k1_zfmisc_1(A_803)) | v1_xboole_0(C_804) | v1_xboole_0(A_803))), inference(negUnitSimplification, [status(thm)], [c_94, c_88, c_6247])).
% 11.97/4.80  tff(c_6291, plain, (![A_803]: (v1_funct_1(k1_tmap_1(A_803, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_803)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_803)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_803))), inference(resolution, [status(thm)], [c_78, c_6287])).
% 11.97/4.80  tff(c_6298, plain, (![A_803]: (v1_funct_1(k1_tmap_1(A_803, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_803)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_803)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_803))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_6291])).
% 11.97/4.80  tff(c_6485, plain, (![A_824]: (v1_funct_1(k1_tmap_1(A_824, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_824)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_824)) | v1_xboole_0(A_824))), inference(negUnitSimplification, [status(thm)], [c_92, c_6298])).
% 11.97/4.80  tff(c_6488, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_86, c_6485])).
% 11.97/4.80  tff(c_6491, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_6488])).
% 11.97/4.80  tff(c_6492, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_96, c_6491])).
% 11.97/4.80  tff(c_6636, plain, (![A_835, F_836, E_840, B_838, C_837, D_839]: (k2_partfun1(k4_subset_1(A_835, C_837, D_839), B_838, k1_tmap_1(A_835, B_838, C_837, D_839, E_840, F_836), D_839)=F_836 | ~m1_subset_1(k1_tmap_1(A_835, B_838, C_837, D_839, E_840, F_836), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_835, C_837, D_839), B_838))) | ~v1_funct_2(k1_tmap_1(A_835, B_838, C_837, D_839, E_840, F_836), k4_subset_1(A_835, C_837, D_839), B_838) | ~v1_funct_1(k1_tmap_1(A_835, B_838, C_837, D_839, E_840, F_836)) | k2_partfun1(D_839, B_838, F_836, k9_subset_1(A_835, C_837, D_839))!=k2_partfun1(C_837, B_838, E_840, k9_subset_1(A_835, C_837, D_839)) | ~m1_subset_1(F_836, k1_zfmisc_1(k2_zfmisc_1(D_839, B_838))) | ~v1_funct_2(F_836, D_839, B_838) | ~v1_funct_1(F_836) | ~m1_subset_1(E_840, k1_zfmisc_1(k2_zfmisc_1(C_837, B_838))) | ~v1_funct_2(E_840, C_837, B_838) | ~v1_funct_1(E_840) | ~m1_subset_1(D_839, k1_zfmisc_1(A_835)) | v1_xboole_0(D_839) | ~m1_subset_1(C_837, k1_zfmisc_1(A_835)) | v1_xboole_0(C_837) | v1_xboole_0(B_838) | v1_xboole_0(A_835))), inference(cnfTransformation, [status(thm)], [f_190])).
% 11.97/4.80  tff(c_10044, plain, (![D_991, F_989, C_992, B_994, A_990, E_993]: (k2_partfun1(k4_subset_1(A_990, C_992, D_991), B_994, k1_tmap_1(A_990, B_994, C_992, D_991, E_993, F_989), D_991)=F_989 | ~v1_funct_2(k1_tmap_1(A_990, B_994, C_992, D_991, E_993, F_989), k4_subset_1(A_990, C_992, D_991), B_994) | ~v1_funct_1(k1_tmap_1(A_990, B_994, C_992, D_991, E_993, F_989)) | k2_partfun1(D_991, B_994, F_989, k9_subset_1(A_990, C_992, D_991))!=k2_partfun1(C_992, B_994, E_993, k9_subset_1(A_990, C_992, D_991)) | ~m1_subset_1(F_989, k1_zfmisc_1(k2_zfmisc_1(D_991, B_994))) | ~v1_funct_2(F_989, D_991, B_994) | ~v1_funct_1(F_989) | ~m1_subset_1(E_993, k1_zfmisc_1(k2_zfmisc_1(C_992, B_994))) | ~v1_funct_2(E_993, C_992, B_994) | ~v1_funct_1(E_993) | ~m1_subset_1(D_991, k1_zfmisc_1(A_990)) | v1_xboole_0(D_991) | ~m1_subset_1(C_992, k1_zfmisc_1(A_990)) | v1_xboole_0(C_992) | v1_xboole_0(B_994) | v1_xboole_0(A_990))), inference(resolution, [status(thm)], [c_64, c_6636])).
% 11.97/4.80  tff(c_12754, plain, (![A_1064, C_1066, F_1063, B_1068, E_1067, D_1065]: (k2_partfun1(k4_subset_1(A_1064, C_1066, D_1065), B_1068, k1_tmap_1(A_1064, B_1068, C_1066, D_1065, E_1067, F_1063), D_1065)=F_1063 | ~v1_funct_1(k1_tmap_1(A_1064, B_1068, C_1066, D_1065, E_1067, F_1063)) | k2_partfun1(D_1065, B_1068, F_1063, k9_subset_1(A_1064, C_1066, D_1065))!=k2_partfun1(C_1066, B_1068, E_1067, k9_subset_1(A_1064, C_1066, D_1065)) | ~m1_subset_1(F_1063, k1_zfmisc_1(k2_zfmisc_1(D_1065, B_1068))) | ~v1_funct_2(F_1063, D_1065, B_1068) | ~v1_funct_1(F_1063) | ~m1_subset_1(E_1067, k1_zfmisc_1(k2_zfmisc_1(C_1066, B_1068))) | ~v1_funct_2(E_1067, C_1066, B_1068) | ~v1_funct_1(E_1067) | ~m1_subset_1(D_1065, k1_zfmisc_1(A_1064)) | v1_xboole_0(D_1065) | ~m1_subset_1(C_1066, k1_zfmisc_1(A_1064)) | v1_xboole_0(C_1066) | v1_xboole_0(B_1068) | v1_xboole_0(A_1064))), inference(resolution, [status(thm)], [c_66, c_10044])).
% 11.97/4.80  tff(c_12758, plain, (![A_1064, C_1066, E_1067]: (k2_partfun1(k4_subset_1(A_1064, C_1066, '#skF_5'), '#skF_3', k1_tmap_1(A_1064, '#skF_3', C_1066, '#skF_5', E_1067, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1064, '#skF_3', C_1066, '#skF_5', E_1067, '#skF_7')) | k2_partfun1(C_1066, '#skF_3', E_1067, k9_subset_1(A_1064, C_1066, '#skF_5'))!=k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1(A_1064, C_1066, '#skF_5')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_1067, k1_zfmisc_1(k2_zfmisc_1(C_1066, '#skF_3'))) | ~v1_funct_2(E_1067, C_1066, '#skF_3') | ~v1_funct_1(E_1067) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1064)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1066, k1_zfmisc_1(A_1064)) | v1_xboole_0(C_1066) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1064))), inference(resolution, [status(thm)], [c_72, c_12754])).
% 11.97/4.80  tff(c_12764, plain, (![A_1064, C_1066, E_1067]: (k2_partfun1(k4_subset_1(A_1064, C_1066, '#skF_5'), '#skF_3', k1_tmap_1(A_1064, '#skF_3', C_1066, '#skF_5', E_1067, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1064, '#skF_3', C_1066, '#skF_5', E_1067, '#skF_7')) | k2_partfun1(C_1066, '#skF_3', E_1067, k9_subset_1(A_1064, C_1066, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_1064, C_1066, '#skF_5')) | ~m1_subset_1(E_1067, k1_zfmisc_1(k2_zfmisc_1(C_1066, '#skF_3'))) | ~v1_funct_2(E_1067, C_1066, '#skF_3') | ~v1_funct_1(E_1067) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1064)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1066, k1_zfmisc_1(A_1064)) | v1_xboole_0(C_1066) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1064))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_6018, c_12758])).
% 11.97/4.80  tff(c_14448, plain, (![A_1115, C_1116, E_1117]: (k2_partfun1(k4_subset_1(A_1115, C_1116, '#skF_5'), '#skF_3', k1_tmap_1(A_1115, '#skF_3', C_1116, '#skF_5', E_1117, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1115, '#skF_3', C_1116, '#skF_5', E_1117, '#skF_7')) | k2_partfun1(C_1116, '#skF_3', E_1117, k9_subset_1(A_1115, C_1116, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_1115, C_1116, '#skF_5')) | ~m1_subset_1(E_1117, k1_zfmisc_1(k2_zfmisc_1(C_1116, '#skF_3'))) | ~v1_funct_2(E_1117, C_1116, '#skF_3') | ~v1_funct_1(E_1117) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1115)) | ~m1_subset_1(C_1116, k1_zfmisc_1(A_1115)) | v1_xboole_0(C_1116) | v1_xboole_0(A_1115))), inference(negUnitSimplification, [status(thm)], [c_94, c_88, c_12764])).
% 11.97/4.80  tff(c_14455, plain, (![A_1115]: (k2_partfun1(k4_subset_1(A_1115, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_1115, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1115, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1(A_1115, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_1115, '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1115)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1115)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1115))), inference(resolution, [status(thm)], [c_78, c_14448])).
% 11.97/4.80  tff(c_14465, plain, (![A_1115]: (k2_partfun1(k4_subset_1(A_1115, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_1115, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1115, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_1115, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_1115, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1115)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1115)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1115))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_6021, c_14455])).
% 11.97/4.80  tff(c_16343, plain, (![A_1143]: (k2_partfun1(k4_subset_1(A_1143, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_1143, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1143, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_1143, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_1143, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1143)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1143)) | v1_xboole_0(A_1143))), inference(negUnitSimplification, [status(thm)], [c_92, c_14465])).
% 11.97/4.80  tff(c_3774, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_70])).
% 11.97/4.80  tff(c_4294, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')!='#skF_7'), inference(splitLeft, [status(thm)], [c_3774])).
% 11.97/4.80  tff(c_16354, plain, (~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_16343, c_4294])).
% 11.97/4.80  tff(c_16368, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_6513, c_6368, c_5786, c_6517, c_6368, c_5786, c_6492, c_16354])).
% 11.97/4.80  tff(c_16370, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_16368])).
% 11.97/4.80  tff(c_16371, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_3774])).
% 11.97/4.80  tff(c_26220, plain, (~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_26211, c_16371])).
% 11.97/4.80  tff(c_26231, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_18713, c_18629, c_16502, c_18721, c_18629, c_16502, c_18926, c_26220])).
% 11.97/4.80  tff(c_26233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_26231])).
% 11.97/4.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.97/4.80  
% 11.97/4.80  Inference rules
% 11.97/4.80  ----------------------
% 11.97/4.80  #Ref     : 0
% 11.97/4.80  #Sup     : 5358
% 11.97/4.80  #Fact    : 0
% 11.97/4.80  #Define  : 0
% 11.97/4.80  #Split   : 90
% 11.97/4.80  #Chain   : 0
% 11.97/4.80  #Close   : 0
% 11.97/4.80  
% 11.97/4.80  Ordering : KBO
% 11.97/4.80  
% 11.97/4.80  Simplification rules
% 11.97/4.80  ----------------------
% 11.97/4.80  #Subsume      : 848
% 11.97/4.80  #Demod        : 10208
% 11.97/4.80  #Tautology    : 3226
% 11.97/4.80  #SimpNegUnit  : 421
% 11.97/4.80  #BackRed      : 118
% 11.97/4.80  
% 11.97/4.80  #Partial instantiations: 0
% 11.97/4.80  #Strategies tried      : 1
% 11.97/4.80  
% 11.97/4.80  Timing (in seconds)
% 11.97/4.80  ----------------------
% 11.97/4.81  Preprocessing        : 0.46
% 11.97/4.81  Parsing              : 0.22
% 11.97/4.81  CNF conversion       : 0.06
% 11.97/4.81  Main loop            : 3.47
% 11.97/4.81  Inferencing          : 1.01
% 11.97/4.81  Reduction            : 1.43
% 11.97/4.81  Demodulation         : 1.07
% 11.97/4.81  BG Simplification    : 0.10
% 11.97/4.81  Subsumption          : 0.73
% 11.97/4.81  Abstraction          : 0.12
% 11.97/4.81  MUC search           : 0.00
% 11.97/4.81  Cooper               : 0.00
% 11.97/4.81  Total                : 4.06
% 11.97/4.81  Index Insertion      : 0.00
% 11.97/4.81  Index Deletion       : 0.00
% 11.97/4.81  Index Matching       : 0.00
% 11.97/4.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
