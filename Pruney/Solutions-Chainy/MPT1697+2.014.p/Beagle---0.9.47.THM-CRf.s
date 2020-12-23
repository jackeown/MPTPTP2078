%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:10 EST 2020

% Result     : Theorem 27.21s
% Output     : CNFRefutation 27.65s
% Verified   : 
% Statistics : Number of formulae       :  590 (7538 expanded)
%              Number of leaves         :   54 (2516 expanded)
%              Depth                    :   27
%              Number of atoms          : 1907 (32958 expanded)
%              Number of equality atoms :  418 (7741 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff(f_260,negated_conjecture,(
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

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_62,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_108,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_130,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_122,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

tff(f_88,axiom,(
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

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_218,axiom,(
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

tff(f_136,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_184,axiom,(
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

tff(c_92,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_86,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_82,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_88,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_90,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_74,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_6969,plain,(
    ! [C_806,A_807,B_808] :
      ( v1_relat_1(C_806)
      | ~ m1_subset_1(C_806,k1_zfmisc_1(k2_zfmisc_1(A_807,B_808))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_6977,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_6969])).

tff(c_84,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_6620,plain,(
    ! [C_762,A_763,B_764] :
      ( v1_relat_1(C_762)
      | ~ m1_subset_1(C_762,k1_zfmisc_1(k2_zfmisc_1(A_763,B_764))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_6628,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_6620])).

tff(c_24,plain,(
    ! [A_19] :
      ( k1_relat_1(A_19) != k1_xboole_0
      | k1_xboole_0 = A_19
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6643,plain,
    ( k1_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_6628,c_24])).

tff(c_6658,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_6643])).

tff(c_20,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_104,plain,(
    ! [A_237] :
      ( k7_relat_1(A_237,k1_relat_1(A_237)) = A_237
      | ~ v1_relat_1(A_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_116,plain,
    ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_104])).

tff(c_6551,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_40,plain,(
    ! [A_31] :
      ( r1_xboole_0('#skF_1'(A_31),A_31)
      | k1_xboole_0 = A_31 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_6682,plain,(
    ! [A_773,B_774] :
      ( k7_relat_1(A_773,B_774) = k1_xboole_0
      | ~ r1_xboole_0(B_774,k1_relat_1(A_773))
      | ~ v1_relat_1(A_773) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6818,plain,(
    ! [A_793] :
      ( k7_relat_1(A_793,'#skF_1'(k1_relat_1(A_793))) = k1_xboole_0
      | ~ v1_relat_1(A_793)
      | k1_relat_1(A_793) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_6682])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( v1_relat_1(k7_relat_1(A_11,B_12))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6834,plain,(
    ! [A_793] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_793)
      | ~ v1_relat_1(A_793)
      | k1_relat_1(A_793) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6818,c_12])).

tff(c_6850,plain,(
    ! [A_794] :
      ( ~ v1_relat_1(A_794)
      | ~ v1_relat_1(A_794)
      | k1_relat_1(A_794) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_6551,c_6834])).

tff(c_6852,plain,
    ( ~ v1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6628,c_6850])).

tff(c_6859,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6628,c_6852])).

tff(c_6861,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6658,c_6859])).

tff(c_6862,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_6643])).

tff(c_6872,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6862,c_6551])).

tff(c_6879,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6628,c_6872])).

tff(c_6880,plain,(
    k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_7017,plain,(
    ! [C_814,A_815,B_816] :
      ( v4_relat_1(C_814,A_815)
      | ~ m1_subset_1(C_814,k1_zfmisc_1(k2_zfmisc_1(A_815,B_816))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_7025,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_7017])).

tff(c_7192,plain,(
    ! [B_835,A_836] :
      ( k1_relat_1(B_835) = A_836
      | ~ v1_partfun1(B_835,A_836)
      | ~ v4_relat_1(B_835,A_836)
      | ~ v1_relat_1(B_835) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_7195,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_7025,c_7192])).

tff(c_7201,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6977,c_7195])).

tff(c_7205,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_7201])).

tff(c_78,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_76,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_7738,plain,(
    ! [C_871,A_872,B_873] :
      ( v1_partfun1(C_871,A_872)
      | ~ v1_funct_2(C_871,A_872,B_873)
      | ~ v1_funct_1(C_871)
      | ~ m1_subset_1(C_871,k1_zfmisc_1(k2_zfmisc_1(A_872,B_873)))
      | v1_xboole_0(B_873) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_7744,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_7738])).

tff(c_7751,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_7744])).

tff(c_7753,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_7205,c_7751])).

tff(c_7754,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_7201])).

tff(c_6993,plain,
    ( k1_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_6977,c_24])).

tff(c_6996,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_6993])).

tff(c_7756,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7754,c_6996])).

tff(c_16,plain,(
    ! [A_16,B_18] :
      ( k7_relat_1(A_16,B_18) = k1_xboole_0
      | ~ r1_xboole_0(B_18,k1_relat_1(A_16))
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_7769,plain,(
    ! [B_18] :
      ( k7_relat_1('#skF_6',B_18) = k1_xboole_0
      | ~ r1_xboole_0(B_18,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7754,c_16])).

tff(c_8092,plain,(
    ! [B_891] :
      ( k7_relat_1('#skF_6',B_891) = k1_xboole_0
      | ~ r1_xboole_0(B_891,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6977,c_7769])).

tff(c_8104,plain,
    ( k7_relat_1('#skF_6','#skF_1'('#skF_4')) = k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_8092])).

tff(c_8111,plain,(
    k7_relat_1('#skF_6','#skF_1'('#skF_4')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_7756,c_8104])).

tff(c_26,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_21,A_20)),A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_8115,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),'#skF_1'('#skF_4'))
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_8111,c_26])).

tff(c_8122,plain,(
    r1_tarski(k1_xboole_0,'#skF_1'('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6977,c_20,c_8115])).

tff(c_8126,plain,(
    ! [C_892,B_893,A_894] :
      ( k7_relat_1(k7_relat_1(C_892,B_893),A_894) = k7_relat_1(C_892,A_894)
      | ~ r1_tarski(A_894,B_893)
      | ~ v1_relat_1(C_892) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8151,plain,(
    ! [A_894] :
      ( k7_relat_1(k1_xboole_0,A_894) = k7_relat_1('#skF_6',A_894)
      | ~ r1_tarski(A_894,'#skF_1'('#skF_4'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8111,c_8126])).

tff(c_8586,plain,(
    ! [A_923] :
      ( k7_relat_1(k1_xboole_0,A_923) = k7_relat_1('#skF_6',A_923)
      | ~ r1_tarski(A_923,'#skF_1'('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6977,c_8151])).

tff(c_8597,plain,(
    k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8122,c_8586])).

tff(c_8611,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6880,c_8597])).

tff(c_80,plain,(
    r1_subset_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_7114,plain,(
    ! [A_824,B_825] :
      ( r1_xboole_0(A_824,B_825)
      | ~ r1_subset_1(A_824,B_825)
      | v1_xboole_0(B_825)
      | v1_xboole_0(A_824) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8930,plain,(
    ! [A_939,B_940] :
      ( k3_xboole_0(A_939,B_940) = k1_xboole_0
      | ~ r1_subset_1(A_939,B_940)
      | v1_xboole_0(B_940)
      | v1_xboole_0(A_939) ) ),
    inference(resolution,[status(thm)],[c_7114,c_2])).

tff(c_8936,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_8930])).

tff(c_8940,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_84,c_8936])).

tff(c_68,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_6976,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_6969])).

tff(c_32,plain,(
    ! [A_23,B_24] :
      ( r1_xboole_0(A_23,B_24)
      | ~ r1_subset_1(A_23,B_24)
      | v1_xboole_0(B_24)
      | v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_7024,plain,(
    v4_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_7017])).

tff(c_7198,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_7024,c_7192])).

tff(c_7204,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6976,c_7198])).

tff(c_7806,plain,(
    ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_7204])).

tff(c_72,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_70,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_8032,plain,(
    ! [C_888,A_889,B_890] :
      ( v1_partfun1(C_888,A_889)
      | ~ v1_funct_2(C_888,A_889,B_890)
      | ~ v1_funct_1(C_888)
      | ~ m1_subset_1(C_888,k1_zfmisc_1(k2_zfmisc_1(A_889,B_890)))
      | v1_xboole_0(B_890) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_8035,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_8032])).

tff(c_8041,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_8035])).

tff(c_8043,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_7806,c_8041])).

tff(c_8044,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_7204])).

tff(c_8059,plain,(
    ! [B_18] :
      ( k7_relat_1('#skF_7',B_18) = k1_xboole_0
      | ~ r1_xboole_0(B_18,'#skF_5')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8044,c_16])).

tff(c_8188,plain,(
    ! [B_895] :
      ( k7_relat_1('#skF_7',B_895) = k1_xboole_0
      | ~ r1_xboole_0(B_895,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6976,c_8059])).

tff(c_8192,plain,(
    ! [A_23] :
      ( k7_relat_1('#skF_7',A_23) = k1_xboole_0
      | ~ r1_subset_1(A_23,'#skF_5')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_23) ) ),
    inference(resolution,[status(thm)],[c_32,c_8188])).

tff(c_8291,plain,(
    ! [A_903] :
      ( k7_relat_1('#skF_7',A_903) = k1_xboole_0
      | ~ r1_subset_1(A_903,'#skF_5')
      | v1_xboole_0(A_903) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_8192])).

tff(c_8294,plain,
    ( k7_relat_1('#skF_7','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_8291])).

tff(c_8297,plain,(
    k7_relat_1('#skF_7','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_8294])).

tff(c_8307,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),'#skF_4')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_8297,c_26])).

tff(c_8320,plain,(
    r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6976,c_20,c_8307])).

tff(c_14,plain,(
    ! [C_15,B_14,A_13] :
      ( k7_relat_1(k7_relat_1(C_15,B_14),A_13) = k7_relat_1(C_15,A_13)
      | ~ r1_tarski(A_13,B_14)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8304,plain,(
    ! [A_13] :
      ( k7_relat_1(k1_xboole_0,A_13) = k7_relat_1('#skF_7',A_13)
      | ~ r1_tarski(A_13,'#skF_4')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8297,c_14])).

tff(c_8410,plain,(
    ! [A_910] :
      ( k7_relat_1(k1_xboole_0,A_910) = k7_relat_1('#skF_7',A_910)
      | ~ r1_tarski(A_910,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6976,c_8304])).

tff(c_8413,plain,(
    k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8320,c_8410])).

tff(c_8430,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6880,c_8413])).

tff(c_7142,plain,(
    ! [A_828,B_829,C_830] :
      ( k9_subset_1(A_828,B_829,C_830) = k3_xboole_0(B_829,C_830)
      | ~ m1_subset_1(C_830,k1_zfmisc_1(A_828)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_7154,plain,(
    ! [B_829] : k9_subset_1('#skF_2',B_829,'#skF_5') = k3_xboole_0(B_829,'#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_7142])).

tff(c_8500,plain,(
    ! [C_915,F_917,D_914,A_912,E_913,B_916] :
      ( v1_funct_1(k1_tmap_1(A_912,B_916,C_915,D_914,E_913,F_917))
      | ~ m1_subset_1(F_917,k1_zfmisc_1(k2_zfmisc_1(D_914,B_916)))
      | ~ v1_funct_2(F_917,D_914,B_916)
      | ~ v1_funct_1(F_917)
      | ~ m1_subset_1(E_913,k1_zfmisc_1(k2_zfmisc_1(C_915,B_916)))
      | ~ v1_funct_2(E_913,C_915,B_916)
      | ~ v1_funct_1(E_913)
      | ~ m1_subset_1(D_914,k1_zfmisc_1(A_912))
      | v1_xboole_0(D_914)
      | ~ m1_subset_1(C_915,k1_zfmisc_1(A_912))
      | v1_xboole_0(C_915)
      | v1_xboole_0(B_916)
      | v1_xboole_0(A_912) ) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_8502,plain,(
    ! [A_912,C_915,E_913] :
      ( v1_funct_1(k1_tmap_1(A_912,'#skF_3',C_915,'#skF_5',E_913,'#skF_7'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_913,k1_zfmisc_1(k2_zfmisc_1(C_915,'#skF_3')))
      | ~ v1_funct_2(E_913,C_915,'#skF_3')
      | ~ v1_funct_1(E_913)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_912))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_915,k1_zfmisc_1(A_912))
      | v1_xboole_0(C_915)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_912) ) ),
    inference(resolution,[status(thm)],[c_68,c_8500])).

tff(c_8507,plain,(
    ! [A_912,C_915,E_913] :
      ( v1_funct_1(k1_tmap_1(A_912,'#skF_3',C_915,'#skF_5',E_913,'#skF_7'))
      | ~ m1_subset_1(E_913,k1_zfmisc_1(k2_zfmisc_1(C_915,'#skF_3')))
      | ~ v1_funct_2(E_913,C_915,'#skF_3')
      | ~ v1_funct_1(E_913)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_912))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_915,k1_zfmisc_1(A_912))
      | v1_xboole_0(C_915)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_912) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_8502])).

tff(c_9245,plain,(
    ! [A_960,C_961,E_962] :
      ( v1_funct_1(k1_tmap_1(A_960,'#skF_3',C_961,'#skF_5',E_962,'#skF_7'))
      | ~ m1_subset_1(E_962,k1_zfmisc_1(k2_zfmisc_1(C_961,'#skF_3')))
      | ~ v1_funct_2(E_962,C_961,'#skF_3')
      | ~ v1_funct_1(E_962)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_960))
      | ~ m1_subset_1(C_961,k1_zfmisc_1(A_960))
      | v1_xboole_0(C_961)
      | v1_xboole_0(A_960) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_8507])).

tff(c_9252,plain,(
    ! [A_960] :
      ( v1_funct_1(k1_tmap_1(A_960,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_960))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_960))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_960) ) ),
    inference(resolution,[status(thm)],[c_74,c_9245])).

tff(c_9262,plain,(
    ! [A_960] :
      ( v1_funct_1(k1_tmap_1(A_960,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_960))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_960))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_960) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_9252])).

tff(c_9951,plain,(
    ! [A_987] :
      ( v1_funct_1(k1_tmap_1(A_987,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_987))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_987))
      | v1_xboole_0(A_987) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_9262])).

tff(c_9954,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_9951])).

tff(c_9957,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_9954])).

tff(c_9958,plain,(
    v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_9957])).

tff(c_8279,plain,(
    ! [A_898,B_899,C_900,D_901] :
      ( k2_partfun1(A_898,B_899,C_900,D_901) = k7_relat_1(C_900,D_901)
      | ~ m1_subset_1(C_900,k1_zfmisc_1(k2_zfmisc_1(A_898,B_899)))
      | ~ v1_funct_1(C_900) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_8283,plain,(
    ! [D_901] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_6',D_901) = k7_relat_1('#skF_6',D_901)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_74,c_8279])).

tff(c_8289,plain,(
    ! [D_901] : k2_partfun1('#skF_4','#skF_3','#skF_6',D_901) = k7_relat_1('#skF_6',D_901) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_8283])).

tff(c_8281,plain,(
    ! [D_901] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_7',D_901) = k7_relat_1('#skF_7',D_901)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_68,c_8279])).

tff(c_8286,plain,(
    ! [D_901] : k2_partfun1('#skF_5','#skF_3','#skF_7',D_901) = k7_relat_1('#skF_7',D_901) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_8281])).

tff(c_62,plain,(
    ! [A_170,D_173,E_174,B_171,C_172,F_175] :
      ( v1_funct_2(k1_tmap_1(A_170,B_171,C_172,D_173,E_174,F_175),k4_subset_1(A_170,C_172,D_173),B_171)
      | ~ m1_subset_1(F_175,k1_zfmisc_1(k2_zfmisc_1(D_173,B_171)))
      | ~ v1_funct_2(F_175,D_173,B_171)
      | ~ v1_funct_1(F_175)
      | ~ m1_subset_1(E_174,k1_zfmisc_1(k2_zfmisc_1(C_172,B_171)))
      | ~ v1_funct_2(E_174,C_172,B_171)
      | ~ v1_funct_1(E_174)
      | ~ m1_subset_1(D_173,k1_zfmisc_1(A_170))
      | v1_xboole_0(D_173)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(A_170))
      | v1_xboole_0(C_172)
      | v1_xboole_0(B_171)
      | v1_xboole_0(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_60,plain,(
    ! [A_170,D_173,E_174,B_171,C_172,F_175] :
      ( m1_subset_1(k1_tmap_1(A_170,B_171,C_172,D_173,E_174,F_175),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_170,C_172,D_173),B_171)))
      | ~ m1_subset_1(F_175,k1_zfmisc_1(k2_zfmisc_1(D_173,B_171)))
      | ~ v1_funct_2(F_175,D_173,B_171)
      | ~ v1_funct_1(F_175)
      | ~ m1_subset_1(E_174,k1_zfmisc_1(k2_zfmisc_1(C_172,B_171)))
      | ~ v1_funct_2(E_174,C_172,B_171)
      | ~ v1_funct_1(E_174)
      | ~ m1_subset_1(D_173,k1_zfmisc_1(A_170))
      | v1_xboole_0(D_173)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(A_170))
      | v1_xboole_0(C_172)
      | v1_xboole_0(B_171)
      | v1_xboole_0(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_9508,plain,(
    ! [C_971,E_972,A_969,F_967,B_970,D_968] :
      ( k2_partfun1(k4_subset_1(A_969,C_971,D_968),B_970,k1_tmap_1(A_969,B_970,C_971,D_968,E_972,F_967),D_968) = F_967
      | ~ m1_subset_1(k1_tmap_1(A_969,B_970,C_971,D_968,E_972,F_967),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_969,C_971,D_968),B_970)))
      | ~ v1_funct_2(k1_tmap_1(A_969,B_970,C_971,D_968,E_972,F_967),k4_subset_1(A_969,C_971,D_968),B_970)
      | ~ v1_funct_1(k1_tmap_1(A_969,B_970,C_971,D_968,E_972,F_967))
      | k2_partfun1(D_968,B_970,F_967,k9_subset_1(A_969,C_971,D_968)) != k2_partfun1(C_971,B_970,E_972,k9_subset_1(A_969,C_971,D_968))
      | ~ m1_subset_1(F_967,k1_zfmisc_1(k2_zfmisc_1(D_968,B_970)))
      | ~ v1_funct_2(F_967,D_968,B_970)
      | ~ v1_funct_1(F_967)
      | ~ m1_subset_1(E_972,k1_zfmisc_1(k2_zfmisc_1(C_971,B_970)))
      | ~ v1_funct_2(E_972,C_971,B_970)
      | ~ v1_funct_1(E_972)
      | ~ m1_subset_1(D_968,k1_zfmisc_1(A_969))
      | v1_xboole_0(D_968)
      | ~ m1_subset_1(C_971,k1_zfmisc_1(A_969))
      | v1_xboole_0(C_971)
      | v1_xboole_0(B_970)
      | v1_xboole_0(A_969) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_15562,plain,(
    ! [A_1140,D_1142,F_1145,C_1143,E_1141,B_1144] :
      ( k2_partfun1(k4_subset_1(A_1140,C_1143,D_1142),B_1144,k1_tmap_1(A_1140,B_1144,C_1143,D_1142,E_1141,F_1145),D_1142) = F_1145
      | ~ v1_funct_2(k1_tmap_1(A_1140,B_1144,C_1143,D_1142,E_1141,F_1145),k4_subset_1(A_1140,C_1143,D_1142),B_1144)
      | ~ v1_funct_1(k1_tmap_1(A_1140,B_1144,C_1143,D_1142,E_1141,F_1145))
      | k2_partfun1(D_1142,B_1144,F_1145,k9_subset_1(A_1140,C_1143,D_1142)) != k2_partfun1(C_1143,B_1144,E_1141,k9_subset_1(A_1140,C_1143,D_1142))
      | ~ m1_subset_1(F_1145,k1_zfmisc_1(k2_zfmisc_1(D_1142,B_1144)))
      | ~ v1_funct_2(F_1145,D_1142,B_1144)
      | ~ v1_funct_1(F_1145)
      | ~ m1_subset_1(E_1141,k1_zfmisc_1(k2_zfmisc_1(C_1143,B_1144)))
      | ~ v1_funct_2(E_1141,C_1143,B_1144)
      | ~ v1_funct_1(E_1141)
      | ~ m1_subset_1(D_1142,k1_zfmisc_1(A_1140))
      | v1_xboole_0(D_1142)
      | ~ m1_subset_1(C_1143,k1_zfmisc_1(A_1140))
      | v1_xboole_0(C_1143)
      | v1_xboole_0(B_1144)
      | v1_xboole_0(A_1140) ) ),
    inference(resolution,[status(thm)],[c_60,c_9508])).

tff(c_34392,plain,(
    ! [E_1347,F_1351,B_1350,C_1349,A_1346,D_1348] :
      ( k2_partfun1(k4_subset_1(A_1346,C_1349,D_1348),B_1350,k1_tmap_1(A_1346,B_1350,C_1349,D_1348,E_1347,F_1351),D_1348) = F_1351
      | ~ v1_funct_1(k1_tmap_1(A_1346,B_1350,C_1349,D_1348,E_1347,F_1351))
      | k2_partfun1(D_1348,B_1350,F_1351,k9_subset_1(A_1346,C_1349,D_1348)) != k2_partfun1(C_1349,B_1350,E_1347,k9_subset_1(A_1346,C_1349,D_1348))
      | ~ m1_subset_1(F_1351,k1_zfmisc_1(k2_zfmisc_1(D_1348,B_1350)))
      | ~ v1_funct_2(F_1351,D_1348,B_1350)
      | ~ v1_funct_1(F_1351)
      | ~ m1_subset_1(E_1347,k1_zfmisc_1(k2_zfmisc_1(C_1349,B_1350)))
      | ~ v1_funct_2(E_1347,C_1349,B_1350)
      | ~ v1_funct_1(E_1347)
      | ~ m1_subset_1(D_1348,k1_zfmisc_1(A_1346))
      | v1_xboole_0(D_1348)
      | ~ m1_subset_1(C_1349,k1_zfmisc_1(A_1346))
      | v1_xboole_0(C_1349)
      | v1_xboole_0(B_1350)
      | v1_xboole_0(A_1346) ) ),
    inference(resolution,[status(thm)],[c_62,c_15562])).

tff(c_34396,plain,(
    ! [A_1346,C_1349,E_1347] :
      ( k2_partfun1(k4_subset_1(A_1346,C_1349,'#skF_5'),'#skF_3',k1_tmap_1(A_1346,'#skF_3',C_1349,'#skF_5',E_1347,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1346,'#skF_3',C_1349,'#skF_5',E_1347,'#skF_7'))
      | k2_partfun1(C_1349,'#skF_3',E_1347,k9_subset_1(A_1346,C_1349,'#skF_5')) != k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1(A_1346,C_1349,'#skF_5'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_1347,k1_zfmisc_1(k2_zfmisc_1(C_1349,'#skF_3')))
      | ~ v1_funct_2(E_1347,C_1349,'#skF_3')
      | ~ v1_funct_1(E_1347)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1346))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1349,k1_zfmisc_1(A_1346))
      | v1_xboole_0(C_1349)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1346) ) ),
    inference(resolution,[status(thm)],[c_68,c_34392])).

tff(c_34402,plain,(
    ! [A_1346,C_1349,E_1347] :
      ( k2_partfun1(k4_subset_1(A_1346,C_1349,'#skF_5'),'#skF_3',k1_tmap_1(A_1346,'#skF_3',C_1349,'#skF_5',E_1347,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1346,'#skF_3',C_1349,'#skF_5',E_1347,'#skF_7'))
      | k2_partfun1(C_1349,'#skF_3',E_1347,k9_subset_1(A_1346,C_1349,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_1346,C_1349,'#skF_5'))
      | ~ m1_subset_1(E_1347,k1_zfmisc_1(k2_zfmisc_1(C_1349,'#skF_3')))
      | ~ v1_funct_2(E_1347,C_1349,'#skF_3')
      | ~ v1_funct_1(E_1347)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1346))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1349,k1_zfmisc_1(A_1346))
      | v1_xboole_0(C_1349)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1346) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_8286,c_34396])).

tff(c_44400,plain,(
    ! [A_1467,C_1468,E_1469] :
      ( k2_partfun1(k4_subset_1(A_1467,C_1468,'#skF_5'),'#skF_3',k1_tmap_1(A_1467,'#skF_3',C_1468,'#skF_5',E_1469,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1467,'#skF_3',C_1468,'#skF_5',E_1469,'#skF_7'))
      | k2_partfun1(C_1468,'#skF_3',E_1469,k9_subset_1(A_1467,C_1468,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_1467,C_1468,'#skF_5'))
      | ~ m1_subset_1(E_1469,k1_zfmisc_1(k2_zfmisc_1(C_1468,'#skF_3')))
      | ~ v1_funct_2(E_1469,C_1468,'#skF_3')
      | ~ v1_funct_1(E_1469)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1467))
      | ~ m1_subset_1(C_1468,k1_zfmisc_1(A_1467))
      | v1_xboole_0(C_1468)
      | v1_xboole_0(A_1467) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_34402])).

tff(c_44407,plain,(
    ! [A_1467] :
      ( k2_partfun1(k4_subset_1(A_1467,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_1467,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1467,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1(A_1467,'#skF_4','#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_1467,'#skF_4','#skF_5'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1467))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1467))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1467) ) ),
    inference(resolution,[status(thm)],[c_74,c_44400])).

tff(c_44417,plain,(
    ! [A_1467] :
      ( k2_partfun1(k4_subset_1(A_1467,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_1467,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1467,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_1467,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_1467,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1467))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1467))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1467) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_8289,c_44407])).

tff(c_46029,plain,(
    ! [A_1478] :
      ( k2_partfun1(k4_subset_1(A_1478,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_1478,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1478,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_1478,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_1478,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1478))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1478))
      | v1_xboole_0(A_1478) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_44417])).

tff(c_654,plain,(
    ! [C_313,A_314,B_315] :
      ( v1_relat_1(C_313)
      | ~ m1_subset_1(C_313,k1_zfmisc_1(k2_zfmisc_1(A_314,B_315))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_662,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_654])).

tff(c_120,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_164,plain,(
    ! [C_249,A_250,B_251] :
      ( v1_relat_1(C_249)
      | ~ m1_subset_1(C_249,k1_zfmisc_1(k2_zfmisc_1(A_250,B_251))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_171,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_164])).

tff(c_214,plain,(
    ! [C_254,A_255,B_256] :
      ( v4_relat_1(C_254,A_255)
      | ~ m1_subset_1(C_254,k1_zfmisc_1(k2_zfmisc_1(A_255,B_256))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_221,plain,(
    v4_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_214])).

tff(c_333,plain,(
    ! [B_275,A_276] :
      ( k1_relat_1(B_275) = A_276
      | ~ v1_partfun1(B_275,A_276)
      | ~ v4_relat_1(B_275,A_276)
      | ~ v1_relat_1(B_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_339,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_221,c_333])).

tff(c_345,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_339])).

tff(c_380,plain,(
    ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_345])).

tff(c_445,plain,(
    ! [C_293,A_294,B_295] :
      ( v1_partfun1(C_293,A_294)
      | ~ v1_funct_2(C_293,A_294,B_295)
      | ~ v1_funct_1(C_293)
      | ~ m1_subset_1(C_293,k1_zfmisc_1(k2_zfmisc_1(A_294,B_295)))
      | v1_xboole_0(B_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_448,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_445])).

tff(c_454,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_448])).

tff(c_456,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_380,c_454])).

tff(c_457,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_345])).

tff(c_463,plain,(
    ! [B_18] :
      ( k7_relat_1('#skF_7',B_18) = k1_xboole_0
      | ~ r1_xboole_0(B_18,'#skF_5')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_457,c_16])).

tff(c_522,plain,(
    ! [B_300] :
      ( k7_relat_1('#skF_7',B_300) = k1_xboole_0
      | ~ r1_xboole_0(B_300,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_463])).

tff(c_526,plain,(
    ! [A_23] :
      ( k7_relat_1('#skF_7',A_23) = k1_xboole_0
      | ~ r1_subset_1(A_23,'#skF_5')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_23) ) ),
    inference(resolution,[status(thm)],[c_32,c_522])).

tff(c_542,plain,(
    ! [A_301] :
      ( k7_relat_1('#skF_7',A_301) = k1_xboole_0
      | ~ r1_subset_1(A_301,'#skF_5')
      | v1_xboole_0(A_301) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_526])).

tff(c_545,plain,
    ( k7_relat_1('#skF_7','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_542])).

tff(c_548,plain,(
    k7_relat_1('#skF_7','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_545])).

tff(c_558,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_548,c_12])).

tff(c_566,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_558])).

tff(c_568,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_566])).

tff(c_569,plain,(
    k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_692,plain,(
    ! [C_318,A_319,B_320] :
      ( v4_relat_1(C_318,A_319)
      | ~ m1_subset_1(C_318,k1_zfmisc_1(k2_zfmisc_1(A_319,B_320))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_700,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_692])).

tff(c_839,plain,(
    ! [B_338,A_339] :
      ( k1_relat_1(B_338) = A_339
      | ~ v1_partfun1(B_338,A_339)
      | ~ v4_relat_1(B_338,A_339)
      | ~ v1_relat_1(B_338) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_842,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_700,c_839])).

tff(c_848,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_662,c_842])).

tff(c_852,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_848])).

tff(c_1555,plain,(
    ! [C_390,A_391,B_392] :
      ( v1_partfun1(C_390,A_391)
      | ~ v1_funct_2(C_390,A_391,B_392)
      | ~ v1_funct_1(C_390)
      | ~ m1_subset_1(C_390,k1_zfmisc_1(k2_zfmisc_1(A_391,B_392)))
      | v1_xboole_0(B_392) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1561,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_1555])).

tff(c_1568,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_1561])).

tff(c_1570,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_852,c_1568])).

tff(c_1571,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_848])).

tff(c_677,plain,
    ( k1_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_662,c_24])).

tff(c_680,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_677])).

tff(c_1573,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1571,c_680])).

tff(c_1580,plain,(
    ! [B_18] :
      ( k7_relat_1('#skF_6',B_18) = k1_xboole_0
      | ~ r1_xboole_0(B_18,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1571,c_16])).

tff(c_2018,plain,(
    ! [B_419] :
      ( k7_relat_1('#skF_6',B_419) = k1_xboole_0
      | ~ r1_xboole_0(B_419,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_662,c_1580])).

tff(c_2030,plain,
    ( k7_relat_1('#skF_6','#skF_1'('#skF_4')) = k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_2018])).

tff(c_2037,plain,(
    k7_relat_1('#skF_6','#skF_1'('#skF_4')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1573,c_2030])).

tff(c_2053,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),'#skF_1'('#skF_4'))
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2037,c_26])).

tff(c_2062,plain,(
    r1_tarski(k1_xboole_0,'#skF_1'('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_662,c_20,c_2053])).

tff(c_2050,plain,(
    ! [A_13] :
      ( k7_relat_1(k1_xboole_0,A_13) = k7_relat_1('#skF_6',A_13)
      | ~ r1_tarski(A_13,'#skF_1'('#skF_4'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2037,c_14])).

tff(c_2404,plain,(
    ! [A_448] :
      ( k7_relat_1(k1_xboole_0,A_448) = k7_relat_1('#skF_6',A_448)
      | ~ r1_tarski(A_448,'#skF_1'('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_662,c_2050])).

tff(c_2415,plain,(
    k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2062,c_2404])).

tff(c_2429,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_569,c_2415])).

tff(c_721,plain,(
    ! [A_325,B_326] :
      ( r1_xboole_0(A_325,B_326)
      | ~ r1_subset_1(A_325,B_326)
      | v1_xboole_0(B_326)
      | v1_xboole_0(A_325) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2645,plain,(
    ! [A_468,B_469] :
      ( k3_xboole_0(A_468,B_469) = k1_xboole_0
      | ~ r1_subset_1(A_468,B_469)
      | v1_xboole_0(B_469)
      | v1_xboole_0(A_468) ) ),
    inference(resolution,[status(thm)],[c_721,c_2])).

tff(c_2651,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_2645])).

tff(c_2655,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_84,c_2651])).

tff(c_661,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_654])).

tff(c_699,plain,(
    v4_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_692])).

tff(c_845,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_699,c_839])).

tff(c_851,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_661,c_845])).

tff(c_1628,plain,(
    ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_851])).

tff(c_1852,plain,(
    ! [C_411,A_412,B_413] :
      ( v1_partfun1(C_411,A_412)
      | ~ v1_funct_2(C_411,A_412,B_413)
      | ~ v1_funct_1(C_411)
      | ~ m1_subset_1(C_411,k1_zfmisc_1(k2_zfmisc_1(A_412,B_413)))
      | v1_xboole_0(B_413) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1855,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1852])).

tff(c_1861,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_1855])).

tff(c_1863,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_1628,c_1861])).

tff(c_1864,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_851])).

tff(c_1873,plain,(
    ! [B_18] :
      ( k7_relat_1('#skF_7',B_18) = k1_xboole_0
      | ~ r1_xboole_0(B_18,'#skF_5')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1864,c_16])).

tff(c_1922,plain,(
    ! [B_415] :
      ( k7_relat_1('#skF_7',B_415) = k1_xboole_0
      | ~ r1_xboole_0(B_415,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_661,c_1873])).

tff(c_1926,plain,(
    ! [A_23] :
      ( k7_relat_1('#skF_7',A_23) = k1_xboole_0
      | ~ r1_subset_1(A_23,'#skF_5')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_23) ) ),
    inference(resolution,[status(thm)],[c_32,c_1922])).

tff(c_2224,plain,(
    ! [A_436] :
      ( k7_relat_1('#skF_7',A_436) = k1_xboole_0
      | ~ r1_subset_1(A_436,'#skF_5')
      | v1_xboole_0(A_436) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_1926])).

tff(c_2227,plain,
    ( k7_relat_1('#skF_7','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_2224])).

tff(c_2230,plain,(
    k7_relat_1('#skF_7','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_2227])).

tff(c_2240,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),'#skF_4')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2230,c_26])).

tff(c_2253,plain,(
    r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_661,c_20,c_2240])).

tff(c_2237,plain,(
    ! [A_13] :
      ( k7_relat_1(k1_xboole_0,A_13) = k7_relat_1('#skF_7',A_13)
      | ~ r1_tarski(A_13,'#skF_4')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2230,c_14])).

tff(c_2271,plain,(
    ! [A_443] :
      ( k7_relat_1(k1_xboole_0,A_443) = k7_relat_1('#skF_7',A_443)
      | ~ r1_tarski(A_443,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_661,c_2237])).

tff(c_2274,plain,(
    k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2253,c_2271])).

tff(c_2295,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_569,c_2274])).

tff(c_2117,plain,(
    ! [A_422,B_423,C_424,D_425] :
      ( k2_partfun1(A_422,B_423,C_424,D_425) = k7_relat_1(C_424,D_425)
      | ~ m1_subset_1(C_424,k1_zfmisc_1(k2_zfmisc_1(A_422,B_423)))
      | ~ v1_funct_1(C_424) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_2121,plain,(
    ! [D_425] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_6',D_425) = k7_relat_1('#skF_6',D_425)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_74,c_2117])).

tff(c_2127,plain,(
    ! [D_425] : k2_partfun1('#skF_4','#skF_3','#skF_6',D_425) = k7_relat_1('#skF_6',D_425) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2121])).

tff(c_2119,plain,(
    ! [D_425] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_7',D_425) = k7_relat_1('#skF_7',D_425)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_68,c_2117])).

tff(c_2124,plain,(
    ! [D_425] : k2_partfun1('#skF_5','#skF_3','#skF_7',D_425) = k7_relat_1('#skF_7',D_425) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2119])).

tff(c_826,plain,(
    ! [A_335,B_336,C_337] :
      ( k9_subset_1(A_335,B_336,C_337) = k3_xboole_0(B_336,C_337)
      | ~ m1_subset_1(C_337,k1_zfmisc_1(A_335)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_838,plain,(
    ! [B_336] : k9_subset_1('#skF_2',B_336,'#skF_5') = k3_xboole_0(B_336,'#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_826])).

tff(c_66,plain,
    ( k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') != '#skF_7'
    | k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') != '#skF_6'
    | k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_119,plain,(
    k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_1896,plain,(
    k2_partfun1('#skF_5','#skF_3','#skF_7',k3_xboole_0('#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3','#skF_6',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_838,c_838,c_119])).

tff(c_3507,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2429,c_2655,c_2295,c_2655,c_2127,c_2124,c_1896])).

tff(c_3508,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_677])).

tff(c_3509,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_677])).

tff(c_3570,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3508,c_3509])).

tff(c_3660,plain,(
    ! [C_523,A_524,B_525] :
      ( v4_relat_1(C_523,A_524)
      | ~ m1_subset_1(C_523,k1_zfmisc_1(k2_zfmisc_1(A_524,B_525))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3668,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_3660])).

tff(c_4733,plain,(
    ! [B_607,A_608] :
      ( k1_relat_1(B_607) = A_608
      | ~ v1_partfun1(B_607,A_608)
      | ~ v4_relat_1(B_607,A_608)
      | ~ v1_relat_1(B_607) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_4739,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_3668,c_4733])).

tff(c_4748,plain,
    ( '#skF_6' = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_662,c_3570,c_4739])).

tff(c_4752,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_4748])).

tff(c_5177,plain,(
    ! [C_642,A_643,B_644] :
      ( v1_partfun1(C_642,A_643)
      | ~ v1_funct_2(C_642,A_643,B_644)
      | ~ v1_funct_1(C_642)
      | ~ m1_subset_1(C_642,k1_zfmisc_1(k2_zfmisc_1(A_643,B_644)))
      | v1_xboole_0(B_644) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_5183,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_5177])).

tff(c_5190,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_5183])).

tff(c_5192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_4752,c_5190])).

tff(c_5193,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4748])).

tff(c_3556,plain,(
    k7_relat_1('#skF_6','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3508,c_3508,c_3508,c_569])).

tff(c_5212,plain,(
    k7_relat_1('#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5193,c_5193,c_5193,c_3556])).

tff(c_3553,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = '#skF_6'
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3508,c_2])).

tff(c_5528,plain,(
    ! [A_668,B_669] :
      ( k3_xboole_0(A_668,B_669) = '#skF_4'
      | ~ r1_xboole_0(A_668,B_669) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5193,c_3553])).

tff(c_6039,plain,(
    ! [A_724,B_725] :
      ( k3_xboole_0(A_724,B_725) = '#skF_4'
      | ~ r1_subset_1(A_724,B_725)
      | v1_xboole_0(B_725)
      | v1_xboole_0(A_724) ) ),
    inference(resolution,[status(thm)],[c_32,c_5528])).

tff(c_6045,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = '#skF_4'
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_6039])).

tff(c_6049,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_84,c_6045])).

tff(c_3667,plain,(
    v4_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_3660])).

tff(c_4742,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_3667,c_4733])).

tff(c_4751,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_661,c_4742])).

tff(c_5329,plain,(
    ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_4751])).

tff(c_5398,plain,(
    ! [C_659,A_660,B_661] :
      ( v1_partfun1(C_659,A_660)
      | ~ v1_funct_2(C_659,A_660,B_661)
      | ~ v1_funct_1(C_659)
      | ~ m1_subset_1(C_659,k1_zfmisc_1(k2_zfmisc_1(A_660,B_661)))
      | v1_xboole_0(B_661) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_5404,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_5398])).

tff(c_5411,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_5404])).

tff(c_5413,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_5329,c_5411])).

tff(c_5414,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_4751])).

tff(c_3698,plain,(
    ! [A_16,B_18] :
      ( k7_relat_1(A_16,B_18) = '#skF_6'
      | ~ r1_xboole_0(B_18,k1_relat_1(A_16))
      | ~ v1_relat_1(A_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3508,c_16])).

tff(c_5682,plain,(
    ! [A_687,B_688] :
      ( k7_relat_1(A_687,B_688) = '#skF_4'
      | ~ r1_xboole_0(B_688,k1_relat_1(A_687))
      | ~ v1_relat_1(A_687) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5193,c_3698])).

tff(c_5693,plain,(
    ! [B_688] :
      ( k7_relat_1('#skF_7',B_688) = '#skF_4'
      | ~ r1_xboole_0(B_688,'#skF_5')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5414,c_5682])).

tff(c_5708,plain,(
    ! [B_689] :
      ( k7_relat_1('#skF_7',B_689) = '#skF_4'
      | ~ r1_xboole_0(B_689,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_661,c_5693])).

tff(c_5720,plain,(
    ! [A_23] :
      ( k7_relat_1('#skF_7',A_23) = '#skF_4'
      | ~ r1_subset_1(A_23,'#skF_5')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_23) ) ),
    inference(resolution,[status(thm)],[c_32,c_5708])).

tff(c_5798,plain,(
    ! [A_697] :
      ( k7_relat_1('#skF_7',A_697) = '#skF_4'
      | ~ r1_subset_1(A_697,'#skF_5')
      | v1_xboole_0(A_697) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_5720])).

tff(c_5801,plain,
    ( k7_relat_1('#skF_7','#skF_4') = '#skF_4'
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_5798])).

tff(c_5804,plain,(
    k7_relat_1('#skF_7','#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_5801])).

tff(c_5221,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5193,c_78])).

tff(c_5219,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5193,c_74])).

tff(c_52,plain,(
    ! [A_39,B_40,C_41,D_42] :
      ( k2_partfun1(A_39,B_40,C_41,D_42) = k7_relat_1(C_41,D_42)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40)))
      | ~ v1_funct_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_5442,plain,(
    ! [D_42] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_4',D_42) = k7_relat_1('#skF_4',D_42)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5219,c_52])).

tff(c_5459,plain,(
    ! [D_42] : k2_partfun1('#skF_4','#skF_3','#skF_4',D_42) = k7_relat_1('#skF_4',D_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5221,c_5442])).

tff(c_5322,plain,(
    ! [A_648,B_649,C_650,D_651] :
      ( k2_partfun1(A_648,B_649,C_650,D_651) = k7_relat_1(C_650,D_651)
      | ~ m1_subset_1(C_650,k1_zfmisc_1(k2_zfmisc_1(A_648,B_649)))
      | ~ v1_funct_1(C_650) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_5324,plain,(
    ! [D_651] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_7',D_651) = k7_relat_1('#skF_7',D_651)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_68,c_5322])).

tff(c_5327,plain,(
    ! [D_651] : k2_partfun1('#skF_5','#skF_3','#skF_7',D_651) = k7_relat_1('#skF_7',D_651) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_5324])).

tff(c_4683,plain,(
    ! [A_600,B_601,C_602] :
      ( k9_subset_1(A_600,B_601,C_602) = k3_xboole_0(B_601,C_602)
      | ~ m1_subset_1(C_602,k1_zfmisc_1(A_600)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4695,plain,(
    ! [B_601] : k9_subset_1('#skF_2',B_601,'#skF_5') = k3_xboole_0(B_601,'#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_4683])).

tff(c_4705,plain,(
    k2_partfun1('#skF_5','#skF_3','#skF_7',k3_xboole_0('#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3','#skF_6',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4695,c_4695,c_119])).

tff(c_6548,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5212,c_6049,c_5804,c_6049,c_5459,c_5327,c_5193,c_4705])).

tff(c_6549,plain,
    ( k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_6995,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_6549])).

tff(c_46040,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_46029,c_6995])).

tff(c_46054,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_8611,c_8940,c_8430,c_8940,c_7154,c_7154,c_9958,c_46040])).

tff(c_46056,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_46054])).

tff(c_46057,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_6993])).

tff(c_46058,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_6993])).

tff(c_46076,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46057,c_46058])).

tff(c_46177,plain,(
    ! [C_1493,A_1494,B_1495] :
      ( v4_relat_1(C_1493,A_1494)
      | ~ m1_subset_1(C_1493,k1_zfmisc_1(k2_zfmisc_1(A_1494,B_1495))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_46185,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_46177])).

tff(c_47296,plain,(
    ! [B_1581,A_1582] :
      ( k1_relat_1(B_1581) = A_1582
      | ~ v1_partfun1(B_1581,A_1582)
      | ~ v4_relat_1(B_1581,A_1582)
      | ~ v1_relat_1(B_1581) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_47302,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46185,c_47296])).

tff(c_47311,plain,
    ( '#skF_6' = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6977,c_46076,c_47302])).

tff(c_47315,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_47311])).

tff(c_47797,plain,(
    ! [C_1617,A_1618,B_1619] :
      ( v1_partfun1(C_1617,A_1618)
      | ~ v1_funct_2(C_1617,A_1618,B_1619)
      | ~ v1_funct_1(C_1617)
      | ~ m1_subset_1(C_1617,k1_zfmisc_1(k2_zfmisc_1(A_1618,B_1619)))
      | v1_xboole_0(B_1619) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_47803,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_47797])).

tff(c_47810,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_47803])).

tff(c_47812,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_47315,c_47810])).

tff(c_47813,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_47311])).

tff(c_46065,plain,(
    k7_relat_1('#skF_6','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46057,c_46057,c_46057,c_6880])).

tff(c_47834,plain,(
    k7_relat_1('#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47813,c_47813,c_47813,c_46065])).

tff(c_46268,plain,(
    ! [A_1502,B_1503] :
      ( r1_xboole_0(A_1502,B_1503)
      | ~ r1_subset_1(A_1502,B_1503)
      | v1_xboole_0(B_1503)
      | v1_xboole_0(A_1502) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_46063,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = '#skF_6'
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46057,c_2])).

tff(c_46282,plain,(
    ! [A_1502,B_1503] :
      ( k3_xboole_0(A_1502,B_1503) = '#skF_6'
      | ~ r1_subset_1(A_1502,B_1503)
      | v1_xboole_0(B_1503)
      | v1_xboole_0(A_1502) ) ),
    inference(resolution,[status(thm)],[c_46268,c_46063])).

tff(c_48641,plain,(
    ! [A_1691,B_1692] :
      ( k3_xboole_0(A_1691,B_1692) = '#skF_4'
      | ~ r1_subset_1(A_1691,B_1692)
      | v1_xboole_0(B_1692)
      | v1_xboole_0(A_1691) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47813,c_46282])).

tff(c_48647,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = '#skF_4'
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_48641])).

tff(c_48651,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_84,c_48647])).

tff(c_47246,plain,(
    ! [A_1574,B_1575,C_1576] :
      ( k9_subset_1(A_1574,B_1575,C_1576) = k3_xboole_0(B_1575,C_1576)
      | ~ m1_subset_1(C_1576,k1_zfmisc_1(A_1574)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_47258,plain,(
    ! [B_1575] : k9_subset_1('#skF_2',B_1575,'#skF_5') = k3_xboole_0(B_1575,'#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_47246])).

tff(c_46184,plain,(
    v4_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_46177])).

tff(c_47305,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_46184,c_47296])).

tff(c_47314,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6976,c_47305])).

tff(c_47950,plain,(
    ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_47314])).

tff(c_48019,plain,(
    ! [C_1634,A_1635,B_1636] :
      ( v1_partfun1(C_1634,A_1635)
      | ~ v1_funct_2(C_1634,A_1635,B_1636)
      | ~ v1_funct_1(C_1634)
      | ~ m1_subset_1(C_1634,k1_zfmisc_1(k2_zfmisc_1(A_1635,B_1636)))
      | v1_xboole_0(B_1636) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_48025,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_48019])).

tff(c_48032,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_48025])).

tff(c_48034,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_47950,c_48032])).

tff(c_48035,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_47314])).

tff(c_46186,plain,(
    ! [A_16,B_18] :
      ( k7_relat_1(A_16,B_18) = '#skF_6'
      | ~ r1_xboole_0(B_18,k1_relat_1(A_16))
      | ~ v1_relat_1(A_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46057,c_16])).

tff(c_48303,plain,(
    ! [A_1662,B_1663] :
      ( k7_relat_1(A_1662,B_1663) = '#skF_4'
      | ~ r1_xboole_0(B_1663,k1_relat_1(A_1662))
      | ~ v1_relat_1(A_1662) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47813,c_46186])).

tff(c_48314,plain,(
    ! [B_1663] :
      ( k7_relat_1('#skF_7',B_1663) = '#skF_4'
      | ~ r1_xboole_0(B_1663,'#skF_5')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48035,c_48303])).

tff(c_48329,plain,(
    ! [B_1664] :
      ( k7_relat_1('#skF_7',B_1664) = '#skF_4'
      | ~ r1_xboole_0(B_1664,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6976,c_48314])).

tff(c_48341,plain,(
    ! [A_23] :
      ( k7_relat_1('#skF_7',A_23) = '#skF_4'
      | ~ r1_subset_1(A_23,'#skF_5')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_23) ) ),
    inference(resolution,[status(thm)],[c_32,c_48329])).

tff(c_48419,plain,(
    ! [A_1672] :
      ( k7_relat_1('#skF_7',A_1672) = '#skF_4'
      | ~ r1_subset_1(A_1672,'#skF_5')
      | v1_xboole_0(A_1672) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_48341])).

tff(c_48422,plain,
    ( k7_relat_1('#skF_7','#skF_4') = '#skF_4'
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_48419])).

tff(c_48425,plain,(
    k7_relat_1('#skF_7','#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_48422])).

tff(c_47842,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47813,c_78])).

tff(c_47841,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47813,c_76])).

tff(c_47840,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47813,c_74])).

tff(c_48222,plain,(
    ! [D_1653,F_1656,B_1655,A_1651,E_1652,C_1654] :
      ( v1_funct_1(k1_tmap_1(A_1651,B_1655,C_1654,D_1653,E_1652,F_1656))
      | ~ m1_subset_1(F_1656,k1_zfmisc_1(k2_zfmisc_1(D_1653,B_1655)))
      | ~ v1_funct_2(F_1656,D_1653,B_1655)
      | ~ v1_funct_1(F_1656)
      | ~ m1_subset_1(E_1652,k1_zfmisc_1(k2_zfmisc_1(C_1654,B_1655)))
      | ~ v1_funct_2(E_1652,C_1654,B_1655)
      | ~ v1_funct_1(E_1652)
      | ~ m1_subset_1(D_1653,k1_zfmisc_1(A_1651))
      | v1_xboole_0(D_1653)
      | ~ m1_subset_1(C_1654,k1_zfmisc_1(A_1651))
      | v1_xboole_0(C_1654)
      | v1_xboole_0(B_1655)
      | v1_xboole_0(A_1651) ) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_48226,plain,(
    ! [A_1651,C_1654,E_1652] :
      ( v1_funct_1(k1_tmap_1(A_1651,'#skF_3',C_1654,'#skF_5',E_1652,'#skF_7'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_1652,k1_zfmisc_1(k2_zfmisc_1(C_1654,'#skF_3')))
      | ~ v1_funct_2(E_1652,C_1654,'#skF_3')
      | ~ v1_funct_1(E_1652)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1651))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1654,k1_zfmisc_1(A_1651))
      | v1_xboole_0(C_1654)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1651) ) ),
    inference(resolution,[status(thm)],[c_68,c_48222])).

tff(c_48233,plain,(
    ! [A_1651,C_1654,E_1652] :
      ( v1_funct_1(k1_tmap_1(A_1651,'#skF_3',C_1654,'#skF_5',E_1652,'#skF_7'))
      | ~ m1_subset_1(E_1652,k1_zfmisc_1(k2_zfmisc_1(C_1654,'#skF_3')))
      | ~ v1_funct_2(E_1652,C_1654,'#skF_3')
      | ~ v1_funct_1(E_1652)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1651))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1654,k1_zfmisc_1(A_1651))
      | v1_xboole_0(C_1654)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1651) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_48226])).

tff(c_48508,plain,(
    ! [A_1681,C_1682,E_1683] :
      ( v1_funct_1(k1_tmap_1(A_1681,'#skF_3',C_1682,'#skF_5',E_1683,'#skF_7'))
      | ~ m1_subset_1(E_1683,k1_zfmisc_1(k2_zfmisc_1(C_1682,'#skF_3')))
      | ~ v1_funct_2(E_1683,C_1682,'#skF_3')
      | ~ v1_funct_1(E_1683)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1681))
      | ~ m1_subset_1(C_1682,k1_zfmisc_1(A_1681))
      | v1_xboole_0(C_1682)
      | v1_xboole_0(A_1681) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_48233])).

tff(c_48513,plain,(
    ! [A_1681] :
      ( v1_funct_1(k1_tmap_1(A_1681,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | ~ v1_funct_2('#skF_4','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1681))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1681))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1681) ) ),
    inference(resolution,[status(thm)],[c_47840,c_48508])).

tff(c_48521,plain,(
    ! [A_1681] :
      ( v1_funct_1(k1_tmap_1(A_1681,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1681))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1681))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1681) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47842,c_47841,c_48513])).

tff(c_48791,plain,(
    ! [A_1710] :
      ( v1_funct_1(k1_tmap_1(A_1710,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1710))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1710))
      | v1_xboole_0(A_1710) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_48521])).

tff(c_48794,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_48791])).

tff(c_48797,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_48794])).

tff(c_48798,plain,(
    v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_48797])).

tff(c_48063,plain,(
    ! [D_42] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_4',D_42) = k7_relat_1('#skF_4',D_42)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_47840,c_52])).

tff(c_48080,plain,(
    ! [D_42] : k2_partfun1('#skF_4','#skF_3','#skF_4',D_42) = k7_relat_1('#skF_4',D_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47842,c_48063])).

tff(c_47943,plain,(
    ! [A_1623,B_1624,C_1625,D_1626] :
      ( k2_partfun1(A_1623,B_1624,C_1625,D_1626) = k7_relat_1(C_1625,D_1626)
      | ~ m1_subset_1(C_1625,k1_zfmisc_1(k2_zfmisc_1(A_1623,B_1624)))
      | ~ v1_funct_1(C_1625) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_47945,plain,(
    ! [D_1626] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_7',D_1626) = k7_relat_1('#skF_7',D_1626)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_68,c_47943])).

tff(c_47948,plain,(
    ! [D_1626] : k2_partfun1('#skF_5','#skF_3','#skF_7',D_1626) = k7_relat_1('#skF_7',D_1626) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_47945])).

tff(c_48652,plain,(
    ! [D_1694,E_1698,F_1693,A_1695,B_1696,C_1697] :
      ( k2_partfun1(k4_subset_1(A_1695,C_1697,D_1694),B_1696,k1_tmap_1(A_1695,B_1696,C_1697,D_1694,E_1698,F_1693),D_1694) = F_1693
      | ~ m1_subset_1(k1_tmap_1(A_1695,B_1696,C_1697,D_1694,E_1698,F_1693),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1695,C_1697,D_1694),B_1696)))
      | ~ v1_funct_2(k1_tmap_1(A_1695,B_1696,C_1697,D_1694,E_1698,F_1693),k4_subset_1(A_1695,C_1697,D_1694),B_1696)
      | ~ v1_funct_1(k1_tmap_1(A_1695,B_1696,C_1697,D_1694,E_1698,F_1693))
      | k2_partfun1(D_1694,B_1696,F_1693,k9_subset_1(A_1695,C_1697,D_1694)) != k2_partfun1(C_1697,B_1696,E_1698,k9_subset_1(A_1695,C_1697,D_1694))
      | ~ m1_subset_1(F_1693,k1_zfmisc_1(k2_zfmisc_1(D_1694,B_1696)))
      | ~ v1_funct_2(F_1693,D_1694,B_1696)
      | ~ v1_funct_1(F_1693)
      | ~ m1_subset_1(E_1698,k1_zfmisc_1(k2_zfmisc_1(C_1697,B_1696)))
      | ~ v1_funct_2(E_1698,C_1697,B_1696)
      | ~ v1_funct_1(E_1698)
      | ~ m1_subset_1(D_1694,k1_zfmisc_1(A_1695))
      | v1_xboole_0(D_1694)
      | ~ m1_subset_1(C_1697,k1_zfmisc_1(A_1695))
      | v1_xboole_0(C_1697)
      | v1_xboole_0(B_1696)
      | v1_xboole_0(A_1695) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_53370,plain,(
    ! [C_1878,A_1875,F_1880,B_1879,E_1876,D_1877] :
      ( k2_partfun1(k4_subset_1(A_1875,C_1878,D_1877),B_1879,k1_tmap_1(A_1875,B_1879,C_1878,D_1877,E_1876,F_1880),D_1877) = F_1880
      | ~ v1_funct_2(k1_tmap_1(A_1875,B_1879,C_1878,D_1877,E_1876,F_1880),k4_subset_1(A_1875,C_1878,D_1877),B_1879)
      | ~ v1_funct_1(k1_tmap_1(A_1875,B_1879,C_1878,D_1877,E_1876,F_1880))
      | k2_partfun1(D_1877,B_1879,F_1880,k9_subset_1(A_1875,C_1878,D_1877)) != k2_partfun1(C_1878,B_1879,E_1876,k9_subset_1(A_1875,C_1878,D_1877))
      | ~ m1_subset_1(F_1880,k1_zfmisc_1(k2_zfmisc_1(D_1877,B_1879)))
      | ~ v1_funct_2(F_1880,D_1877,B_1879)
      | ~ v1_funct_1(F_1880)
      | ~ m1_subset_1(E_1876,k1_zfmisc_1(k2_zfmisc_1(C_1878,B_1879)))
      | ~ v1_funct_2(E_1876,C_1878,B_1879)
      | ~ v1_funct_1(E_1876)
      | ~ m1_subset_1(D_1877,k1_zfmisc_1(A_1875))
      | v1_xboole_0(D_1877)
      | ~ m1_subset_1(C_1878,k1_zfmisc_1(A_1875))
      | v1_xboole_0(C_1878)
      | v1_xboole_0(B_1879)
      | v1_xboole_0(A_1875) ) ),
    inference(resolution,[status(thm)],[c_60,c_48652])).

tff(c_62150,plain,(
    ! [E_2005,F_2009,A_2004,D_2006,C_2007,B_2008] :
      ( k2_partfun1(k4_subset_1(A_2004,C_2007,D_2006),B_2008,k1_tmap_1(A_2004,B_2008,C_2007,D_2006,E_2005,F_2009),D_2006) = F_2009
      | ~ v1_funct_1(k1_tmap_1(A_2004,B_2008,C_2007,D_2006,E_2005,F_2009))
      | k2_partfun1(D_2006,B_2008,F_2009,k9_subset_1(A_2004,C_2007,D_2006)) != k2_partfun1(C_2007,B_2008,E_2005,k9_subset_1(A_2004,C_2007,D_2006))
      | ~ m1_subset_1(F_2009,k1_zfmisc_1(k2_zfmisc_1(D_2006,B_2008)))
      | ~ v1_funct_2(F_2009,D_2006,B_2008)
      | ~ v1_funct_1(F_2009)
      | ~ m1_subset_1(E_2005,k1_zfmisc_1(k2_zfmisc_1(C_2007,B_2008)))
      | ~ v1_funct_2(E_2005,C_2007,B_2008)
      | ~ v1_funct_1(E_2005)
      | ~ m1_subset_1(D_2006,k1_zfmisc_1(A_2004))
      | v1_xboole_0(D_2006)
      | ~ m1_subset_1(C_2007,k1_zfmisc_1(A_2004))
      | v1_xboole_0(C_2007)
      | v1_xboole_0(B_2008)
      | v1_xboole_0(A_2004) ) ),
    inference(resolution,[status(thm)],[c_62,c_53370])).

tff(c_62156,plain,(
    ! [A_2004,C_2007,E_2005] :
      ( k2_partfun1(k4_subset_1(A_2004,C_2007,'#skF_5'),'#skF_3',k1_tmap_1(A_2004,'#skF_3',C_2007,'#skF_5',E_2005,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_2004,'#skF_3',C_2007,'#skF_5',E_2005,'#skF_7'))
      | k2_partfun1(C_2007,'#skF_3',E_2005,k9_subset_1(A_2004,C_2007,'#skF_5')) != k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1(A_2004,C_2007,'#skF_5'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_2005,k1_zfmisc_1(k2_zfmisc_1(C_2007,'#skF_3')))
      | ~ v1_funct_2(E_2005,C_2007,'#skF_3')
      | ~ v1_funct_1(E_2005)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2004))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_2007,k1_zfmisc_1(A_2004))
      | v1_xboole_0(C_2007)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2004) ) ),
    inference(resolution,[status(thm)],[c_68,c_62150])).

tff(c_62164,plain,(
    ! [A_2004,C_2007,E_2005] :
      ( k2_partfun1(k4_subset_1(A_2004,C_2007,'#skF_5'),'#skF_3',k1_tmap_1(A_2004,'#skF_3',C_2007,'#skF_5',E_2005,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_2004,'#skF_3',C_2007,'#skF_5',E_2005,'#skF_7'))
      | k2_partfun1(C_2007,'#skF_3',E_2005,k9_subset_1(A_2004,C_2007,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_2004,C_2007,'#skF_5'))
      | ~ m1_subset_1(E_2005,k1_zfmisc_1(k2_zfmisc_1(C_2007,'#skF_3')))
      | ~ v1_funct_2(E_2005,C_2007,'#skF_3')
      | ~ v1_funct_1(E_2005)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2004))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_2007,k1_zfmisc_1(A_2004))
      | v1_xboole_0(C_2007)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2004) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_47948,c_62156])).

tff(c_62603,plain,(
    ! [A_2012,C_2013,E_2014] :
      ( k2_partfun1(k4_subset_1(A_2012,C_2013,'#skF_5'),'#skF_3',k1_tmap_1(A_2012,'#skF_3',C_2013,'#skF_5',E_2014,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_2012,'#skF_3',C_2013,'#skF_5',E_2014,'#skF_7'))
      | k2_partfun1(C_2013,'#skF_3',E_2014,k9_subset_1(A_2012,C_2013,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_2012,C_2013,'#skF_5'))
      | ~ m1_subset_1(E_2014,k1_zfmisc_1(k2_zfmisc_1(C_2013,'#skF_3')))
      | ~ v1_funct_2(E_2014,C_2013,'#skF_3')
      | ~ v1_funct_1(E_2014)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2012))
      | ~ m1_subset_1(C_2013,k1_zfmisc_1(A_2012))
      | v1_xboole_0(C_2013)
      | v1_xboole_0(A_2012) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_62164])).

tff(c_62608,plain,(
    ! [A_2012] :
      ( k2_partfun1(k4_subset_1(A_2012,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_2012,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_2012,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | k2_partfun1('#skF_4','#skF_3','#skF_4',k9_subset_1(A_2012,'#skF_4','#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_2012,'#skF_4','#skF_5'))
      | ~ v1_funct_2('#skF_4','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2012))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2012))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_2012) ) ),
    inference(resolution,[status(thm)],[c_47840,c_62603])).

tff(c_62616,plain,(
    ! [A_2012] :
      ( k2_partfun1(k4_subset_1(A_2012,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_2012,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_2012,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_2012,'#skF_4','#skF_5')) != k7_relat_1('#skF_4',k9_subset_1(A_2012,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2012))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2012))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_2012) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47842,c_47841,c_48080,c_62608])).

tff(c_64456,plain,(
    ! [A_2040] :
      ( k2_partfun1(k4_subset_1(A_2040,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_2040,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_2040,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_2040,'#skF_4','#skF_5')) != k7_relat_1('#skF_4',k9_subset_1(A_2040,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2040))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2040))
      | v1_xboole_0(A_2040) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_62616])).

tff(c_47826,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),'#skF_5') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47813,c_6995])).

tff(c_64465,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k7_relat_1('#skF_4',k9_subset_1('#skF_2','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_64456,c_47826])).

tff(c_64478,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_47834,c_48651,c_47258,c_48425,c_48651,c_47258,c_48798,c_64465])).

tff(c_64480,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_64478])).

tff(c_64481,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_6549])).

tff(c_64499,plain,(
    ! [C_2043,A_2044,B_2045] :
      ( v4_relat_1(C_2043,A_2044)
      | ~ m1_subset_1(C_2043,k1_zfmisc_1(k2_zfmisc_1(A_2044,B_2045))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_64507,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_64499])).

tff(c_64683,plain,(
    ! [B_2067,A_2068] :
      ( k1_relat_1(B_2067) = A_2068
      | ~ v1_partfun1(B_2067,A_2068)
      | ~ v4_relat_1(B_2067,A_2068)
      | ~ v1_relat_1(B_2067) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_64686,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_64507,c_64683])).

tff(c_64692,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6977,c_64686])).

tff(c_64696,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_64692])).

tff(c_65085,plain,(
    ! [C_2099,A_2100,B_2101] :
      ( v1_partfun1(C_2099,A_2100)
      | ~ v1_funct_2(C_2099,A_2100,B_2101)
      | ~ v1_funct_1(C_2099)
      | ~ m1_subset_1(C_2099,k1_zfmisc_1(k2_zfmisc_1(A_2100,B_2101)))
      | v1_xboole_0(B_2101) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_65091,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_65085])).

tff(c_65098,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_65091])).

tff(c_65100,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_64696,c_65098])).

tff(c_65101,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_64692])).

tff(c_64483,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_6993])).

tff(c_65103,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_65101,c_64483])).

tff(c_65107,plain,(
    ! [B_18] :
      ( k7_relat_1('#skF_6',B_18) = k1_xboole_0
      | ~ r1_xboole_0(B_18,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65101,c_16])).

tff(c_65439,plain,(
    ! [B_2119] :
      ( k7_relat_1('#skF_6',B_2119) = k1_xboole_0
      | ~ r1_xboole_0(B_2119,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6977,c_65107])).

tff(c_65451,plain,
    ( k7_relat_1('#skF_6','#skF_1'('#skF_4')) = k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_65439])).

tff(c_65458,plain,(
    k7_relat_1('#skF_6','#skF_1'('#skF_4')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_65103,c_65451])).

tff(c_65462,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),'#skF_1'('#skF_4'))
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_65458,c_26])).

tff(c_65469,plain,(
    r1_tarski(k1_xboole_0,'#skF_1'('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6977,c_20,c_65462])).

tff(c_65473,plain,(
    ! [C_2120,B_2121,A_2122] :
      ( k7_relat_1(k7_relat_1(C_2120,B_2121),A_2122) = k7_relat_1(C_2120,A_2122)
      | ~ r1_tarski(A_2122,B_2121)
      | ~ v1_relat_1(C_2120) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_65498,plain,(
    ! [A_2122] :
      ( k7_relat_1(k1_xboole_0,A_2122) = k7_relat_1('#skF_6',A_2122)
      | ~ r1_tarski(A_2122,'#skF_1'('#skF_4'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65458,c_65473])).

tff(c_65933,plain,(
    ! [A_2151] :
      ( k7_relat_1(k1_xboole_0,A_2151) = k7_relat_1('#skF_6',A_2151)
      | ~ r1_tarski(A_2151,'#skF_1'('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6977,c_65498])).

tff(c_65944,plain,(
    k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_65469,c_65933])).

tff(c_65958,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6880,c_65944])).

tff(c_64517,plain,(
    ! [A_2049,B_2050] :
      ( r1_xboole_0(A_2049,B_2050)
      | ~ r1_subset_1(A_2049,B_2050)
      | v1_xboole_0(B_2050)
      | v1_xboole_0(A_2049) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_66096,plain,(
    ! [A_2162,B_2163] :
      ( k3_xboole_0(A_2162,B_2163) = k1_xboole_0
      | ~ r1_subset_1(A_2162,B_2163)
      | v1_xboole_0(B_2163)
      | v1_xboole_0(A_2162) ) ),
    inference(resolution,[status(thm)],[c_64517,c_2])).

tff(c_66099,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_66096])).

tff(c_66102,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_84,c_66099])).

tff(c_64591,plain,(
    ! [A_2058,B_2059,C_2060] :
      ( k9_subset_1(A_2058,B_2059,C_2060) = k3_xboole_0(B_2059,C_2060)
      | ~ m1_subset_1(C_2060,k1_zfmisc_1(A_2058)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_64603,plain,(
    ! [B_2059] : k9_subset_1('#skF_2',B_2059,'#skF_5') = k3_xboole_0(B_2059,'#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_64591])).

tff(c_64506,plain,(
    v4_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_64499])).

tff(c_64689,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_64506,c_64683])).

tff(c_64695,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6976,c_64689])).

tff(c_65153,plain,(
    ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_64695])).

tff(c_65379,plain,(
    ! [C_2116,A_2117,B_2118] :
      ( v1_partfun1(C_2116,A_2117)
      | ~ v1_funct_2(C_2116,A_2117,B_2118)
      | ~ v1_funct_1(C_2116)
      | ~ m1_subset_1(C_2116,k1_zfmisc_1(k2_zfmisc_1(A_2117,B_2118)))
      | v1_xboole_0(B_2118) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_65382,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_65379])).

tff(c_65388,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_65382])).

tff(c_65390,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_65153,c_65388])).

tff(c_65391,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_64695])).

tff(c_65397,plain,(
    ! [B_18] :
      ( k7_relat_1('#skF_7',B_18) = k1_xboole_0
      | ~ r1_xboole_0(B_18,'#skF_5')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65391,c_16])).

tff(c_65535,plain,(
    ! [B_2123] :
      ( k7_relat_1('#skF_7',B_2123) = k1_xboole_0
      | ~ r1_xboole_0(B_2123,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6976,c_65397])).

tff(c_65539,plain,(
    ! [A_23] :
      ( k7_relat_1('#skF_7',A_23) = k1_xboole_0
      | ~ r1_subset_1(A_23,'#skF_5')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_23) ) ),
    inference(resolution,[status(thm)],[c_32,c_65535])).

tff(c_65638,plain,(
    ! [A_2131] :
      ( k7_relat_1('#skF_7',A_2131) = k1_xboole_0
      | ~ r1_subset_1(A_2131,'#skF_5')
      | v1_xboole_0(A_2131) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_65539])).

tff(c_65641,plain,
    ( k7_relat_1('#skF_7','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_65638])).

tff(c_65644,plain,(
    k7_relat_1('#skF_7','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_65641])).

tff(c_65654,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),'#skF_4')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_65644,c_26])).

tff(c_65667,plain,(
    r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6976,c_20,c_65654])).

tff(c_65651,plain,(
    ! [A_13] :
      ( k7_relat_1(k1_xboole_0,A_13) = k7_relat_1('#skF_7',A_13)
      | ~ r1_tarski(A_13,'#skF_4')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65644,c_14])).

tff(c_65757,plain,(
    ! [A_2138] :
      ( k7_relat_1(k1_xboole_0,A_2138) = k7_relat_1('#skF_7',A_2138)
      | ~ r1_tarski(A_2138,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6976,c_65651])).

tff(c_65760,plain,(
    k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_65667,c_65757])).

tff(c_65777,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6880,c_65760])).

tff(c_65626,plain,(
    ! [A_2126,B_2127,C_2128,D_2129] :
      ( k2_partfun1(A_2126,B_2127,C_2128,D_2129) = k7_relat_1(C_2128,D_2129)
      | ~ m1_subset_1(C_2128,k1_zfmisc_1(k2_zfmisc_1(A_2126,B_2127)))
      | ~ v1_funct_1(C_2128) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_65628,plain,(
    ! [D_2129] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_7',D_2129) = k7_relat_1('#skF_7',D_2129)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_68,c_65626])).

tff(c_65633,plain,(
    ! [D_2129] : k2_partfun1('#skF_5','#skF_3','#skF_7',D_2129) = k7_relat_1('#skF_7',D_2129) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_65628])).

tff(c_65630,plain,(
    ! [D_2129] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_6',D_2129) = k7_relat_1('#skF_6',D_2129)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_74,c_65626])).

tff(c_65636,plain,(
    ! [D_2129] : k2_partfun1('#skF_4','#skF_3','#skF_6',D_2129) = k7_relat_1('#skF_6',D_2129) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_65630])).

tff(c_65847,plain,(
    ! [F_2145,E_2141,A_2140,C_2143,B_2144,D_2142] :
      ( v1_funct_1(k1_tmap_1(A_2140,B_2144,C_2143,D_2142,E_2141,F_2145))
      | ~ m1_subset_1(F_2145,k1_zfmisc_1(k2_zfmisc_1(D_2142,B_2144)))
      | ~ v1_funct_2(F_2145,D_2142,B_2144)
      | ~ v1_funct_1(F_2145)
      | ~ m1_subset_1(E_2141,k1_zfmisc_1(k2_zfmisc_1(C_2143,B_2144)))
      | ~ v1_funct_2(E_2141,C_2143,B_2144)
      | ~ v1_funct_1(E_2141)
      | ~ m1_subset_1(D_2142,k1_zfmisc_1(A_2140))
      | v1_xboole_0(D_2142)
      | ~ m1_subset_1(C_2143,k1_zfmisc_1(A_2140))
      | v1_xboole_0(C_2143)
      | v1_xboole_0(B_2144)
      | v1_xboole_0(A_2140) ) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_65849,plain,(
    ! [A_2140,C_2143,E_2141] :
      ( v1_funct_1(k1_tmap_1(A_2140,'#skF_3',C_2143,'#skF_5',E_2141,'#skF_7'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_2141,k1_zfmisc_1(k2_zfmisc_1(C_2143,'#skF_3')))
      | ~ v1_funct_2(E_2141,C_2143,'#skF_3')
      | ~ v1_funct_1(E_2141)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2140))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_2143,k1_zfmisc_1(A_2140))
      | v1_xboole_0(C_2143)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2140) ) ),
    inference(resolution,[status(thm)],[c_68,c_65847])).

tff(c_65854,plain,(
    ! [A_2140,C_2143,E_2141] :
      ( v1_funct_1(k1_tmap_1(A_2140,'#skF_3',C_2143,'#skF_5',E_2141,'#skF_7'))
      | ~ m1_subset_1(E_2141,k1_zfmisc_1(k2_zfmisc_1(C_2143,'#skF_3')))
      | ~ v1_funct_2(E_2141,C_2143,'#skF_3')
      | ~ v1_funct_1(E_2141)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2140))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_2143,k1_zfmisc_1(A_2140))
      | v1_xboole_0(C_2143)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_65849])).

tff(c_66592,plain,(
    ! [A_2188,C_2189,E_2190] :
      ( v1_funct_1(k1_tmap_1(A_2188,'#skF_3',C_2189,'#skF_5',E_2190,'#skF_7'))
      | ~ m1_subset_1(E_2190,k1_zfmisc_1(k2_zfmisc_1(C_2189,'#skF_3')))
      | ~ v1_funct_2(E_2190,C_2189,'#skF_3')
      | ~ v1_funct_1(E_2190)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2188))
      | ~ m1_subset_1(C_2189,k1_zfmisc_1(A_2188))
      | v1_xboole_0(C_2189)
      | v1_xboole_0(A_2188) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_65854])).

tff(c_66599,plain,(
    ! [A_2188] :
      ( v1_funct_1(k1_tmap_1(A_2188,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2188))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2188))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_2188) ) ),
    inference(resolution,[status(thm)],[c_74,c_66592])).

tff(c_66609,plain,(
    ! [A_2188] :
      ( v1_funct_1(k1_tmap_1(A_2188,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2188))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2188))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_2188) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_66599])).

tff(c_67303,plain,(
    ! [A_2215] :
      ( v1_funct_1(k1_tmap_1(A_2215,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2215))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2215))
      | v1_xboole_0(A_2215) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_66609])).

tff(c_67306,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_67303])).

tff(c_67309,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_67306])).

tff(c_67310,plain,(
    v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_67309])).

tff(c_66855,plain,(
    ! [A_2197,C_2199,E_2200,B_2198,D_2196,F_2195] :
      ( k2_partfun1(k4_subset_1(A_2197,C_2199,D_2196),B_2198,k1_tmap_1(A_2197,B_2198,C_2199,D_2196,E_2200,F_2195),C_2199) = E_2200
      | ~ m1_subset_1(k1_tmap_1(A_2197,B_2198,C_2199,D_2196,E_2200,F_2195),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_2197,C_2199,D_2196),B_2198)))
      | ~ v1_funct_2(k1_tmap_1(A_2197,B_2198,C_2199,D_2196,E_2200,F_2195),k4_subset_1(A_2197,C_2199,D_2196),B_2198)
      | ~ v1_funct_1(k1_tmap_1(A_2197,B_2198,C_2199,D_2196,E_2200,F_2195))
      | k2_partfun1(D_2196,B_2198,F_2195,k9_subset_1(A_2197,C_2199,D_2196)) != k2_partfun1(C_2199,B_2198,E_2200,k9_subset_1(A_2197,C_2199,D_2196))
      | ~ m1_subset_1(F_2195,k1_zfmisc_1(k2_zfmisc_1(D_2196,B_2198)))
      | ~ v1_funct_2(F_2195,D_2196,B_2198)
      | ~ v1_funct_1(F_2195)
      | ~ m1_subset_1(E_2200,k1_zfmisc_1(k2_zfmisc_1(C_2199,B_2198)))
      | ~ v1_funct_2(E_2200,C_2199,B_2198)
      | ~ v1_funct_1(E_2200)
      | ~ m1_subset_1(D_2196,k1_zfmisc_1(A_2197))
      | v1_xboole_0(D_2196)
      | ~ m1_subset_1(C_2199,k1_zfmisc_1(A_2197))
      | v1_xboole_0(C_2199)
      | v1_xboole_0(B_2198)
      | v1_xboole_0(A_2197) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_73030,plain,(
    ! [A_2378,B_2382,E_2379,D_2380,F_2383,C_2381] :
      ( k2_partfun1(k4_subset_1(A_2378,C_2381,D_2380),B_2382,k1_tmap_1(A_2378,B_2382,C_2381,D_2380,E_2379,F_2383),C_2381) = E_2379
      | ~ v1_funct_2(k1_tmap_1(A_2378,B_2382,C_2381,D_2380,E_2379,F_2383),k4_subset_1(A_2378,C_2381,D_2380),B_2382)
      | ~ v1_funct_1(k1_tmap_1(A_2378,B_2382,C_2381,D_2380,E_2379,F_2383))
      | k2_partfun1(D_2380,B_2382,F_2383,k9_subset_1(A_2378,C_2381,D_2380)) != k2_partfun1(C_2381,B_2382,E_2379,k9_subset_1(A_2378,C_2381,D_2380))
      | ~ m1_subset_1(F_2383,k1_zfmisc_1(k2_zfmisc_1(D_2380,B_2382)))
      | ~ v1_funct_2(F_2383,D_2380,B_2382)
      | ~ v1_funct_1(F_2383)
      | ~ m1_subset_1(E_2379,k1_zfmisc_1(k2_zfmisc_1(C_2381,B_2382)))
      | ~ v1_funct_2(E_2379,C_2381,B_2382)
      | ~ v1_funct_1(E_2379)
      | ~ m1_subset_1(D_2380,k1_zfmisc_1(A_2378))
      | v1_xboole_0(D_2380)
      | ~ m1_subset_1(C_2381,k1_zfmisc_1(A_2378))
      | v1_xboole_0(C_2381)
      | v1_xboole_0(B_2382)
      | v1_xboole_0(A_2378) ) ),
    inference(resolution,[status(thm)],[c_60,c_66855])).

tff(c_87351,plain,(
    ! [A_2560,B_2564,E_2561,C_2563,D_2562,F_2565] :
      ( k2_partfun1(k4_subset_1(A_2560,C_2563,D_2562),B_2564,k1_tmap_1(A_2560,B_2564,C_2563,D_2562,E_2561,F_2565),C_2563) = E_2561
      | ~ v1_funct_1(k1_tmap_1(A_2560,B_2564,C_2563,D_2562,E_2561,F_2565))
      | k2_partfun1(D_2562,B_2564,F_2565,k9_subset_1(A_2560,C_2563,D_2562)) != k2_partfun1(C_2563,B_2564,E_2561,k9_subset_1(A_2560,C_2563,D_2562))
      | ~ m1_subset_1(F_2565,k1_zfmisc_1(k2_zfmisc_1(D_2562,B_2564)))
      | ~ v1_funct_2(F_2565,D_2562,B_2564)
      | ~ v1_funct_1(F_2565)
      | ~ m1_subset_1(E_2561,k1_zfmisc_1(k2_zfmisc_1(C_2563,B_2564)))
      | ~ v1_funct_2(E_2561,C_2563,B_2564)
      | ~ v1_funct_1(E_2561)
      | ~ m1_subset_1(D_2562,k1_zfmisc_1(A_2560))
      | v1_xboole_0(D_2562)
      | ~ m1_subset_1(C_2563,k1_zfmisc_1(A_2560))
      | v1_xboole_0(C_2563)
      | v1_xboole_0(B_2564)
      | v1_xboole_0(A_2560) ) ),
    inference(resolution,[status(thm)],[c_62,c_73030])).

tff(c_87355,plain,(
    ! [A_2560,C_2563,E_2561] :
      ( k2_partfun1(k4_subset_1(A_2560,C_2563,'#skF_5'),'#skF_3',k1_tmap_1(A_2560,'#skF_3',C_2563,'#skF_5',E_2561,'#skF_7'),C_2563) = E_2561
      | ~ v1_funct_1(k1_tmap_1(A_2560,'#skF_3',C_2563,'#skF_5',E_2561,'#skF_7'))
      | k2_partfun1(C_2563,'#skF_3',E_2561,k9_subset_1(A_2560,C_2563,'#skF_5')) != k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1(A_2560,C_2563,'#skF_5'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_2561,k1_zfmisc_1(k2_zfmisc_1(C_2563,'#skF_3')))
      | ~ v1_funct_2(E_2561,C_2563,'#skF_3')
      | ~ v1_funct_1(E_2561)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2560))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_2563,k1_zfmisc_1(A_2560))
      | v1_xboole_0(C_2563)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2560) ) ),
    inference(resolution,[status(thm)],[c_68,c_87351])).

tff(c_87361,plain,(
    ! [A_2560,C_2563,E_2561] :
      ( k2_partfun1(k4_subset_1(A_2560,C_2563,'#skF_5'),'#skF_3',k1_tmap_1(A_2560,'#skF_3',C_2563,'#skF_5',E_2561,'#skF_7'),C_2563) = E_2561
      | ~ v1_funct_1(k1_tmap_1(A_2560,'#skF_3',C_2563,'#skF_5',E_2561,'#skF_7'))
      | k2_partfun1(C_2563,'#skF_3',E_2561,k9_subset_1(A_2560,C_2563,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_2560,C_2563,'#skF_5'))
      | ~ m1_subset_1(E_2561,k1_zfmisc_1(k2_zfmisc_1(C_2563,'#skF_3')))
      | ~ v1_funct_2(E_2561,C_2563,'#skF_3')
      | ~ v1_funct_1(E_2561)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2560))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_2563,k1_zfmisc_1(A_2560))
      | v1_xboole_0(C_2563)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2560) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_65633,c_87355])).

tff(c_99324,plain,(
    ! [A_2673,C_2674,E_2675] :
      ( k2_partfun1(k4_subset_1(A_2673,C_2674,'#skF_5'),'#skF_3',k1_tmap_1(A_2673,'#skF_3',C_2674,'#skF_5',E_2675,'#skF_7'),C_2674) = E_2675
      | ~ v1_funct_1(k1_tmap_1(A_2673,'#skF_3',C_2674,'#skF_5',E_2675,'#skF_7'))
      | k2_partfun1(C_2674,'#skF_3',E_2675,k9_subset_1(A_2673,C_2674,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_2673,C_2674,'#skF_5'))
      | ~ m1_subset_1(E_2675,k1_zfmisc_1(k2_zfmisc_1(C_2674,'#skF_3')))
      | ~ v1_funct_2(E_2675,C_2674,'#skF_3')
      | ~ v1_funct_1(E_2675)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2673))
      | ~ m1_subset_1(C_2674,k1_zfmisc_1(A_2673))
      | v1_xboole_0(C_2674)
      | v1_xboole_0(A_2673) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_87361])).

tff(c_99331,plain,(
    ! [A_2673] :
      ( k2_partfun1(k4_subset_1(A_2673,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_2673,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_2673,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1(A_2673,'#skF_4','#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_2673,'#skF_4','#skF_5'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2673))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2673))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_2673) ) ),
    inference(resolution,[status(thm)],[c_74,c_99324])).

tff(c_99341,plain,(
    ! [A_2673] :
      ( k2_partfun1(k4_subset_1(A_2673,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_2673,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_2673,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_2673,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_2673,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2673))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2673))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_2673) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_65636,c_99331])).

tff(c_100460,plain,(
    ! [A_2685] :
      ( k2_partfun1(k4_subset_1(A_2685,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_2685,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_2685,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_2685,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_2685,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2685))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2685))
      | v1_xboole_0(A_2685) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_99341])).

tff(c_64482,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_6549])).

tff(c_67083,plain,(
    ! [C_2211,B_2210,D_2208,G_2207,A_2209] :
      ( k1_tmap_1(A_2209,B_2210,C_2211,D_2208,k2_partfun1(k4_subset_1(A_2209,C_2211,D_2208),B_2210,G_2207,C_2211),k2_partfun1(k4_subset_1(A_2209,C_2211,D_2208),B_2210,G_2207,D_2208)) = G_2207
      | ~ m1_subset_1(G_2207,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_2209,C_2211,D_2208),B_2210)))
      | ~ v1_funct_2(G_2207,k4_subset_1(A_2209,C_2211,D_2208),B_2210)
      | ~ v1_funct_1(G_2207)
      | k2_partfun1(D_2208,B_2210,k2_partfun1(k4_subset_1(A_2209,C_2211,D_2208),B_2210,G_2207,D_2208),k9_subset_1(A_2209,C_2211,D_2208)) != k2_partfun1(C_2211,B_2210,k2_partfun1(k4_subset_1(A_2209,C_2211,D_2208),B_2210,G_2207,C_2211),k9_subset_1(A_2209,C_2211,D_2208))
      | ~ m1_subset_1(k2_partfun1(k4_subset_1(A_2209,C_2211,D_2208),B_2210,G_2207,D_2208),k1_zfmisc_1(k2_zfmisc_1(D_2208,B_2210)))
      | ~ v1_funct_2(k2_partfun1(k4_subset_1(A_2209,C_2211,D_2208),B_2210,G_2207,D_2208),D_2208,B_2210)
      | ~ v1_funct_1(k2_partfun1(k4_subset_1(A_2209,C_2211,D_2208),B_2210,G_2207,D_2208))
      | ~ m1_subset_1(k2_partfun1(k4_subset_1(A_2209,C_2211,D_2208),B_2210,G_2207,C_2211),k1_zfmisc_1(k2_zfmisc_1(C_2211,B_2210)))
      | ~ v1_funct_2(k2_partfun1(k4_subset_1(A_2209,C_2211,D_2208),B_2210,G_2207,C_2211),C_2211,B_2210)
      | ~ v1_funct_1(k2_partfun1(k4_subset_1(A_2209,C_2211,D_2208),B_2210,G_2207,C_2211))
      | ~ m1_subset_1(D_2208,k1_zfmisc_1(A_2209))
      | v1_xboole_0(D_2208)
      | ~ m1_subset_1(C_2211,k1_zfmisc_1(A_2209))
      | v1_xboole_0(C_2211)
      | v1_xboole_0(B_2210)
      | v1_xboole_0(A_2209) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_67085,plain,
    ( k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5',k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5')) = k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3')))
    | ~ v1_funct_2(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3')
    | ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | k2_partfun1('#skF_5','#skF_3',k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5'),k9_subset_1('#skF_2','#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3',k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),k9_subset_1('#skF_2','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5'),'#skF_5','#skF_3')
    | ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5'))
    | ~ m1_subset_1(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_64482,c_67083])).

tff(c_67087,plain,
    ( k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5',k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),'#skF_7') = k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3')))
    | ~ v1_funct_2(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3')
    | ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | k2_partfun1('#skF_4','#skF_3',k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),k1_xboole_0) != k1_xboole_0
    | ~ m1_subset_1(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'))
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_72,c_64482,c_70,c_64482,c_68,c_65777,c_66102,c_66102,c_65633,c_64482,c_64603,c_64603,c_64482,c_67085])).

tff(c_67088,plain,
    ( k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5',k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),'#skF_7') = k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3')))
    | ~ v1_funct_2(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3')
    | ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | k2_partfun1('#skF_4','#skF_3',k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),k1_xboole_0) != k1_xboole_0
    | ~ m1_subset_1(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_90,c_88,c_84,c_67087])).

tff(c_68873,plain,
    ( k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5',k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),'#skF_7') = k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3')))
    | ~ v1_funct_2(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3')
    | k2_partfun1('#skF_4','#skF_3',k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),k1_xboole_0) != k1_xboole_0
    | ~ m1_subset_1(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67310,c_67088])).

tff(c_68874,plain,(
    ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_68873])).

tff(c_100469,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_100460,c_68874])).

tff(c_100482,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_65958,c_66102,c_65777,c_66102,c_64603,c_64603,c_67310,c_78,c_100469])).

tff(c_100484,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_100482])).

tff(c_100485,plain,
    ( ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | k2_partfun1('#skF_4','#skF_3',k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),k1_xboole_0) != k1_xboole_0
    | ~ v1_funct_2(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3')
    | ~ m1_subset_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3')))
    | k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5',k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),'#skF_7') = k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_68873])).

tff(c_101339,plain,(
    ~ m1_subset_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_100485])).

tff(c_104969,plain,
    ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_101339])).

tff(c_104972,plain,
    ( v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_78,c_76,c_74,c_72,c_70,c_68,c_104969])).

tff(c_104974,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_90,c_88,c_84,c_104972])).

tff(c_104976,plain,(
    m1_subset_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_100485])).

tff(c_44,plain,(
    ! [C_36,A_33,B_34] :
      ( v1_partfun1(C_36,A_33)
      | ~ v1_funct_2(C_36,A_33,B_34)
      | ~ v1_funct_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34)))
      | v1_xboole_0(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_108626,plain,
    ( v1_partfun1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k4_subset_1('#skF_2','#skF_4','#skF_5'))
    | ~ v1_funct_2(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3')
    | ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_104976,c_44])).

tff(c_108679,plain,
    ( v1_partfun1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k4_subset_1('#skF_2','#skF_4','#skF_5'))
    | ~ v1_funct_2(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67310,c_108626])).

tff(c_108680,plain,
    ( v1_partfun1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k4_subset_1('#skF_2','#skF_4','#skF_5'))
    | ~ v1_funct_2(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_108679])).

tff(c_109054,plain,(
    ~ v1_funct_2(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_108680])).

tff(c_109838,plain,
    ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_109054])).

tff(c_109841,plain,
    ( v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_78,c_76,c_74,c_72,c_70,c_68,c_109838])).

tff(c_109843,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_90,c_88,c_84,c_109841])).

tff(c_109845,plain,(
    v1_funct_2(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_108680])).

tff(c_66858,plain,(
    ! [A_170,D_173,E_174,B_171,C_172,F_175] :
      ( k2_partfun1(k4_subset_1(A_170,C_172,D_173),B_171,k1_tmap_1(A_170,B_171,C_172,D_173,E_174,F_175),C_172) = E_174
      | ~ v1_funct_2(k1_tmap_1(A_170,B_171,C_172,D_173,E_174,F_175),k4_subset_1(A_170,C_172,D_173),B_171)
      | ~ v1_funct_1(k1_tmap_1(A_170,B_171,C_172,D_173,E_174,F_175))
      | k2_partfun1(D_173,B_171,F_175,k9_subset_1(A_170,C_172,D_173)) != k2_partfun1(C_172,B_171,E_174,k9_subset_1(A_170,C_172,D_173))
      | ~ m1_subset_1(F_175,k1_zfmisc_1(k2_zfmisc_1(D_173,B_171)))
      | ~ v1_funct_2(F_175,D_173,B_171)
      | ~ v1_funct_1(F_175)
      | ~ m1_subset_1(E_174,k1_zfmisc_1(k2_zfmisc_1(C_172,B_171)))
      | ~ v1_funct_2(E_174,C_172,B_171)
      | ~ v1_funct_1(E_174)
      | ~ m1_subset_1(D_173,k1_zfmisc_1(A_170))
      | v1_xboole_0(D_173)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(A_170))
      | v1_xboole_0(C_172)
      | v1_xboole_0(B_171)
      | v1_xboole_0(A_170) ) ),
    inference(resolution,[status(thm)],[c_60,c_66855])).

tff(c_111781,plain,
    ( k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
    | ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_109845,c_66858])).

tff(c_111789,plain,
    ( k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_78,c_76,c_74,c_72,c_70,c_68,c_65958,c_66102,c_64603,c_65777,c_66102,c_64603,c_65633,c_65636,c_67310,c_111781])).

tff(c_111791,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_90,c_88,c_84,c_64481,c_111789])).

tff(c_111792,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_6993])).

tff(c_111793,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_6993])).

tff(c_111820,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111792,c_111793])).

tff(c_111886,plain,(
    ! [C_3045,A_3046,B_3047] :
      ( v4_relat_1(C_3045,A_3046)
      | ~ m1_subset_1(C_3045,k1_zfmisc_1(k2_zfmisc_1(A_3046,B_3047))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_111894,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_111886])).

tff(c_113088,plain,(
    ! [B_3133,A_3134] :
      ( k1_relat_1(B_3133) = A_3134
      | ~ v1_partfun1(B_3133,A_3134)
      | ~ v4_relat_1(B_3133,A_3134)
      | ~ v1_relat_1(B_3133) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_113094,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_111894,c_113088])).

tff(c_113103,plain,
    ( '#skF_6' = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6977,c_111820,c_113094])).

tff(c_113107,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_113103])).

tff(c_113844,plain,(
    ! [C_3180,A_3181,B_3182] :
      ( v1_partfun1(C_3180,A_3181)
      | ~ v1_funct_2(C_3180,A_3181,B_3182)
      | ~ v1_funct_1(C_3180)
      | ~ m1_subset_1(C_3180,k1_zfmisc_1(k2_zfmisc_1(A_3181,B_3182)))
      | v1_xboole_0(B_3182) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_113850,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_113844])).

tff(c_113857,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_113850])).

tff(c_113859,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_113107,c_113857])).

tff(c_113860,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_113103])).

tff(c_113889,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113860,c_78])).

tff(c_113888,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113860,c_76])).

tff(c_113887,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113860,c_74])).

tff(c_114278,plain,(
    ! [F_3217,A_3212,B_3216,E_3213,C_3215,D_3214] :
      ( v1_funct_1(k1_tmap_1(A_3212,B_3216,C_3215,D_3214,E_3213,F_3217))
      | ~ m1_subset_1(F_3217,k1_zfmisc_1(k2_zfmisc_1(D_3214,B_3216)))
      | ~ v1_funct_2(F_3217,D_3214,B_3216)
      | ~ v1_funct_1(F_3217)
      | ~ m1_subset_1(E_3213,k1_zfmisc_1(k2_zfmisc_1(C_3215,B_3216)))
      | ~ v1_funct_2(E_3213,C_3215,B_3216)
      | ~ v1_funct_1(E_3213)
      | ~ m1_subset_1(D_3214,k1_zfmisc_1(A_3212))
      | v1_xboole_0(D_3214)
      | ~ m1_subset_1(C_3215,k1_zfmisc_1(A_3212))
      | v1_xboole_0(C_3215)
      | v1_xboole_0(B_3216)
      | v1_xboole_0(A_3212) ) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_114282,plain,(
    ! [A_3212,C_3215,E_3213] :
      ( v1_funct_1(k1_tmap_1(A_3212,'#skF_3',C_3215,'#skF_5',E_3213,'#skF_7'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_3213,k1_zfmisc_1(k2_zfmisc_1(C_3215,'#skF_3')))
      | ~ v1_funct_2(E_3213,C_3215,'#skF_3')
      | ~ v1_funct_1(E_3213)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3212))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_3215,k1_zfmisc_1(A_3212))
      | v1_xboole_0(C_3215)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_3212) ) ),
    inference(resolution,[status(thm)],[c_68,c_114278])).

tff(c_114289,plain,(
    ! [A_3212,C_3215,E_3213] :
      ( v1_funct_1(k1_tmap_1(A_3212,'#skF_3',C_3215,'#skF_5',E_3213,'#skF_7'))
      | ~ m1_subset_1(E_3213,k1_zfmisc_1(k2_zfmisc_1(C_3215,'#skF_3')))
      | ~ v1_funct_2(E_3213,C_3215,'#skF_3')
      | ~ v1_funct_1(E_3213)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3212))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_3215,k1_zfmisc_1(A_3212))
      | v1_xboole_0(C_3215)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_3212) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_114282])).

tff(c_114572,plain,(
    ! [A_3242,C_3243,E_3244] :
      ( v1_funct_1(k1_tmap_1(A_3242,'#skF_3',C_3243,'#skF_5',E_3244,'#skF_7'))
      | ~ m1_subset_1(E_3244,k1_zfmisc_1(k2_zfmisc_1(C_3243,'#skF_3')))
      | ~ v1_funct_2(E_3244,C_3243,'#skF_3')
      | ~ v1_funct_1(E_3244)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3242))
      | ~ m1_subset_1(C_3243,k1_zfmisc_1(A_3242))
      | v1_xboole_0(C_3243)
      | v1_xboole_0(A_3242) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_114289])).

tff(c_114577,plain,(
    ! [A_3242] :
      ( v1_funct_1(k1_tmap_1(A_3242,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | ~ v1_funct_2('#skF_4','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3242))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3242))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_3242) ) ),
    inference(resolution,[status(thm)],[c_113887,c_114572])).

tff(c_114585,plain,(
    ! [A_3242] :
      ( v1_funct_1(k1_tmap_1(A_3242,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3242))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3242))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_3242) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113889,c_113888,c_114577])).

tff(c_114854,plain,(
    ! [A_3271] :
      ( v1_funct_1(k1_tmap_1(A_3271,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3271))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3271))
      | v1_xboole_0(A_3271) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_114585])).

tff(c_114857,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_114854])).

tff(c_114860,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_114857])).

tff(c_114861,plain,(
    v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_114860])).

tff(c_114518,plain,(
    ! [A_3234,F_3239,D_3236,B_3238,C_3237,E_3235] :
      ( m1_subset_1(k1_tmap_1(A_3234,B_3238,C_3237,D_3236,E_3235,F_3239),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_3234,C_3237,D_3236),B_3238)))
      | ~ m1_subset_1(F_3239,k1_zfmisc_1(k2_zfmisc_1(D_3236,B_3238)))
      | ~ v1_funct_2(F_3239,D_3236,B_3238)
      | ~ v1_funct_1(F_3239)
      | ~ m1_subset_1(E_3235,k1_zfmisc_1(k2_zfmisc_1(C_3237,B_3238)))
      | ~ v1_funct_2(E_3235,C_3237,B_3238)
      | ~ v1_funct_1(E_3235)
      | ~ m1_subset_1(D_3236,k1_zfmisc_1(A_3234))
      | v1_xboole_0(D_3236)
      | ~ m1_subset_1(C_3237,k1_zfmisc_1(A_3234))
      | v1_xboole_0(C_3237)
      | v1_xboole_0(B_3238)
      | v1_xboole_0(A_3234) ) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_127627,plain,(
    ! [F_3620,A_3618,D_3622,C_3624,B_3619,D_3621,E_3623] :
      ( k2_partfun1(k4_subset_1(A_3618,C_3624,D_3621),B_3619,k1_tmap_1(A_3618,B_3619,C_3624,D_3621,E_3623,F_3620),D_3622) = k7_relat_1(k1_tmap_1(A_3618,B_3619,C_3624,D_3621,E_3623,F_3620),D_3622)
      | ~ v1_funct_1(k1_tmap_1(A_3618,B_3619,C_3624,D_3621,E_3623,F_3620))
      | ~ m1_subset_1(F_3620,k1_zfmisc_1(k2_zfmisc_1(D_3621,B_3619)))
      | ~ v1_funct_2(F_3620,D_3621,B_3619)
      | ~ v1_funct_1(F_3620)
      | ~ m1_subset_1(E_3623,k1_zfmisc_1(k2_zfmisc_1(C_3624,B_3619)))
      | ~ v1_funct_2(E_3623,C_3624,B_3619)
      | ~ v1_funct_1(E_3623)
      | ~ m1_subset_1(D_3621,k1_zfmisc_1(A_3618))
      | v1_xboole_0(D_3621)
      | ~ m1_subset_1(C_3624,k1_zfmisc_1(A_3618))
      | v1_xboole_0(C_3624)
      | v1_xboole_0(B_3619)
      | v1_xboole_0(A_3618) ) ),
    inference(resolution,[status(thm)],[c_114518,c_52])).

tff(c_127633,plain,(
    ! [A_3618,C_3624,E_3623,D_3622] :
      ( k2_partfun1(k4_subset_1(A_3618,C_3624,'#skF_5'),'#skF_3',k1_tmap_1(A_3618,'#skF_3',C_3624,'#skF_5',E_3623,'#skF_7'),D_3622) = k7_relat_1(k1_tmap_1(A_3618,'#skF_3',C_3624,'#skF_5',E_3623,'#skF_7'),D_3622)
      | ~ v1_funct_1(k1_tmap_1(A_3618,'#skF_3',C_3624,'#skF_5',E_3623,'#skF_7'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_3623,k1_zfmisc_1(k2_zfmisc_1(C_3624,'#skF_3')))
      | ~ v1_funct_2(E_3623,C_3624,'#skF_3')
      | ~ v1_funct_1(E_3623)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3618))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_3624,k1_zfmisc_1(A_3618))
      | v1_xboole_0(C_3624)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_3618) ) ),
    inference(resolution,[status(thm)],[c_68,c_127627])).

tff(c_127641,plain,(
    ! [A_3618,C_3624,E_3623,D_3622] :
      ( k2_partfun1(k4_subset_1(A_3618,C_3624,'#skF_5'),'#skF_3',k1_tmap_1(A_3618,'#skF_3',C_3624,'#skF_5',E_3623,'#skF_7'),D_3622) = k7_relat_1(k1_tmap_1(A_3618,'#skF_3',C_3624,'#skF_5',E_3623,'#skF_7'),D_3622)
      | ~ v1_funct_1(k1_tmap_1(A_3618,'#skF_3',C_3624,'#skF_5',E_3623,'#skF_7'))
      | ~ m1_subset_1(E_3623,k1_zfmisc_1(k2_zfmisc_1(C_3624,'#skF_3')))
      | ~ v1_funct_2(E_3623,C_3624,'#skF_3')
      | ~ v1_funct_1(E_3623)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3618))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_3624,k1_zfmisc_1(A_3618))
      | v1_xboole_0(C_3624)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_3618) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_127633])).

tff(c_129779,plain,(
    ! [A_3683,C_3684,E_3685,D_3686] :
      ( k2_partfun1(k4_subset_1(A_3683,C_3684,'#skF_5'),'#skF_3',k1_tmap_1(A_3683,'#skF_3',C_3684,'#skF_5',E_3685,'#skF_7'),D_3686) = k7_relat_1(k1_tmap_1(A_3683,'#skF_3',C_3684,'#skF_5',E_3685,'#skF_7'),D_3686)
      | ~ v1_funct_1(k1_tmap_1(A_3683,'#skF_3',C_3684,'#skF_5',E_3685,'#skF_7'))
      | ~ m1_subset_1(E_3685,k1_zfmisc_1(k2_zfmisc_1(C_3684,'#skF_3')))
      | ~ v1_funct_2(E_3685,C_3684,'#skF_3')
      | ~ v1_funct_1(E_3685)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3683))
      | ~ m1_subset_1(C_3684,k1_zfmisc_1(A_3683))
      | v1_xboole_0(C_3684)
      | v1_xboole_0(A_3683) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_127641])).

tff(c_129784,plain,(
    ! [A_3683,D_3686] :
      ( k2_partfun1(k4_subset_1(A_3683,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_3683,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),D_3686) = k7_relat_1(k1_tmap_1(A_3683,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),D_3686)
      | ~ v1_funct_1(k1_tmap_1(A_3683,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | ~ v1_funct_2('#skF_4','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3683))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3683))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_3683) ) ),
    inference(resolution,[status(thm)],[c_113887,c_129779])).

tff(c_129792,plain,(
    ! [A_3683,D_3686] :
      ( k2_partfun1(k4_subset_1(A_3683,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_3683,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),D_3686) = k7_relat_1(k1_tmap_1(A_3683,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),D_3686)
      | ~ v1_funct_1(k1_tmap_1(A_3683,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3683))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3683))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_3683) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113889,c_113888,c_129784])).

tff(c_131306,plain,(
    ! [A_3705,D_3706] :
      ( k2_partfun1(k4_subset_1(A_3705,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_3705,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),D_3706) = k7_relat_1(k1_tmap_1(A_3705,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),D_3706)
      | ~ v1_funct_1(k1_tmap_1(A_3705,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3705))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3705))
      | v1_xboole_0(A_3705) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_129792])).

tff(c_113863,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),'#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113860,c_113860,c_64481])).

tff(c_131315,plain,
    ( k7_relat_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),'#skF_4') != '#skF_4'
    | ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_131306,c_113863])).

tff(c_131333,plain,
    ( k7_relat_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),'#skF_4') != '#skF_4'
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_114861,c_131315])).

tff(c_131334,plain,(
    k7_relat_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),'#skF_4') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_131333])).

tff(c_34,plain,(
    ! [C_27,A_25,B_26] :
      ( v1_relat_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_126097,plain,(
    ! [D_3557,B_3555,F_3556,C_3559,E_3558,A_3554] :
      ( v1_relat_1(k1_tmap_1(A_3554,B_3555,C_3559,D_3557,E_3558,F_3556))
      | ~ m1_subset_1(F_3556,k1_zfmisc_1(k2_zfmisc_1(D_3557,B_3555)))
      | ~ v1_funct_2(F_3556,D_3557,B_3555)
      | ~ v1_funct_1(F_3556)
      | ~ m1_subset_1(E_3558,k1_zfmisc_1(k2_zfmisc_1(C_3559,B_3555)))
      | ~ v1_funct_2(E_3558,C_3559,B_3555)
      | ~ v1_funct_1(E_3558)
      | ~ m1_subset_1(D_3557,k1_zfmisc_1(A_3554))
      | v1_xboole_0(D_3557)
      | ~ m1_subset_1(C_3559,k1_zfmisc_1(A_3554))
      | v1_xboole_0(C_3559)
      | v1_xboole_0(B_3555)
      | v1_xboole_0(A_3554) ) ),
    inference(resolution,[status(thm)],[c_114518,c_34])).

tff(c_126103,plain,(
    ! [A_3554,C_3559,E_3558] :
      ( v1_relat_1(k1_tmap_1(A_3554,'#skF_3',C_3559,'#skF_5',E_3558,'#skF_7'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_3558,k1_zfmisc_1(k2_zfmisc_1(C_3559,'#skF_3')))
      | ~ v1_funct_2(E_3558,C_3559,'#skF_3')
      | ~ v1_funct_1(E_3558)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3554))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_3559,k1_zfmisc_1(A_3554))
      | v1_xboole_0(C_3559)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_3554) ) ),
    inference(resolution,[status(thm)],[c_68,c_126097])).

tff(c_126111,plain,(
    ! [A_3554,C_3559,E_3558] :
      ( v1_relat_1(k1_tmap_1(A_3554,'#skF_3',C_3559,'#skF_5',E_3558,'#skF_7'))
      | ~ m1_subset_1(E_3558,k1_zfmisc_1(k2_zfmisc_1(C_3559,'#skF_3')))
      | ~ v1_funct_2(E_3558,C_3559,'#skF_3')
      | ~ v1_funct_1(E_3558)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3554))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_3559,k1_zfmisc_1(A_3554))
      | v1_xboole_0(C_3559)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_3554) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_126103])).

tff(c_126122,plain,(
    ! [A_3560,C_3561,E_3562] :
      ( v1_relat_1(k1_tmap_1(A_3560,'#skF_3',C_3561,'#skF_5',E_3562,'#skF_7'))
      | ~ m1_subset_1(E_3562,k1_zfmisc_1(k2_zfmisc_1(C_3561,'#skF_3')))
      | ~ v1_funct_2(E_3562,C_3561,'#skF_3')
      | ~ v1_funct_1(E_3562)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3560))
      | ~ m1_subset_1(C_3561,k1_zfmisc_1(A_3560))
      | v1_xboole_0(C_3561)
      | v1_xboole_0(A_3560) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_126111])).

tff(c_126127,plain,(
    ! [A_3560] :
      ( v1_relat_1(k1_tmap_1(A_3560,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | ~ v1_funct_2('#skF_4','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3560))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3560))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_3560) ) ),
    inference(resolution,[status(thm)],[c_113887,c_126122])).

tff(c_126135,plain,(
    ! [A_3560] :
      ( v1_relat_1(k1_tmap_1(A_3560,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3560))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3560))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_3560) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113889,c_113888,c_126127])).

tff(c_126675,plain,(
    ! [A_3586] :
      ( v1_relat_1(k1_tmap_1(A_3586,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3586))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3586))
      | v1_xboole_0(A_3586) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_126135])).

tff(c_126678,plain,
    ( v1_relat_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_126675])).

tff(c_126681,plain,
    ( v1_relat_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_126678])).

tff(c_126682,plain,(
    v1_relat_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_126681])).

tff(c_18,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_111814,plain,(
    k2_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111792,c_111792,c_18])).

tff(c_113883,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113860,c_113860,c_111814])).

tff(c_113884,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113860,c_113860,c_111820])).

tff(c_28,plain,(
    ! [A_22] :
      ( k7_relat_1(A_22,k1_relat_1(A_22)) = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_113885,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113860,c_111792])).

tff(c_6901,plain,(
    ! [A_799] :
      ( k1_relat_1(A_799) != k1_xboole_0
      | k1_xboole_0 = A_799
      | ~ v1_relat_1(A_799) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6912,plain,(
    ! [A_11,B_12] :
      ( k1_relat_1(k7_relat_1(A_11,B_12)) != k1_xboole_0
      | k7_relat_1(A_11,B_12) = k1_xboole_0
      | ~ v1_relat_1(A_11) ) ),
    inference(resolution,[status(thm)],[c_12,c_6901])).

tff(c_114653,plain,(
    ! [A_3248,B_3249] :
      ( k1_relat_1(k7_relat_1(A_3248,B_3249)) != '#skF_4'
      | k7_relat_1(A_3248,B_3249) = '#skF_4'
      | ~ v1_relat_1(A_3248) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113885,c_113885,c_6912])).

tff(c_115056,plain,(
    ! [A_3283] :
      ( k1_relat_1(A_3283) != '#skF_4'
      | k7_relat_1(A_3283,k1_relat_1(A_3283)) = '#skF_4'
      | ~ v1_relat_1(A_3283)
      | ~ v1_relat_1(A_3283) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_114653])).

tff(c_114652,plain,(
    ! [A_11,B_12] :
      ( k1_relat_1(k7_relat_1(A_11,B_12)) != '#skF_4'
      | k7_relat_1(A_11,B_12) = '#skF_4'
      | ~ v1_relat_1(A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113885,c_113885,c_6912])).

tff(c_115065,plain,(
    ! [A_3283] :
      ( k1_relat_1('#skF_4') != '#skF_4'
      | k7_relat_1(A_3283,k1_relat_1(A_3283)) = '#skF_4'
      | ~ v1_relat_1(A_3283)
      | k1_relat_1(A_3283) != '#skF_4'
      | ~ v1_relat_1(A_3283)
      | ~ v1_relat_1(A_3283) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115056,c_114652])).

tff(c_115123,plain,(
    ! [A_3283] :
      ( k7_relat_1(A_3283,k1_relat_1(A_3283)) = '#skF_4'
      | k1_relat_1(A_3283) != '#skF_4'
      | ~ v1_relat_1(A_3283) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113884,c_115065])).

tff(c_111809,plain,(
    k7_relat_1('#skF_6','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111792,c_111792,c_111792,c_6880])).

tff(c_113879,plain,(
    k7_relat_1('#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113860,c_113860,c_113860,c_111809])).

tff(c_6913,plain,(
    ! [A_800] :
      ( k2_relat_1(A_800) != k1_xboole_0
      | k1_xboole_0 = A_800
      | ~ v1_relat_1(A_800) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6924,plain,(
    ! [A_11,B_12] :
      ( k2_relat_1(k7_relat_1(A_11,B_12)) != k1_xboole_0
      | k7_relat_1(A_11,B_12) = k1_xboole_0
      | ~ v1_relat_1(A_11) ) ),
    inference(resolution,[status(thm)],[c_12,c_6913])).

tff(c_114615,plain,(
    ! [A_3246,B_3247] :
      ( k2_relat_1(k7_relat_1(A_3246,B_3247)) != '#skF_4'
      | k7_relat_1(A_3246,B_3247) = '#skF_4'
      | ~ v1_relat_1(A_3246) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113885,c_113885,c_6924])).

tff(c_114866,plain,(
    ! [A_3277] :
      ( k2_relat_1(A_3277) != '#skF_4'
      | k7_relat_1(A_3277,k1_relat_1(A_3277)) = '#skF_4'
      | ~ v1_relat_1(A_3277)
      | ~ v1_relat_1(A_3277) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_114615])).

tff(c_114872,plain,(
    ! [A_3277] :
      ( k1_relat_1('#skF_4') != '#skF_4'
      | k7_relat_1(A_3277,k1_relat_1(A_3277)) = '#skF_4'
      | ~ v1_relat_1(A_3277)
      | k2_relat_1(A_3277) != '#skF_4'
      | ~ v1_relat_1(A_3277)
      | ~ v1_relat_1(A_3277) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114866,c_114652])).

tff(c_114946,plain,(
    ! [A_3278] :
      ( k7_relat_1(A_3278,k1_relat_1(A_3278)) = '#skF_4'
      | k2_relat_1(A_3278) != '#skF_4'
      | ~ v1_relat_1(A_3278) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113884,c_114872])).

tff(c_114973,plain,(
    ! [A_3278] :
      ( r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(A_3278))
      | ~ v1_relat_1(A_3278)
      | k2_relat_1(A_3278) != '#skF_4'
      | ~ v1_relat_1(A_3278) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114946,c_26])).

tff(c_115014,plain,(
    ! [A_3278] :
      ( r1_tarski('#skF_4',k1_relat_1(A_3278))
      | ~ v1_relat_1(A_3278)
      | k2_relat_1(A_3278) != '#skF_4'
      | ~ v1_relat_1(A_3278) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113884,c_114973])).

tff(c_130477,plain,(
    ! [A_3700,A_3701] :
      ( k7_relat_1(A_3700,A_3701) = k7_relat_1('#skF_4',A_3701)
      | ~ r1_tarski(A_3701,k1_relat_1(A_3700))
      | ~ v1_relat_1(A_3700)
      | k2_relat_1(A_3700) != '#skF_4'
      | ~ v1_relat_1(A_3700) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114946,c_14])).

tff(c_130530,plain,(
    ! [A_3278] :
      ( k7_relat_1(A_3278,'#skF_4') = k7_relat_1('#skF_4','#skF_4')
      | k2_relat_1(A_3278) != '#skF_4'
      | ~ v1_relat_1(A_3278) ) ),
    inference(resolution,[status(thm)],[c_115014,c_130477])).

tff(c_130588,plain,(
    ! [A_3702] :
      ( k7_relat_1(A_3702,'#skF_4') = '#skF_4'
      | k2_relat_1(A_3702) != '#skF_4'
      | ~ v1_relat_1(A_3702) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113879,c_130530])).

tff(c_131873,plain,(
    ! [A_3715,B_3716] :
      ( k7_relat_1(k7_relat_1(A_3715,B_3716),'#skF_4') = '#skF_4'
      | k2_relat_1(k7_relat_1(A_3715,B_3716)) != '#skF_4'
      | ~ v1_relat_1(A_3715) ) ),
    inference(resolution,[status(thm)],[c_12,c_130588])).

tff(c_132568,plain,(
    ! [A_3721] :
      ( k7_relat_1(A_3721,'#skF_4') = '#skF_4'
      | k2_relat_1(k7_relat_1(A_3721,k1_relat_1(A_3721))) != '#skF_4'
      | ~ v1_relat_1(A_3721)
      | ~ v1_relat_1(A_3721) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_131873])).

tff(c_132602,plain,(
    ! [A_3283] :
      ( k7_relat_1(A_3283,'#skF_4') = '#skF_4'
      | k2_relat_1('#skF_4') != '#skF_4'
      | ~ v1_relat_1(A_3283)
      | ~ v1_relat_1(A_3283)
      | k1_relat_1(A_3283) != '#skF_4'
      | ~ v1_relat_1(A_3283) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115123,c_132568])).

tff(c_132645,plain,(
    ! [A_3722] :
      ( k7_relat_1(A_3722,'#skF_4') = '#skF_4'
      | k1_relat_1(A_3722) != '#skF_4'
      | ~ v1_relat_1(A_3722) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113883,c_132602])).

tff(c_132687,plain,
    ( k7_relat_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),'#skF_4') = '#skF_4'
    | k1_relat_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_126682,c_132645])).

tff(c_132736,plain,(
    k1_relat_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_131334,c_132687])).

tff(c_111812,plain,(
    ! [A_31] :
      ( r1_xboole_0('#skF_1'(A_31),A_31)
      | A_31 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111792,c_40])).

tff(c_113876,plain,(
    ! [A_31] :
      ( r1_xboole_0('#skF_1'(A_31),A_31)
      | A_31 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113860,c_111812])).

tff(c_112966,plain,(
    ! [A_16,B_18] :
      ( k7_relat_1(A_16,B_18) = '#skF_6'
      | ~ r1_xboole_0(B_18,k1_relat_1(A_16))
      | ~ v1_relat_1(A_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111792,c_16])).

tff(c_114367,plain,(
    ! [A_3223,B_3224] :
      ( k7_relat_1(A_3223,B_3224) = '#skF_4'
      | ~ r1_xboole_0(B_3224,k1_relat_1(A_3223))
      | ~ v1_relat_1(A_3223) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113860,c_112966])).

tff(c_114769,plain,(
    ! [A_3264] :
      ( k7_relat_1(A_3264,'#skF_1'(k1_relat_1(A_3264))) = '#skF_4'
      | ~ v1_relat_1(A_3264)
      | k1_relat_1(A_3264) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_113876,c_114367])).

tff(c_114796,plain,(
    ! [A_3264] :
      ( r1_tarski(k1_relat_1('#skF_4'),'#skF_1'(k1_relat_1(A_3264)))
      | ~ v1_relat_1(A_3264)
      | ~ v1_relat_1(A_3264)
      | k1_relat_1(A_3264) = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114769,c_26])).

tff(c_114833,plain,(
    ! [A_3264] :
      ( r1_tarski('#skF_4','#skF_1'(k1_relat_1(A_3264)))
      | ~ v1_relat_1(A_3264)
      | ~ v1_relat_1(A_3264)
      | k1_relat_1(A_3264) = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113884,c_114796])).

tff(c_114387,plain,(
    ! [A_3223] :
      ( k7_relat_1(A_3223,'#skF_1'(k1_relat_1(A_3223))) = '#skF_4'
      | ~ v1_relat_1(A_3223)
      | k1_relat_1(A_3223) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_113876,c_114367])).

tff(c_134191,plain,(
    ! [A_3748,B_3749] :
      ( k7_relat_1(A_3748,'#skF_4') = '#skF_4'
      | ~ r1_tarski('#skF_4',B_3749)
      | ~ v1_relat_1(A_3748)
      | k2_relat_1(k7_relat_1(A_3748,B_3749)) != '#skF_4'
      | ~ v1_relat_1(A_3748) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131873,c_14])).

tff(c_134269,plain,(
    ! [A_3223] :
      ( k7_relat_1(A_3223,'#skF_4') = '#skF_4'
      | ~ r1_tarski('#skF_4','#skF_1'(k1_relat_1(A_3223)))
      | ~ v1_relat_1(A_3223)
      | k2_relat_1('#skF_4') != '#skF_4'
      | ~ v1_relat_1(A_3223)
      | ~ v1_relat_1(A_3223)
      | k1_relat_1(A_3223) = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114387,c_134191])).

tff(c_134562,plain,(
    ! [A_3766] :
      ( k7_relat_1(A_3766,'#skF_4') = '#skF_4'
      | ~ r1_tarski('#skF_4','#skF_1'(k1_relat_1(A_3766)))
      | ~ v1_relat_1(A_3766)
      | k1_relat_1(A_3766) = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113883,c_134269])).

tff(c_134602,plain,(
    ! [A_3773] :
      ( k7_relat_1(A_3773,'#skF_4') = '#skF_4'
      | ~ v1_relat_1(A_3773)
      | k1_relat_1(A_3773) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_114833,c_134562])).

tff(c_134650,plain,
    ( k7_relat_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),'#skF_4') = '#skF_4'
    | k1_relat_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_126682,c_134602])).

tff(c_134704,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_132736,c_131334,c_134650])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:56:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 27.21/16.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.44/16.85  
% 27.44/16.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.44/16.86  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 27.44/16.86  
% 27.44/16.86  %Foreground sorts:
% 27.44/16.86  
% 27.44/16.86  
% 27.44/16.86  %Background operators:
% 27.44/16.86  
% 27.44/16.86  
% 27.44/16.86  %Foreground operators:
% 27.44/16.86  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 27.44/16.86  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 27.44/16.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 27.44/16.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 27.44/16.86  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 27.44/16.86  tff('#skF_1', type, '#skF_1': $i > $i).
% 27.44/16.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 27.44/16.86  tff('#skF_7', type, '#skF_7': $i).
% 27.44/16.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 27.44/16.86  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 27.44/16.86  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 27.44/16.86  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 27.44/16.86  tff('#skF_5', type, '#skF_5': $i).
% 27.44/16.86  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 27.44/16.86  tff('#skF_6', type, '#skF_6': $i).
% 27.44/16.86  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 27.44/16.86  tff('#skF_2', type, '#skF_2': $i).
% 27.44/16.86  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 27.44/16.86  tff('#skF_3', type, '#skF_3': $i).
% 27.44/16.86  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 27.44/16.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 27.44/16.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 27.44/16.86  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 27.44/16.86  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 27.44/16.86  tff('#skF_4', type, '#skF_4': $i).
% 27.44/16.86  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 27.44/16.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 27.44/16.86  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 27.44/16.86  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 27.44/16.86  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 27.44/16.86  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 27.44/16.86  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 27.44/16.86  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 27.44/16.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 27.44/16.86  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 27.44/16.86  
% 27.65/16.91  tff(f_260, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 27.65/16.91  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 27.65/16.91  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 27.65/16.91  tff(f_62, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 27.65/16.91  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 27.65/16.91  tff(f_108, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 27.65/16.91  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 27.65/16.91  tff(f_46, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 27.65/16.91  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 27.65/16.91  tff(f_130, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 27.65/16.91  tff(f_122, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 27.65/16.91  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 27.65/16.91  tff(f_52, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_relat_1)).
% 27.65/16.91  tff(f_88, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 27.65/16.91  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 27.65/16.91  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 27.65/16.91  tff(f_218, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 27.65/16.91  tff(f_136, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 27.65/16.91  tff(f_184, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 27.65/16.91  tff(c_92, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_260])).
% 27.65/16.91  tff(c_86, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_260])).
% 27.65/16.91  tff(c_82, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_260])).
% 27.65/16.91  tff(c_88, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_260])).
% 27.65/16.91  tff(c_90, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_260])).
% 27.65/16.91  tff(c_74, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_260])).
% 27.65/16.91  tff(c_6969, plain, (![C_806, A_807, B_808]: (v1_relat_1(C_806) | ~m1_subset_1(C_806, k1_zfmisc_1(k2_zfmisc_1(A_807, B_808))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 27.65/16.91  tff(c_6977, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_6969])).
% 27.65/16.91  tff(c_84, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_260])).
% 27.65/16.91  tff(c_6620, plain, (![C_762, A_763, B_764]: (v1_relat_1(C_762) | ~m1_subset_1(C_762, k1_zfmisc_1(k2_zfmisc_1(A_763, B_764))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 27.65/16.91  tff(c_6628, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_6620])).
% 27.65/16.91  tff(c_24, plain, (![A_19]: (k1_relat_1(A_19)!=k1_xboole_0 | k1_xboole_0=A_19 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_70])).
% 27.65/16.91  tff(c_6643, plain, (k1_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_6628, c_24])).
% 27.65/16.91  tff(c_6658, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_6643])).
% 27.65/16.91  tff(c_20, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 27.65/16.91  tff(c_104, plain, (![A_237]: (k7_relat_1(A_237, k1_relat_1(A_237))=A_237 | ~v1_relat_1(A_237))), inference(cnfTransformation, [status(thm)], [f_78])).
% 27.65/16.91  tff(c_116, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_104])).
% 27.65/16.91  tff(c_6551, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_116])).
% 27.65/16.91  tff(c_40, plain, (![A_31]: (r1_xboole_0('#skF_1'(A_31), A_31) | k1_xboole_0=A_31)), inference(cnfTransformation, [status(thm)], [f_108])).
% 27.65/16.91  tff(c_6682, plain, (![A_773, B_774]: (k7_relat_1(A_773, B_774)=k1_xboole_0 | ~r1_xboole_0(B_774, k1_relat_1(A_773)) | ~v1_relat_1(A_773))), inference(cnfTransformation, [status(thm)], [f_59])).
% 27.65/16.91  tff(c_6818, plain, (![A_793]: (k7_relat_1(A_793, '#skF_1'(k1_relat_1(A_793)))=k1_xboole_0 | ~v1_relat_1(A_793) | k1_relat_1(A_793)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_6682])).
% 27.65/16.91  tff(c_12, plain, (![A_11, B_12]: (v1_relat_1(k7_relat_1(A_11, B_12)) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 27.65/16.91  tff(c_6834, plain, (![A_793]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_793) | ~v1_relat_1(A_793) | k1_relat_1(A_793)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6818, c_12])).
% 27.65/16.91  tff(c_6850, plain, (![A_794]: (~v1_relat_1(A_794) | ~v1_relat_1(A_794) | k1_relat_1(A_794)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_6551, c_6834])).
% 27.65/16.91  tff(c_6852, plain, (~v1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_6628, c_6850])).
% 27.65/16.91  tff(c_6859, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6628, c_6852])).
% 27.65/16.91  tff(c_6861, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6658, c_6859])).
% 27.65/16.91  tff(c_6862, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_6643])).
% 27.65/16.91  tff(c_6872, plain, (~v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6862, c_6551])).
% 27.65/16.91  tff(c_6879, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6628, c_6872])).
% 27.65/16.91  tff(c_6880, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_116])).
% 27.65/16.91  tff(c_7017, plain, (![C_814, A_815, B_816]: (v4_relat_1(C_814, A_815) | ~m1_subset_1(C_814, k1_zfmisc_1(k2_zfmisc_1(A_815, B_816))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 27.65/16.91  tff(c_7025, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_74, c_7017])).
% 27.65/16.91  tff(c_7192, plain, (![B_835, A_836]: (k1_relat_1(B_835)=A_836 | ~v1_partfun1(B_835, A_836) | ~v4_relat_1(B_835, A_836) | ~v1_relat_1(B_835))), inference(cnfTransformation, [status(thm)], [f_130])).
% 27.65/16.91  tff(c_7195, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_7025, c_7192])).
% 27.65/16.91  tff(c_7201, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6977, c_7195])).
% 27.65/16.91  tff(c_7205, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_7201])).
% 27.65/16.91  tff(c_78, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_260])).
% 27.65/16.91  tff(c_76, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_260])).
% 27.65/16.91  tff(c_7738, plain, (![C_871, A_872, B_873]: (v1_partfun1(C_871, A_872) | ~v1_funct_2(C_871, A_872, B_873) | ~v1_funct_1(C_871) | ~m1_subset_1(C_871, k1_zfmisc_1(k2_zfmisc_1(A_872, B_873))) | v1_xboole_0(B_873))), inference(cnfTransformation, [status(thm)], [f_122])).
% 27.65/16.91  tff(c_7744, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_74, c_7738])).
% 27.65/16.91  tff(c_7751, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_7744])).
% 27.65/16.91  tff(c_7753, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_7205, c_7751])).
% 27.65/16.91  tff(c_7754, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_7201])).
% 27.65/16.91  tff(c_6993, plain, (k1_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_6977, c_24])).
% 27.65/16.91  tff(c_6996, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_6993])).
% 27.65/16.91  tff(c_7756, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7754, c_6996])).
% 27.65/16.91  tff(c_16, plain, (![A_16, B_18]: (k7_relat_1(A_16, B_18)=k1_xboole_0 | ~r1_xboole_0(B_18, k1_relat_1(A_16)) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 27.65/16.91  tff(c_7769, plain, (![B_18]: (k7_relat_1('#skF_6', B_18)=k1_xboole_0 | ~r1_xboole_0(B_18, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_7754, c_16])).
% 27.65/16.91  tff(c_8092, plain, (![B_891]: (k7_relat_1('#skF_6', B_891)=k1_xboole_0 | ~r1_xboole_0(B_891, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6977, c_7769])).
% 27.65/16.91  tff(c_8104, plain, (k7_relat_1('#skF_6', '#skF_1'('#skF_4'))=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_40, c_8092])).
% 27.65/16.91  tff(c_8111, plain, (k7_relat_1('#skF_6', '#skF_1'('#skF_4'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_7756, c_8104])).
% 27.65/16.91  tff(c_26, plain, (![B_21, A_20]: (r1_tarski(k1_relat_1(k7_relat_1(B_21, A_20)), A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_74])).
% 27.65/16.91  tff(c_8115, plain, (r1_tarski(k1_relat_1(k1_xboole_0), '#skF_1'('#skF_4')) | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_8111, c_26])).
% 27.65/16.91  tff(c_8122, plain, (r1_tarski(k1_xboole_0, '#skF_1'('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6977, c_20, c_8115])).
% 27.65/16.91  tff(c_8126, plain, (![C_892, B_893, A_894]: (k7_relat_1(k7_relat_1(C_892, B_893), A_894)=k7_relat_1(C_892, A_894) | ~r1_tarski(A_894, B_893) | ~v1_relat_1(C_892))), inference(cnfTransformation, [status(thm)], [f_52])).
% 27.65/16.91  tff(c_8151, plain, (![A_894]: (k7_relat_1(k1_xboole_0, A_894)=k7_relat_1('#skF_6', A_894) | ~r1_tarski(A_894, '#skF_1'('#skF_4')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_8111, c_8126])).
% 27.65/16.91  tff(c_8586, plain, (![A_923]: (k7_relat_1(k1_xboole_0, A_923)=k7_relat_1('#skF_6', A_923) | ~r1_tarski(A_923, '#skF_1'('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_6977, c_8151])).
% 27.65/16.91  tff(c_8597, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k7_relat_1('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_8122, c_8586])).
% 27.65/16.91  tff(c_8611, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6880, c_8597])).
% 27.65/16.91  tff(c_80, plain, (r1_subset_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_260])).
% 27.65/16.91  tff(c_7114, plain, (![A_824, B_825]: (r1_xboole_0(A_824, B_825) | ~r1_subset_1(A_824, B_825) | v1_xboole_0(B_825) | v1_xboole_0(A_824))), inference(cnfTransformation, [status(thm)], [f_88])).
% 27.65/16.91  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 27.65/16.91  tff(c_8930, plain, (![A_939, B_940]: (k3_xboole_0(A_939, B_940)=k1_xboole_0 | ~r1_subset_1(A_939, B_940) | v1_xboole_0(B_940) | v1_xboole_0(A_939))), inference(resolution, [status(thm)], [c_7114, c_2])).
% 27.65/16.91  tff(c_8936, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0 | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_80, c_8930])).
% 27.65/16.91  tff(c_8940, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_88, c_84, c_8936])).
% 27.65/16.91  tff(c_68, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_260])).
% 27.65/16.91  tff(c_6976, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_68, c_6969])).
% 27.65/16.91  tff(c_32, plain, (![A_23, B_24]: (r1_xboole_0(A_23, B_24) | ~r1_subset_1(A_23, B_24) | v1_xboole_0(B_24) | v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_88])).
% 27.65/16.91  tff(c_7024, plain, (v4_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_68, c_7017])).
% 27.65/16.91  tff(c_7198, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_7024, c_7192])).
% 27.65/16.91  tff(c_7204, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6976, c_7198])).
% 27.65/16.91  tff(c_7806, plain, (~v1_partfun1('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_7204])).
% 27.65/16.91  tff(c_72, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_260])).
% 27.65/16.91  tff(c_70, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_260])).
% 27.65/16.91  tff(c_8032, plain, (![C_888, A_889, B_890]: (v1_partfun1(C_888, A_889) | ~v1_funct_2(C_888, A_889, B_890) | ~v1_funct_1(C_888) | ~m1_subset_1(C_888, k1_zfmisc_1(k2_zfmisc_1(A_889, B_890))) | v1_xboole_0(B_890))), inference(cnfTransformation, [status(thm)], [f_122])).
% 27.65/16.91  tff(c_8035, plain, (v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_68, c_8032])).
% 27.65/16.91  tff(c_8041, plain, (v1_partfun1('#skF_7', '#skF_5') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_8035])).
% 27.65/16.91  tff(c_8043, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_7806, c_8041])).
% 27.65/16.91  tff(c_8044, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitRight, [status(thm)], [c_7204])).
% 27.65/16.91  tff(c_8059, plain, (![B_18]: (k7_relat_1('#skF_7', B_18)=k1_xboole_0 | ~r1_xboole_0(B_18, '#skF_5') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_8044, c_16])).
% 27.65/16.91  tff(c_8188, plain, (![B_895]: (k7_relat_1('#skF_7', B_895)=k1_xboole_0 | ~r1_xboole_0(B_895, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_6976, c_8059])).
% 27.65/16.91  tff(c_8192, plain, (![A_23]: (k7_relat_1('#skF_7', A_23)=k1_xboole_0 | ~r1_subset_1(A_23, '#skF_5') | v1_xboole_0('#skF_5') | v1_xboole_0(A_23))), inference(resolution, [status(thm)], [c_32, c_8188])).
% 27.65/16.91  tff(c_8291, plain, (![A_903]: (k7_relat_1('#skF_7', A_903)=k1_xboole_0 | ~r1_subset_1(A_903, '#skF_5') | v1_xboole_0(A_903))), inference(negUnitSimplification, [status(thm)], [c_84, c_8192])).
% 27.65/16.91  tff(c_8294, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_80, c_8291])).
% 27.65/16.91  tff(c_8297, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_88, c_8294])).
% 27.65/16.91  tff(c_8307, plain, (r1_tarski(k1_relat_1(k1_xboole_0), '#skF_4') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_8297, c_26])).
% 27.65/16.91  tff(c_8320, plain, (r1_tarski(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6976, c_20, c_8307])).
% 27.65/16.91  tff(c_14, plain, (![C_15, B_14, A_13]: (k7_relat_1(k7_relat_1(C_15, B_14), A_13)=k7_relat_1(C_15, A_13) | ~r1_tarski(A_13, B_14) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_52])).
% 27.65/16.91  tff(c_8304, plain, (![A_13]: (k7_relat_1(k1_xboole_0, A_13)=k7_relat_1('#skF_7', A_13) | ~r1_tarski(A_13, '#skF_4') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_8297, c_14])).
% 27.65/16.91  tff(c_8410, plain, (![A_910]: (k7_relat_1(k1_xboole_0, A_910)=k7_relat_1('#skF_7', A_910) | ~r1_tarski(A_910, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6976, c_8304])).
% 27.65/16.91  tff(c_8413, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k7_relat_1('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_8320, c_8410])).
% 27.65/16.91  tff(c_8430, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6880, c_8413])).
% 27.65/16.91  tff(c_7142, plain, (![A_828, B_829, C_830]: (k9_subset_1(A_828, B_829, C_830)=k3_xboole_0(B_829, C_830) | ~m1_subset_1(C_830, k1_zfmisc_1(A_828)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 27.65/16.91  tff(c_7154, plain, (![B_829]: (k9_subset_1('#skF_2', B_829, '#skF_5')=k3_xboole_0(B_829, '#skF_5'))), inference(resolution, [status(thm)], [c_82, c_7142])).
% 27.65/16.91  tff(c_8500, plain, (![C_915, F_917, D_914, A_912, E_913, B_916]: (v1_funct_1(k1_tmap_1(A_912, B_916, C_915, D_914, E_913, F_917)) | ~m1_subset_1(F_917, k1_zfmisc_1(k2_zfmisc_1(D_914, B_916))) | ~v1_funct_2(F_917, D_914, B_916) | ~v1_funct_1(F_917) | ~m1_subset_1(E_913, k1_zfmisc_1(k2_zfmisc_1(C_915, B_916))) | ~v1_funct_2(E_913, C_915, B_916) | ~v1_funct_1(E_913) | ~m1_subset_1(D_914, k1_zfmisc_1(A_912)) | v1_xboole_0(D_914) | ~m1_subset_1(C_915, k1_zfmisc_1(A_912)) | v1_xboole_0(C_915) | v1_xboole_0(B_916) | v1_xboole_0(A_912))), inference(cnfTransformation, [status(thm)], [f_218])).
% 27.65/16.91  tff(c_8502, plain, (![A_912, C_915, E_913]: (v1_funct_1(k1_tmap_1(A_912, '#skF_3', C_915, '#skF_5', E_913, '#skF_7')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_913, k1_zfmisc_1(k2_zfmisc_1(C_915, '#skF_3'))) | ~v1_funct_2(E_913, C_915, '#skF_3') | ~v1_funct_1(E_913) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_912)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_915, k1_zfmisc_1(A_912)) | v1_xboole_0(C_915) | v1_xboole_0('#skF_3') | v1_xboole_0(A_912))), inference(resolution, [status(thm)], [c_68, c_8500])).
% 27.65/16.91  tff(c_8507, plain, (![A_912, C_915, E_913]: (v1_funct_1(k1_tmap_1(A_912, '#skF_3', C_915, '#skF_5', E_913, '#skF_7')) | ~m1_subset_1(E_913, k1_zfmisc_1(k2_zfmisc_1(C_915, '#skF_3'))) | ~v1_funct_2(E_913, C_915, '#skF_3') | ~v1_funct_1(E_913) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_912)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_915, k1_zfmisc_1(A_912)) | v1_xboole_0(C_915) | v1_xboole_0('#skF_3') | v1_xboole_0(A_912))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_8502])).
% 27.65/16.91  tff(c_9245, plain, (![A_960, C_961, E_962]: (v1_funct_1(k1_tmap_1(A_960, '#skF_3', C_961, '#skF_5', E_962, '#skF_7')) | ~m1_subset_1(E_962, k1_zfmisc_1(k2_zfmisc_1(C_961, '#skF_3'))) | ~v1_funct_2(E_962, C_961, '#skF_3') | ~v1_funct_1(E_962) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_960)) | ~m1_subset_1(C_961, k1_zfmisc_1(A_960)) | v1_xboole_0(C_961) | v1_xboole_0(A_960))), inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_8507])).
% 27.65/16.91  tff(c_9252, plain, (![A_960]: (v1_funct_1(k1_tmap_1(A_960, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_960)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_960)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_960))), inference(resolution, [status(thm)], [c_74, c_9245])).
% 27.65/16.91  tff(c_9262, plain, (![A_960]: (v1_funct_1(k1_tmap_1(A_960, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_960)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_960)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_960))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_9252])).
% 27.65/16.91  tff(c_9951, plain, (![A_987]: (v1_funct_1(k1_tmap_1(A_987, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_987)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_987)) | v1_xboole_0(A_987))), inference(negUnitSimplification, [status(thm)], [c_88, c_9262])).
% 27.65/16.91  tff(c_9954, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_82, c_9951])).
% 27.65/16.91  tff(c_9957, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_9954])).
% 27.65/16.91  tff(c_9958, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_92, c_9957])).
% 27.65/16.91  tff(c_8279, plain, (![A_898, B_899, C_900, D_901]: (k2_partfun1(A_898, B_899, C_900, D_901)=k7_relat_1(C_900, D_901) | ~m1_subset_1(C_900, k1_zfmisc_1(k2_zfmisc_1(A_898, B_899))) | ~v1_funct_1(C_900))), inference(cnfTransformation, [status(thm)], [f_136])).
% 27.65/16.91  tff(c_8283, plain, (![D_901]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_901)=k7_relat_1('#skF_6', D_901) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_74, c_8279])).
% 27.65/16.91  tff(c_8289, plain, (![D_901]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_901)=k7_relat_1('#skF_6', D_901))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_8283])).
% 27.65/16.91  tff(c_8281, plain, (![D_901]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_901)=k7_relat_1('#skF_7', D_901) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_68, c_8279])).
% 27.65/16.91  tff(c_8286, plain, (![D_901]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_901)=k7_relat_1('#skF_7', D_901))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_8281])).
% 27.65/16.91  tff(c_62, plain, (![A_170, D_173, E_174, B_171, C_172, F_175]: (v1_funct_2(k1_tmap_1(A_170, B_171, C_172, D_173, E_174, F_175), k4_subset_1(A_170, C_172, D_173), B_171) | ~m1_subset_1(F_175, k1_zfmisc_1(k2_zfmisc_1(D_173, B_171))) | ~v1_funct_2(F_175, D_173, B_171) | ~v1_funct_1(F_175) | ~m1_subset_1(E_174, k1_zfmisc_1(k2_zfmisc_1(C_172, B_171))) | ~v1_funct_2(E_174, C_172, B_171) | ~v1_funct_1(E_174) | ~m1_subset_1(D_173, k1_zfmisc_1(A_170)) | v1_xboole_0(D_173) | ~m1_subset_1(C_172, k1_zfmisc_1(A_170)) | v1_xboole_0(C_172) | v1_xboole_0(B_171) | v1_xboole_0(A_170))), inference(cnfTransformation, [status(thm)], [f_218])).
% 27.65/16.91  tff(c_60, plain, (![A_170, D_173, E_174, B_171, C_172, F_175]: (m1_subset_1(k1_tmap_1(A_170, B_171, C_172, D_173, E_174, F_175), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_170, C_172, D_173), B_171))) | ~m1_subset_1(F_175, k1_zfmisc_1(k2_zfmisc_1(D_173, B_171))) | ~v1_funct_2(F_175, D_173, B_171) | ~v1_funct_1(F_175) | ~m1_subset_1(E_174, k1_zfmisc_1(k2_zfmisc_1(C_172, B_171))) | ~v1_funct_2(E_174, C_172, B_171) | ~v1_funct_1(E_174) | ~m1_subset_1(D_173, k1_zfmisc_1(A_170)) | v1_xboole_0(D_173) | ~m1_subset_1(C_172, k1_zfmisc_1(A_170)) | v1_xboole_0(C_172) | v1_xboole_0(B_171) | v1_xboole_0(A_170))), inference(cnfTransformation, [status(thm)], [f_218])).
% 27.65/16.91  tff(c_9508, plain, (![C_971, E_972, A_969, F_967, B_970, D_968]: (k2_partfun1(k4_subset_1(A_969, C_971, D_968), B_970, k1_tmap_1(A_969, B_970, C_971, D_968, E_972, F_967), D_968)=F_967 | ~m1_subset_1(k1_tmap_1(A_969, B_970, C_971, D_968, E_972, F_967), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_969, C_971, D_968), B_970))) | ~v1_funct_2(k1_tmap_1(A_969, B_970, C_971, D_968, E_972, F_967), k4_subset_1(A_969, C_971, D_968), B_970) | ~v1_funct_1(k1_tmap_1(A_969, B_970, C_971, D_968, E_972, F_967)) | k2_partfun1(D_968, B_970, F_967, k9_subset_1(A_969, C_971, D_968))!=k2_partfun1(C_971, B_970, E_972, k9_subset_1(A_969, C_971, D_968)) | ~m1_subset_1(F_967, k1_zfmisc_1(k2_zfmisc_1(D_968, B_970))) | ~v1_funct_2(F_967, D_968, B_970) | ~v1_funct_1(F_967) | ~m1_subset_1(E_972, k1_zfmisc_1(k2_zfmisc_1(C_971, B_970))) | ~v1_funct_2(E_972, C_971, B_970) | ~v1_funct_1(E_972) | ~m1_subset_1(D_968, k1_zfmisc_1(A_969)) | v1_xboole_0(D_968) | ~m1_subset_1(C_971, k1_zfmisc_1(A_969)) | v1_xboole_0(C_971) | v1_xboole_0(B_970) | v1_xboole_0(A_969))), inference(cnfTransformation, [status(thm)], [f_184])).
% 27.65/16.91  tff(c_15562, plain, (![A_1140, D_1142, F_1145, C_1143, E_1141, B_1144]: (k2_partfun1(k4_subset_1(A_1140, C_1143, D_1142), B_1144, k1_tmap_1(A_1140, B_1144, C_1143, D_1142, E_1141, F_1145), D_1142)=F_1145 | ~v1_funct_2(k1_tmap_1(A_1140, B_1144, C_1143, D_1142, E_1141, F_1145), k4_subset_1(A_1140, C_1143, D_1142), B_1144) | ~v1_funct_1(k1_tmap_1(A_1140, B_1144, C_1143, D_1142, E_1141, F_1145)) | k2_partfun1(D_1142, B_1144, F_1145, k9_subset_1(A_1140, C_1143, D_1142))!=k2_partfun1(C_1143, B_1144, E_1141, k9_subset_1(A_1140, C_1143, D_1142)) | ~m1_subset_1(F_1145, k1_zfmisc_1(k2_zfmisc_1(D_1142, B_1144))) | ~v1_funct_2(F_1145, D_1142, B_1144) | ~v1_funct_1(F_1145) | ~m1_subset_1(E_1141, k1_zfmisc_1(k2_zfmisc_1(C_1143, B_1144))) | ~v1_funct_2(E_1141, C_1143, B_1144) | ~v1_funct_1(E_1141) | ~m1_subset_1(D_1142, k1_zfmisc_1(A_1140)) | v1_xboole_0(D_1142) | ~m1_subset_1(C_1143, k1_zfmisc_1(A_1140)) | v1_xboole_0(C_1143) | v1_xboole_0(B_1144) | v1_xboole_0(A_1140))), inference(resolution, [status(thm)], [c_60, c_9508])).
% 27.65/16.91  tff(c_34392, plain, (![E_1347, F_1351, B_1350, C_1349, A_1346, D_1348]: (k2_partfun1(k4_subset_1(A_1346, C_1349, D_1348), B_1350, k1_tmap_1(A_1346, B_1350, C_1349, D_1348, E_1347, F_1351), D_1348)=F_1351 | ~v1_funct_1(k1_tmap_1(A_1346, B_1350, C_1349, D_1348, E_1347, F_1351)) | k2_partfun1(D_1348, B_1350, F_1351, k9_subset_1(A_1346, C_1349, D_1348))!=k2_partfun1(C_1349, B_1350, E_1347, k9_subset_1(A_1346, C_1349, D_1348)) | ~m1_subset_1(F_1351, k1_zfmisc_1(k2_zfmisc_1(D_1348, B_1350))) | ~v1_funct_2(F_1351, D_1348, B_1350) | ~v1_funct_1(F_1351) | ~m1_subset_1(E_1347, k1_zfmisc_1(k2_zfmisc_1(C_1349, B_1350))) | ~v1_funct_2(E_1347, C_1349, B_1350) | ~v1_funct_1(E_1347) | ~m1_subset_1(D_1348, k1_zfmisc_1(A_1346)) | v1_xboole_0(D_1348) | ~m1_subset_1(C_1349, k1_zfmisc_1(A_1346)) | v1_xboole_0(C_1349) | v1_xboole_0(B_1350) | v1_xboole_0(A_1346))), inference(resolution, [status(thm)], [c_62, c_15562])).
% 27.65/16.91  tff(c_34396, plain, (![A_1346, C_1349, E_1347]: (k2_partfun1(k4_subset_1(A_1346, C_1349, '#skF_5'), '#skF_3', k1_tmap_1(A_1346, '#skF_3', C_1349, '#skF_5', E_1347, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1346, '#skF_3', C_1349, '#skF_5', E_1347, '#skF_7')) | k2_partfun1(C_1349, '#skF_3', E_1347, k9_subset_1(A_1346, C_1349, '#skF_5'))!=k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1(A_1346, C_1349, '#skF_5')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_1347, k1_zfmisc_1(k2_zfmisc_1(C_1349, '#skF_3'))) | ~v1_funct_2(E_1347, C_1349, '#skF_3') | ~v1_funct_1(E_1347) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1346)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1349, k1_zfmisc_1(A_1346)) | v1_xboole_0(C_1349) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1346))), inference(resolution, [status(thm)], [c_68, c_34392])).
% 27.65/16.91  tff(c_34402, plain, (![A_1346, C_1349, E_1347]: (k2_partfun1(k4_subset_1(A_1346, C_1349, '#skF_5'), '#skF_3', k1_tmap_1(A_1346, '#skF_3', C_1349, '#skF_5', E_1347, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1346, '#skF_3', C_1349, '#skF_5', E_1347, '#skF_7')) | k2_partfun1(C_1349, '#skF_3', E_1347, k9_subset_1(A_1346, C_1349, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_1346, C_1349, '#skF_5')) | ~m1_subset_1(E_1347, k1_zfmisc_1(k2_zfmisc_1(C_1349, '#skF_3'))) | ~v1_funct_2(E_1347, C_1349, '#skF_3') | ~v1_funct_1(E_1347) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1346)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1349, k1_zfmisc_1(A_1346)) | v1_xboole_0(C_1349) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1346))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_8286, c_34396])).
% 27.65/16.91  tff(c_44400, plain, (![A_1467, C_1468, E_1469]: (k2_partfun1(k4_subset_1(A_1467, C_1468, '#skF_5'), '#skF_3', k1_tmap_1(A_1467, '#skF_3', C_1468, '#skF_5', E_1469, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1467, '#skF_3', C_1468, '#skF_5', E_1469, '#skF_7')) | k2_partfun1(C_1468, '#skF_3', E_1469, k9_subset_1(A_1467, C_1468, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_1467, C_1468, '#skF_5')) | ~m1_subset_1(E_1469, k1_zfmisc_1(k2_zfmisc_1(C_1468, '#skF_3'))) | ~v1_funct_2(E_1469, C_1468, '#skF_3') | ~v1_funct_1(E_1469) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1467)) | ~m1_subset_1(C_1468, k1_zfmisc_1(A_1467)) | v1_xboole_0(C_1468) | v1_xboole_0(A_1467))), inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_34402])).
% 27.65/16.91  tff(c_44407, plain, (![A_1467]: (k2_partfun1(k4_subset_1(A_1467, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_1467, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1467, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1(A_1467, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_1467, '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1467)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1467)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1467))), inference(resolution, [status(thm)], [c_74, c_44400])).
% 27.65/16.91  tff(c_44417, plain, (![A_1467]: (k2_partfun1(k4_subset_1(A_1467, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_1467, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1467, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_1467, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_1467, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1467)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1467)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1467))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_8289, c_44407])).
% 27.65/16.91  tff(c_46029, plain, (![A_1478]: (k2_partfun1(k4_subset_1(A_1478, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_1478, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1478, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_1478, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_1478, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1478)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1478)) | v1_xboole_0(A_1478))), inference(negUnitSimplification, [status(thm)], [c_88, c_44417])).
% 27.65/16.91  tff(c_654, plain, (![C_313, A_314, B_315]: (v1_relat_1(C_313) | ~m1_subset_1(C_313, k1_zfmisc_1(k2_zfmisc_1(A_314, B_315))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 27.65/16.91  tff(c_662, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_654])).
% 27.65/16.91  tff(c_120, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_116])).
% 27.65/16.91  tff(c_164, plain, (![C_249, A_250, B_251]: (v1_relat_1(C_249) | ~m1_subset_1(C_249, k1_zfmisc_1(k2_zfmisc_1(A_250, B_251))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 27.65/16.91  tff(c_171, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_68, c_164])).
% 27.65/16.91  tff(c_214, plain, (![C_254, A_255, B_256]: (v4_relat_1(C_254, A_255) | ~m1_subset_1(C_254, k1_zfmisc_1(k2_zfmisc_1(A_255, B_256))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 27.65/16.91  tff(c_221, plain, (v4_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_68, c_214])).
% 27.65/16.91  tff(c_333, plain, (![B_275, A_276]: (k1_relat_1(B_275)=A_276 | ~v1_partfun1(B_275, A_276) | ~v4_relat_1(B_275, A_276) | ~v1_relat_1(B_275))), inference(cnfTransformation, [status(thm)], [f_130])).
% 27.65/16.91  tff(c_339, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_221, c_333])).
% 27.65/16.91  tff(c_345, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_171, c_339])).
% 27.65/16.91  tff(c_380, plain, (~v1_partfun1('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_345])).
% 27.65/16.91  tff(c_445, plain, (![C_293, A_294, B_295]: (v1_partfun1(C_293, A_294) | ~v1_funct_2(C_293, A_294, B_295) | ~v1_funct_1(C_293) | ~m1_subset_1(C_293, k1_zfmisc_1(k2_zfmisc_1(A_294, B_295))) | v1_xboole_0(B_295))), inference(cnfTransformation, [status(thm)], [f_122])).
% 27.65/16.91  tff(c_448, plain, (v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_68, c_445])).
% 27.65/16.91  tff(c_454, plain, (v1_partfun1('#skF_7', '#skF_5') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_448])).
% 27.65/16.91  tff(c_456, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_380, c_454])).
% 27.65/16.91  tff(c_457, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitRight, [status(thm)], [c_345])).
% 27.65/16.91  tff(c_463, plain, (![B_18]: (k7_relat_1('#skF_7', B_18)=k1_xboole_0 | ~r1_xboole_0(B_18, '#skF_5') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_457, c_16])).
% 27.65/16.91  tff(c_522, plain, (![B_300]: (k7_relat_1('#skF_7', B_300)=k1_xboole_0 | ~r1_xboole_0(B_300, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_463])).
% 27.65/16.91  tff(c_526, plain, (![A_23]: (k7_relat_1('#skF_7', A_23)=k1_xboole_0 | ~r1_subset_1(A_23, '#skF_5') | v1_xboole_0('#skF_5') | v1_xboole_0(A_23))), inference(resolution, [status(thm)], [c_32, c_522])).
% 27.65/16.91  tff(c_542, plain, (![A_301]: (k7_relat_1('#skF_7', A_301)=k1_xboole_0 | ~r1_subset_1(A_301, '#skF_5') | v1_xboole_0(A_301))), inference(negUnitSimplification, [status(thm)], [c_84, c_526])).
% 27.65/16.91  tff(c_545, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_80, c_542])).
% 27.65/16.91  tff(c_548, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_88, c_545])).
% 27.65/16.91  tff(c_558, plain, (v1_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_548, c_12])).
% 27.65/16.91  tff(c_566, plain, (v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_171, c_558])).
% 27.65/16.91  tff(c_568, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120, c_566])).
% 27.65/16.91  tff(c_569, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_116])).
% 27.65/16.91  tff(c_692, plain, (![C_318, A_319, B_320]: (v4_relat_1(C_318, A_319) | ~m1_subset_1(C_318, k1_zfmisc_1(k2_zfmisc_1(A_319, B_320))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 27.65/16.91  tff(c_700, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_74, c_692])).
% 27.65/16.91  tff(c_839, plain, (![B_338, A_339]: (k1_relat_1(B_338)=A_339 | ~v1_partfun1(B_338, A_339) | ~v4_relat_1(B_338, A_339) | ~v1_relat_1(B_338))), inference(cnfTransformation, [status(thm)], [f_130])).
% 27.65/16.91  tff(c_842, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_700, c_839])).
% 27.65/16.91  tff(c_848, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_662, c_842])).
% 27.65/16.91  tff(c_852, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_848])).
% 27.65/16.91  tff(c_1555, plain, (![C_390, A_391, B_392]: (v1_partfun1(C_390, A_391) | ~v1_funct_2(C_390, A_391, B_392) | ~v1_funct_1(C_390) | ~m1_subset_1(C_390, k1_zfmisc_1(k2_zfmisc_1(A_391, B_392))) | v1_xboole_0(B_392))), inference(cnfTransformation, [status(thm)], [f_122])).
% 27.65/16.91  tff(c_1561, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_74, c_1555])).
% 27.65/16.91  tff(c_1568, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_1561])).
% 27.65/16.91  tff(c_1570, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_852, c_1568])).
% 27.65/16.91  tff(c_1571, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_848])).
% 27.65/16.91  tff(c_677, plain, (k1_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_662, c_24])).
% 27.65/16.91  tff(c_680, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_677])).
% 27.65/16.91  tff(c_1573, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1571, c_680])).
% 27.65/16.91  tff(c_1580, plain, (![B_18]: (k7_relat_1('#skF_6', B_18)=k1_xboole_0 | ~r1_xboole_0(B_18, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1571, c_16])).
% 27.65/16.91  tff(c_2018, plain, (![B_419]: (k7_relat_1('#skF_6', B_419)=k1_xboole_0 | ~r1_xboole_0(B_419, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_662, c_1580])).
% 27.65/16.91  tff(c_2030, plain, (k7_relat_1('#skF_6', '#skF_1'('#skF_4'))=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_40, c_2018])).
% 27.65/16.91  tff(c_2037, plain, (k7_relat_1('#skF_6', '#skF_1'('#skF_4'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_1573, c_2030])).
% 27.65/16.91  tff(c_2053, plain, (r1_tarski(k1_relat_1(k1_xboole_0), '#skF_1'('#skF_4')) | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2037, c_26])).
% 27.65/16.91  tff(c_2062, plain, (r1_tarski(k1_xboole_0, '#skF_1'('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_662, c_20, c_2053])).
% 27.65/16.91  tff(c_2050, plain, (![A_13]: (k7_relat_1(k1_xboole_0, A_13)=k7_relat_1('#skF_6', A_13) | ~r1_tarski(A_13, '#skF_1'('#skF_4')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2037, c_14])).
% 27.65/16.91  tff(c_2404, plain, (![A_448]: (k7_relat_1(k1_xboole_0, A_448)=k7_relat_1('#skF_6', A_448) | ~r1_tarski(A_448, '#skF_1'('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_662, c_2050])).
% 27.65/16.91  tff(c_2415, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k7_relat_1('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_2062, c_2404])).
% 27.65/16.91  tff(c_2429, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_569, c_2415])).
% 27.65/16.91  tff(c_721, plain, (![A_325, B_326]: (r1_xboole_0(A_325, B_326) | ~r1_subset_1(A_325, B_326) | v1_xboole_0(B_326) | v1_xboole_0(A_325))), inference(cnfTransformation, [status(thm)], [f_88])).
% 27.65/16.91  tff(c_2645, plain, (![A_468, B_469]: (k3_xboole_0(A_468, B_469)=k1_xboole_0 | ~r1_subset_1(A_468, B_469) | v1_xboole_0(B_469) | v1_xboole_0(A_468))), inference(resolution, [status(thm)], [c_721, c_2])).
% 27.65/16.91  tff(c_2651, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0 | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_80, c_2645])).
% 27.65/16.91  tff(c_2655, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_88, c_84, c_2651])).
% 27.65/16.91  tff(c_661, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_68, c_654])).
% 27.65/16.91  tff(c_699, plain, (v4_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_68, c_692])).
% 27.65/16.91  tff(c_845, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_699, c_839])).
% 27.65/16.91  tff(c_851, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_661, c_845])).
% 27.65/16.91  tff(c_1628, plain, (~v1_partfun1('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_851])).
% 27.65/16.91  tff(c_1852, plain, (![C_411, A_412, B_413]: (v1_partfun1(C_411, A_412) | ~v1_funct_2(C_411, A_412, B_413) | ~v1_funct_1(C_411) | ~m1_subset_1(C_411, k1_zfmisc_1(k2_zfmisc_1(A_412, B_413))) | v1_xboole_0(B_413))), inference(cnfTransformation, [status(thm)], [f_122])).
% 27.65/16.91  tff(c_1855, plain, (v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_68, c_1852])).
% 27.65/16.91  tff(c_1861, plain, (v1_partfun1('#skF_7', '#skF_5') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_1855])).
% 27.65/16.91  tff(c_1863, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_1628, c_1861])).
% 27.65/16.91  tff(c_1864, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitRight, [status(thm)], [c_851])).
% 27.65/16.91  tff(c_1873, plain, (![B_18]: (k7_relat_1('#skF_7', B_18)=k1_xboole_0 | ~r1_xboole_0(B_18, '#skF_5') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1864, c_16])).
% 27.65/16.91  tff(c_1922, plain, (![B_415]: (k7_relat_1('#skF_7', B_415)=k1_xboole_0 | ~r1_xboole_0(B_415, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_661, c_1873])).
% 27.65/16.91  tff(c_1926, plain, (![A_23]: (k7_relat_1('#skF_7', A_23)=k1_xboole_0 | ~r1_subset_1(A_23, '#skF_5') | v1_xboole_0('#skF_5') | v1_xboole_0(A_23))), inference(resolution, [status(thm)], [c_32, c_1922])).
% 27.65/16.91  tff(c_2224, plain, (![A_436]: (k7_relat_1('#skF_7', A_436)=k1_xboole_0 | ~r1_subset_1(A_436, '#skF_5') | v1_xboole_0(A_436))), inference(negUnitSimplification, [status(thm)], [c_84, c_1926])).
% 27.65/16.91  tff(c_2227, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_80, c_2224])).
% 27.65/16.91  tff(c_2230, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_88, c_2227])).
% 27.65/16.91  tff(c_2240, plain, (r1_tarski(k1_relat_1(k1_xboole_0), '#skF_4') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2230, c_26])).
% 27.65/16.91  tff(c_2253, plain, (r1_tarski(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_661, c_20, c_2240])).
% 27.65/16.91  tff(c_2237, plain, (![A_13]: (k7_relat_1(k1_xboole_0, A_13)=k7_relat_1('#skF_7', A_13) | ~r1_tarski(A_13, '#skF_4') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2230, c_14])).
% 27.65/16.91  tff(c_2271, plain, (![A_443]: (k7_relat_1(k1_xboole_0, A_443)=k7_relat_1('#skF_7', A_443) | ~r1_tarski(A_443, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_661, c_2237])).
% 27.65/16.91  tff(c_2274, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k7_relat_1('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_2253, c_2271])).
% 27.65/16.91  tff(c_2295, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_569, c_2274])).
% 27.65/16.91  tff(c_2117, plain, (![A_422, B_423, C_424, D_425]: (k2_partfun1(A_422, B_423, C_424, D_425)=k7_relat_1(C_424, D_425) | ~m1_subset_1(C_424, k1_zfmisc_1(k2_zfmisc_1(A_422, B_423))) | ~v1_funct_1(C_424))), inference(cnfTransformation, [status(thm)], [f_136])).
% 27.65/16.91  tff(c_2121, plain, (![D_425]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_425)=k7_relat_1('#skF_6', D_425) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_74, c_2117])).
% 27.65/16.91  tff(c_2127, plain, (![D_425]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_425)=k7_relat_1('#skF_6', D_425))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2121])).
% 27.65/16.91  tff(c_2119, plain, (![D_425]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_425)=k7_relat_1('#skF_7', D_425) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_68, c_2117])).
% 27.65/16.91  tff(c_2124, plain, (![D_425]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_425)=k7_relat_1('#skF_7', D_425))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2119])).
% 27.65/16.91  tff(c_826, plain, (![A_335, B_336, C_337]: (k9_subset_1(A_335, B_336, C_337)=k3_xboole_0(B_336, C_337) | ~m1_subset_1(C_337, k1_zfmisc_1(A_335)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 27.65/16.91  tff(c_838, plain, (![B_336]: (k9_subset_1('#skF_2', B_336, '#skF_5')=k3_xboole_0(B_336, '#skF_5'))), inference(resolution, [status(thm)], [c_82, c_826])).
% 27.65/16.91  tff(c_66, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')!='#skF_7' | k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')!='#skF_6' | k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_260])).
% 27.65/16.91  tff(c_119, plain, (k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_66])).
% 27.65/16.91  tff(c_1896, plain, (k2_partfun1('#skF_5', '#skF_3', '#skF_7', k3_xboole_0('#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_838, c_838, c_119])).
% 27.65/16.91  tff(c_3507, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2429, c_2655, c_2295, c_2655, c_2127, c_2124, c_1896])).
% 27.65/16.91  tff(c_3508, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_677])).
% 27.65/16.91  tff(c_3509, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_677])).
% 27.65/16.91  tff(c_3570, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3508, c_3509])).
% 27.65/16.91  tff(c_3660, plain, (![C_523, A_524, B_525]: (v4_relat_1(C_523, A_524) | ~m1_subset_1(C_523, k1_zfmisc_1(k2_zfmisc_1(A_524, B_525))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 27.65/16.91  tff(c_3668, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_74, c_3660])).
% 27.65/16.91  tff(c_4733, plain, (![B_607, A_608]: (k1_relat_1(B_607)=A_608 | ~v1_partfun1(B_607, A_608) | ~v4_relat_1(B_607, A_608) | ~v1_relat_1(B_607))), inference(cnfTransformation, [status(thm)], [f_130])).
% 27.65/16.91  tff(c_4739, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_3668, c_4733])).
% 27.65/16.91  tff(c_4748, plain, ('#skF_6'='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_662, c_3570, c_4739])).
% 27.65/16.91  tff(c_4752, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_4748])).
% 27.65/16.91  tff(c_5177, plain, (![C_642, A_643, B_644]: (v1_partfun1(C_642, A_643) | ~v1_funct_2(C_642, A_643, B_644) | ~v1_funct_1(C_642) | ~m1_subset_1(C_642, k1_zfmisc_1(k2_zfmisc_1(A_643, B_644))) | v1_xboole_0(B_644))), inference(cnfTransformation, [status(thm)], [f_122])).
% 27.65/16.91  tff(c_5183, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_74, c_5177])).
% 27.65/16.91  tff(c_5190, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_5183])).
% 27.65/16.91  tff(c_5192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_4752, c_5190])).
% 27.65/16.91  tff(c_5193, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_4748])).
% 27.65/16.91  tff(c_3556, plain, (k7_relat_1('#skF_6', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3508, c_3508, c_3508, c_569])).
% 27.65/16.91  tff(c_5212, plain, (k7_relat_1('#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5193, c_5193, c_5193, c_3556])).
% 27.65/16.91  tff(c_3553, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)='#skF_6' | ~r1_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_3508, c_2])).
% 27.65/16.91  tff(c_5528, plain, (![A_668, B_669]: (k3_xboole_0(A_668, B_669)='#skF_4' | ~r1_xboole_0(A_668, B_669))), inference(demodulation, [status(thm), theory('equality')], [c_5193, c_3553])).
% 27.65/16.91  tff(c_6039, plain, (![A_724, B_725]: (k3_xboole_0(A_724, B_725)='#skF_4' | ~r1_subset_1(A_724, B_725) | v1_xboole_0(B_725) | v1_xboole_0(A_724))), inference(resolution, [status(thm)], [c_32, c_5528])).
% 27.65/16.91  tff(c_6045, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4' | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_80, c_6039])).
% 27.65/16.91  tff(c_6049, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_88, c_84, c_6045])).
% 27.65/16.91  tff(c_3667, plain, (v4_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_68, c_3660])).
% 27.65/16.91  tff(c_4742, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_3667, c_4733])).
% 27.65/16.91  tff(c_4751, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_661, c_4742])).
% 27.65/16.91  tff(c_5329, plain, (~v1_partfun1('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_4751])).
% 27.65/16.91  tff(c_5398, plain, (![C_659, A_660, B_661]: (v1_partfun1(C_659, A_660) | ~v1_funct_2(C_659, A_660, B_661) | ~v1_funct_1(C_659) | ~m1_subset_1(C_659, k1_zfmisc_1(k2_zfmisc_1(A_660, B_661))) | v1_xboole_0(B_661))), inference(cnfTransformation, [status(thm)], [f_122])).
% 27.65/16.91  tff(c_5404, plain, (v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_68, c_5398])).
% 27.65/16.91  tff(c_5411, plain, (v1_partfun1('#skF_7', '#skF_5') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_5404])).
% 27.65/16.91  tff(c_5413, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_5329, c_5411])).
% 27.65/16.91  tff(c_5414, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitRight, [status(thm)], [c_4751])).
% 27.65/16.91  tff(c_3698, plain, (![A_16, B_18]: (k7_relat_1(A_16, B_18)='#skF_6' | ~r1_xboole_0(B_18, k1_relat_1(A_16)) | ~v1_relat_1(A_16))), inference(demodulation, [status(thm), theory('equality')], [c_3508, c_16])).
% 27.65/16.91  tff(c_5682, plain, (![A_687, B_688]: (k7_relat_1(A_687, B_688)='#skF_4' | ~r1_xboole_0(B_688, k1_relat_1(A_687)) | ~v1_relat_1(A_687))), inference(demodulation, [status(thm), theory('equality')], [c_5193, c_3698])).
% 27.65/16.91  tff(c_5693, plain, (![B_688]: (k7_relat_1('#skF_7', B_688)='#skF_4' | ~r1_xboole_0(B_688, '#skF_5') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_5414, c_5682])).
% 27.65/16.91  tff(c_5708, plain, (![B_689]: (k7_relat_1('#skF_7', B_689)='#skF_4' | ~r1_xboole_0(B_689, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_661, c_5693])).
% 27.65/16.91  tff(c_5720, plain, (![A_23]: (k7_relat_1('#skF_7', A_23)='#skF_4' | ~r1_subset_1(A_23, '#skF_5') | v1_xboole_0('#skF_5') | v1_xboole_0(A_23))), inference(resolution, [status(thm)], [c_32, c_5708])).
% 27.65/16.91  tff(c_5798, plain, (![A_697]: (k7_relat_1('#skF_7', A_697)='#skF_4' | ~r1_subset_1(A_697, '#skF_5') | v1_xboole_0(A_697))), inference(negUnitSimplification, [status(thm)], [c_84, c_5720])).
% 27.65/16.91  tff(c_5801, plain, (k7_relat_1('#skF_7', '#skF_4')='#skF_4' | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_80, c_5798])).
% 27.65/16.91  tff(c_5804, plain, (k7_relat_1('#skF_7', '#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_88, c_5801])).
% 27.65/16.91  tff(c_5221, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5193, c_78])).
% 27.65/16.91  tff(c_5219, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_5193, c_74])).
% 27.65/16.91  tff(c_52, plain, (![A_39, B_40, C_41, D_42]: (k2_partfun1(A_39, B_40, C_41, D_42)=k7_relat_1(C_41, D_42) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))) | ~v1_funct_1(C_41))), inference(cnfTransformation, [status(thm)], [f_136])).
% 27.65/16.91  tff(c_5442, plain, (![D_42]: (k2_partfun1('#skF_4', '#skF_3', '#skF_4', D_42)=k7_relat_1('#skF_4', D_42) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_5219, c_52])).
% 27.65/16.91  tff(c_5459, plain, (![D_42]: (k2_partfun1('#skF_4', '#skF_3', '#skF_4', D_42)=k7_relat_1('#skF_4', D_42))), inference(demodulation, [status(thm), theory('equality')], [c_5221, c_5442])).
% 27.65/16.91  tff(c_5322, plain, (![A_648, B_649, C_650, D_651]: (k2_partfun1(A_648, B_649, C_650, D_651)=k7_relat_1(C_650, D_651) | ~m1_subset_1(C_650, k1_zfmisc_1(k2_zfmisc_1(A_648, B_649))) | ~v1_funct_1(C_650))), inference(cnfTransformation, [status(thm)], [f_136])).
% 27.65/16.91  tff(c_5324, plain, (![D_651]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_651)=k7_relat_1('#skF_7', D_651) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_68, c_5322])).
% 27.65/16.91  tff(c_5327, plain, (![D_651]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_651)=k7_relat_1('#skF_7', D_651))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_5324])).
% 27.65/16.91  tff(c_4683, plain, (![A_600, B_601, C_602]: (k9_subset_1(A_600, B_601, C_602)=k3_xboole_0(B_601, C_602) | ~m1_subset_1(C_602, k1_zfmisc_1(A_600)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 27.65/16.91  tff(c_4695, plain, (![B_601]: (k9_subset_1('#skF_2', B_601, '#skF_5')=k3_xboole_0(B_601, '#skF_5'))), inference(resolution, [status(thm)], [c_82, c_4683])).
% 27.65/16.91  tff(c_4705, plain, (k2_partfun1('#skF_5', '#skF_3', '#skF_7', k3_xboole_0('#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4695, c_4695, c_119])).
% 27.65/16.91  tff(c_6548, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5212, c_6049, c_5804, c_6049, c_5459, c_5327, c_5193, c_4705])).
% 27.65/16.91  tff(c_6549, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_66])).
% 27.65/16.91  tff(c_6995, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')!='#skF_7'), inference(splitLeft, [status(thm)], [c_6549])).
% 27.65/16.91  tff(c_46040, plain, (~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_46029, c_6995])).
% 27.65/16.91  tff(c_46054, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_8611, c_8940, c_8430, c_8940, c_7154, c_7154, c_9958, c_46040])).
% 27.65/16.91  tff(c_46056, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_46054])).
% 27.65/16.91  tff(c_46057, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_6993])).
% 27.65/16.91  tff(c_46058, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_6993])).
% 27.65/16.91  tff(c_46076, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_46057, c_46058])).
% 27.65/16.91  tff(c_46177, plain, (![C_1493, A_1494, B_1495]: (v4_relat_1(C_1493, A_1494) | ~m1_subset_1(C_1493, k1_zfmisc_1(k2_zfmisc_1(A_1494, B_1495))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 27.65/16.91  tff(c_46185, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_74, c_46177])).
% 27.65/16.91  tff(c_47296, plain, (![B_1581, A_1582]: (k1_relat_1(B_1581)=A_1582 | ~v1_partfun1(B_1581, A_1582) | ~v4_relat_1(B_1581, A_1582) | ~v1_relat_1(B_1581))), inference(cnfTransformation, [status(thm)], [f_130])).
% 27.65/16.91  tff(c_47302, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_46185, c_47296])).
% 27.65/16.91  tff(c_47311, plain, ('#skF_6'='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6977, c_46076, c_47302])).
% 27.65/16.91  tff(c_47315, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_47311])).
% 27.65/16.91  tff(c_47797, plain, (![C_1617, A_1618, B_1619]: (v1_partfun1(C_1617, A_1618) | ~v1_funct_2(C_1617, A_1618, B_1619) | ~v1_funct_1(C_1617) | ~m1_subset_1(C_1617, k1_zfmisc_1(k2_zfmisc_1(A_1618, B_1619))) | v1_xboole_0(B_1619))), inference(cnfTransformation, [status(thm)], [f_122])).
% 27.65/16.91  tff(c_47803, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_74, c_47797])).
% 27.65/16.91  tff(c_47810, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_47803])).
% 27.65/16.91  tff(c_47812, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_47315, c_47810])).
% 27.65/16.91  tff(c_47813, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_47311])).
% 27.65/16.91  tff(c_46065, plain, (k7_relat_1('#skF_6', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_46057, c_46057, c_46057, c_6880])).
% 27.65/16.91  tff(c_47834, plain, (k7_relat_1('#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_47813, c_47813, c_47813, c_46065])).
% 27.65/16.91  tff(c_46268, plain, (![A_1502, B_1503]: (r1_xboole_0(A_1502, B_1503) | ~r1_subset_1(A_1502, B_1503) | v1_xboole_0(B_1503) | v1_xboole_0(A_1502))), inference(cnfTransformation, [status(thm)], [f_88])).
% 27.65/16.91  tff(c_46063, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)='#skF_6' | ~r1_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_46057, c_2])).
% 27.65/16.91  tff(c_46282, plain, (![A_1502, B_1503]: (k3_xboole_0(A_1502, B_1503)='#skF_6' | ~r1_subset_1(A_1502, B_1503) | v1_xboole_0(B_1503) | v1_xboole_0(A_1502))), inference(resolution, [status(thm)], [c_46268, c_46063])).
% 27.65/16.91  tff(c_48641, plain, (![A_1691, B_1692]: (k3_xboole_0(A_1691, B_1692)='#skF_4' | ~r1_subset_1(A_1691, B_1692) | v1_xboole_0(B_1692) | v1_xboole_0(A_1691))), inference(demodulation, [status(thm), theory('equality')], [c_47813, c_46282])).
% 27.65/16.91  tff(c_48647, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4' | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_80, c_48641])).
% 27.65/16.91  tff(c_48651, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_88, c_84, c_48647])).
% 27.65/16.91  tff(c_47246, plain, (![A_1574, B_1575, C_1576]: (k9_subset_1(A_1574, B_1575, C_1576)=k3_xboole_0(B_1575, C_1576) | ~m1_subset_1(C_1576, k1_zfmisc_1(A_1574)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 27.65/16.91  tff(c_47258, plain, (![B_1575]: (k9_subset_1('#skF_2', B_1575, '#skF_5')=k3_xboole_0(B_1575, '#skF_5'))), inference(resolution, [status(thm)], [c_82, c_47246])).
% 27.65/16.91  tff(c_46184, plain, (v4_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_68, c_46177])).
% 27.65/16.91  tff(c_47305, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_46184, c_47296])).
% 27.65/16.91  tff(c_47314, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6976, c_47305])).
% 27.65/16.91  tff(c_47950, plain, (~v1_partfun1('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_47314])).
% 27.65/16.91  tff(c_48019, plain, (![C_1634, A_1635, B_1636]: (v1_partfun1(C_1634, A_1635) | ~v1_funct_2(C_1634, A_1635, B_1636) | ~v1_funct_1(C_1634) | ~m1_subset_1(C_1634, k1_zfmisc_1(k2_zfmisc_1(A_1635, B_1636))) | v1_xboole_0(B_1636))), inference(cnfTransformation, [status(thm)], [f_122])).
% 27.65/16.91  tff(c_48025, plain, (v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_68, c_48019])).
% 27.65/16.91  tff(c_48032, plain, (v1_partfun1('#skF_7', '#skF_5') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_48025])).
% 27.65/16.92  tff(c_48034, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_47950, c_48032])).
% 27.65/16.92  tff(c_48035, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitRight, [status(thm)], [c_47314])).
% 27.65/16.92  tff(c_46186, plain, (![A_16, B_18]: (k7_relat_1(A_16, B_18)='#skF_6' | ~r1_xboole_0(B_18, k1_relat_1(A_16)) | ~v1_relat_1(A_16))), inference(demodulation, [status(thm), theory('equality')], [c_46057, c_16])).
% 27.65/16.92  tff(c_48303, plain, (![A_1662, B_1663]: (k7_relat_1(A_1662, B_1663)='#skF_4' | ~r1_xboole_0(B_1663, k1_relat_1(A_1662)) | ~v1_relat_1(A_1662))), inference(demodulation, [status(thm), theory('equality')], [c_47813, c_46186])).
% 27.65/16.92  tff(c_48314, plain, (![B_1663]: (k7_relat_1('#skF_7', B_1663)='#skF_4' | ~r1_xboole_0(B_1663, '#skF_5') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_48035, c_48303])).
% 27.65/16.92  tff(c_48329, plain, (![B_1664]: (k7_relat_1('#skF_7', B_1664)='#skF_4' | ~r1_xboole_0(B_1664, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_6976, c_48314])).
% 27.65/16.92  tff(c_48341, plain, (![A_23]: (k7_relat_1('#skF_7', A_23)='#skF_4' | ~r1_subset_1(A_23, '#skF_5') | v1_xboole_0('#skF_5') | v1_xboole_0(A_23))), inference(resolution, [status(thm)], [c_32, c_48329])).
% 27.65/16.92  tff(c_48419, plain, (![A_1672]: (k7_relat_1('#skF_7', A_1672)='#skF_4' | ~r1_subset_1(A_1672, '#skF_5') | v1_xboole_0(A_1672))), inference(negUnitSimplification, [status(thm)], [c_84, c_48341])).
% 27.65/16.92  tff(c_48422, plain, (k7_relat_1('#skF_7', '#skF_4')='#skF_4' | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_80, c_48419])).
% 27.65/16.92  tff(c_48425, plain, (k7_relat_1('#skF_7', '#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_88, c_48422])).
% 27.65/16.92  tff(c_47842, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_47813, c_78])).
% 27.65/16.92  tff(c_47841, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_47813, c_76])).
% 27.65/16.92  tff(c_47840, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_47813, c_74])).
% 27.65/16.92  tff(c_48222, plain, (![D_1653, F_1656, B_1655, A_1651, E_1652, C_1654]: (v1_funct_1(k1_tmap_1(A_1651, B_1655, C_1654, D_1653, E_1652, F_1656)) | ~m1_subset_1(F_1656, k1_zfmisc_1(k2_zfmisc_1(D_1653, B_1655))) | ~v1_funct_2(F_1656, D_1653, B_1655) | ~v1_funct_1(F_1656) | ~m1_subset_1(E_1652, k1_zfmisc_1(k2_zfmisc_1(C_1654, B_1655))) | ~v1_funct_2(E_1652, C_1654, B_1655) | ~v1_funct_1(E_1652) | ~m1_subset_1(D_1653, k1_zfmisc_1(A_1651)) | v1_xboole_0(D_1653) | ~m1_subset_1(C_1654, k1_zfmisc_1(A_1651)) | v1_xboole_0(C_1654) | v1_xboole_0(B_1655) | v1_xboole_0(A_1651))), inference(cnfTransformation, [status(thm)], [f_218])).
% 27.65/16.92  tff(c_48226, plain, (![A_1651, C_1654, E_1652]: (v1_funct_1(k1_tmap_1(A_1651, '#skF_3', C_1654, '#skF_5', E_1652, '#skF_7')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_1652, k1_zfmisc_1(k2_zfmisc_1(C_1654, '#skF_3'))) | ~v1_funct_2(E_1652, C_1654, '#skF_3') | ~v1_funct_1(E_1652) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1651)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1654, k1_zfmisc_1(A_1651)) | v1_xboole_0(C_1654) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1651))), inference(resolution, [status(thm)], [c_68, c_48222])).
% 27.65/16.92  tff(c_48233, plain, (![A_1651, C_1654, E_1652]: (v1_funct_1(k1_tmap_1(A_1651, '#skF_3', C_1654, '#skF_5', E_1652, '#skF_7')) | ~m1_subset_1(E_1652, k1_zfmisc_1(k2_zfmisc_1(C_1654, '#skF_3'))) | ~v1_funct_2(E_1652, C_1654, '#skF_3') | ~v1_funct_1(E_1652) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1651)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1654, k1_zfmisc_1(A_1651)) | v1_xboole_0(C_1654) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1651))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_48226])).
% 27.65/16.92  tff(c_48508, plain, (![A_1681, C_1682, E_1683]: (v1_funct_1(k1_tmap_1(A_1681, '#skF_3', C_1682, '#skF_5', E_1683, '#skF_7')) | ~m1_subset_1(E_1683, k1_zfmisc_1(k2_zfmisc_1(C_1682, '#skF_3'))) | ~v1_funct_2(E_1683, C_1682, '#skF_3') | ~v1_funct_1(E_1683) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1681)) | ~m1_subset_1(C_1682, k1_zfmisc_1(A_1681)) | v1_xboole_0(C_1682) | v1_xboole_0(A_1681))), inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_48233])).
% 27.65/16.92  tff(c_48513, plain, (![A_1681]: (v1_funct_1(k1_tmap_1(A_1681, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~v1_funct_2('#skF_4', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1681)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1681)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1681))), inference(resolution, [status(thm)], [c_47840, c_48508])).
% 27.65/16.92  tff(c_48521, plain, (![A_1681]: (v1_funct_1(k1_tmap_1(A_1681, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1681)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1681)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1681))), inference(demodulation, [status(thm), theory('equality')], [c_47842, c_47841, c_48513])).
% 27.65/16.92  tff(c_48791, plain, (![A_1710]: (v1_funct_1(k1_tmap_1(A_1710, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1710)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1710)) | v1_xboole_0(A_1710))), inference(negUnitSimplification, [status(thm)], [c_88, c_48521])).
% 27.65/16.92  tff(c_48794, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_82, c_48791])).
% 27.65/16.92  tff(c_48797, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_48794])).
% 27.65/16.92  tff(c_48798, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_92, c_48797])).
% 27.65/16.92  tff(c_48063, plain, (![D_42]: (k2_partfun1('#skF_4', '#skF_3', '#skF_4', D_42)=k7_relat_1('#skF_4', D_42) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_47840, c_52])).
% 27.65/16.92  tff(c_48080, plain, (![D_42]: (k2_partfun1('#skF_4', '#skF_3', '#skF_4', D_42)=k7_relat_1('#skF_4', D_42))), inference(demodulation, [status(thm), theory('equality')], [c_47842, c_48063])).
% 27.65/16.92  tff(c_47943, plain, (![A_1623, B_1624, C_1625, D_1626]: (k2_partfun1(A_1623, B_1624, C_1625, D_1626)=k7_relat_1(C_1625, D_1626) | ~m1_subset_1(C_1625, k1_zfmisc_1(k2_zfmisc_1(A_1623, B_1624))) | ~v1_funct_1(C_1625))), inference(cnfTransformation, [status(thm)], [f_136])).
% 27.65/16.92  tff(c_47945, plain, (![D_1626]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_1626)=k7_relat_1('#skF_7', D_1626) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_68, c_47943])).
% 27.65/16.92  tff(c_47948, plain, (![D_1626]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_1626)=k7_relat_1('#skF_7', D_1626))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_47945])).
% 27.65/16.92  tff(c_48652, plain, (![D_1694, E_1698, F_1693, A_1695, B_1696, C_1697]: (k2_partfun1(k4_subset_1(A_1695, C_1697, D_1694), B_1696, k1_tmap_1(A_1695, B_1696, C_1697, D_1694, E_1698, F_1693), D_1694)=F_1693 | ~m1_subset_1(k1_tmap_1(A_1695, B_1696, C_1697, D_1694, E_1698, F_1693), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1695, C_1697, D_1694), B_1696))) | ~v1_funct_2(k1_tmap_1(A_1695, B_1696, C_1697, D_1694, E_1698, F_1693), k4_subset_1(A_1695, C_1697, D_1694), B_1696) | ~v1_funct_1(k1_tmap_1(A_1695, B_1696, C_1697, D_1694, E_1698, F_1693)) | k2_partfun1(D_1694, B_1696, F_1693, k9_subset_1(A_1695, C_1697, D_1694))!=k2_partfun1(C_1697, B_1696, E_1698, k9_subset_1(A_1695, C_1697, D_1694)) | ~m1_subset_1(F_1693, k1_zfmisc_1(k2_zfmisc_1(D_1694, B_1696))) | ~v1_funct_2(F_1693, D_1694, B_1696) | ~v1_funct_1(F_1693) | ~m1_subset_1(E_1698, k1_zfmisc_1(k2_zfmisc_1(C_1697, B_1696))) | ~v1_funct_2(E_1698, C_1697, B_1696) | ~v1_funct_1(E_1698) | ~m1_subset_1(D_1694, k1_zfmisc_1(A_1695)) | v1_xboole_0(D_1694) | ~m1_subset_1(C_1697, k1_zfmisc_1(A_1695)) | v1_xboole_0(C_1697) | v1_xboole_0(B_1696) | v1_xboole_0(A_1695))), inference(cnfTransformation, [status(thm)], [f_184])).
% 27.65/16.92  tff(c_53370, plain, (![C_1878, A_1875, F_1880, B_1879, E_1876, D_1877]: (k2_partfun1(k4_subset_1(A_1875, C_1878, D_1877), B_1879, k1_tmap_1(A_1875, B_1879, C_1878, D_1877, E_1876, F_1880), D_1877)=F_1880 | ~v1_funct_2(k1_tmap_1(A_1875, B_1879, C_1878, D_1877, E_1876, F_1880), k4_subset_1(A_1875, C_1878, D_1877), B_1879) | ~v1_funct_1(k1_tmap_1(A_1875, B_1879, C_1878, D_1877, E_1876, F_1880)) | k2_partfun1(D_1877, B_1879, F_1880, k9_subset_1(A_1875, C_1878, D_1877))!=k2_partfun1(C_1878, B_1879, E_1876, k9_subset_1(A_1875, C_1878, D_1877)) | ~m1_subset_1(F_1880, k1_zfmisc_1(k2_zfmisc_1(D_1877, B_1879))) | ~v1_funct_2(F_1880, D_1877, B_1879) | ~v1_funct_1(F_1880) | ~m1_subset_1(E_1876, k1_zfmisc_1(k2_zfmisc_1(C_1878, B_1879))) | ~v1_funct_2(E_1876, C_1878, B_1879) | ~v1_funct_1(E_1876) | ~m1_subset_1(D_1877, k1_zfmisc_1(A_1875)) | v1_xboole_0(D_1877) | ~m1_subset_1(C_1878, k1_zfmisc_1(A_1875)) | v1_xboole_0(C_1878) | v1_xboole_0(B_1879) | v1_xboole_0(A_1875))), inference(resolution, [status(thm)], [c_60, c_48652])).
% 27.65/16.92  tff(c_62150, plain, (![E_2005, F_2009, A_2004, D_2006, C_2007, B_2008]: (k2_partfun1(k4_subset_1(A_2004, C_2007, D_2006), B_2008, k1_tmap_1(A_2004, B_2008, C_2007, D_2006, E_2005, F_2009), D_2006)=F_2009 | ~v1_funct_1(k1_tmap_1(A_2004, B_2008, C_2007, D_2006, E_2005, F_2009)) | k2_partfun1(D_2006, B_2008, F_2009, k9_subset_1(A_2004, C_2007, D_2006))!=k2_partfun1(C_2007, B_2008, E_2005, k9_subset_1(A_2004, C_2007, D_2006)) | ~m1_subset_1(F_2009, k1_zfmisc_1(k2_zfmisc_1(D_2006, B_2008))) | ~v1_funct_2(F_2009, D_2006, B_2008) | ~v1_funct_1(F_2009) | ~m1_subset_1(E_2005, k1_zfmisc_1(k2_zfmisc_1(C_2007, B_2008))) | ~v1_funct_2(E_2005, C_2007, B_2008) | ~v1_funct_1(E_2005) | ~m1_subset_1(D_2006, k1_zfmisc_1(A_2004)) | v1_xboole_0(D_2006) | ~m1_subset_1(C_2007, k1_zfmisc_1(A_2004)) | v1_xboole_0(C_2007) | v1_xboole_0(B_2008) | v1_xboole_0(A_2004))), inference(resolution, [status(thm)], [c_62, c_53370])).
% 27.65/16.92  tff(c_62156, plain, (![A_2004, C_2007, E_2005]: (k2_partfun1(k4_subset_1(A_2004, C_2007, '#skF_5'), '#skF_3', k1_tmap_1(A_2004, '#skF_3', C_2007, '#skF_5', E_2005, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_2004, '#skF_3', C_2007, '#skF_5', E_2005, '#skF_7')) | k2_partfun1(C_2007, '#skF_3', E_2005, k9_subset_1(A_2004, C_2007, '#skF_5'))!=k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1(A_2004, C_2007, '#skF_5')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_2005, k1_zfmisc_1(k2_zfmisc_1(C_2007, '#skF_3'))) | ~v1_funct_2(E_2005, C_2007, '#skF_3') | ~v1_funct_1(E_2005) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2004)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_2007, k1_zfmisc_1(A_2004)) | v1_xboole_0(C_2007) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2004))), inference(resolution, [status(thm)], [c_68, c_62150])).
% 27.65/16.92  tff(c_62164, plain, (![A_2004, C_2007, E_2005]: (k2_partfun1(k4_subset_1(A_2004, C_2007, '#skF_5'), '#skF_3', k1_tmap_1(A_2004, '#skF_3', C_2007, '#skF_5', E_2005, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_2004, '#skF_3', C_2007, '#skF_5', E_2005, '#skF_7')) | k2_partfun1(C_2007, '#skF_3', E_2005, k9_subset_1(A_2004, C_2007, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_2004, C_2007, '#skF_5')) | ~m1_subset_1(E_2005, k1_zfmisc_1(k2_zfmisc_1(C_2007, '#skF_3'))) | ~v1_funct_2(E_2005, C_2007, '#skF_3') | ~v1_funct_1(E_2005) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2004)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_2007, k1_zfmisc_1(A_2004)) | v1_xboole_0(C_2007) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2004))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_47948, c_62156])).
% 27.65/16.92  tff(c_62603, plain, (![A_2012, C_2013, E_2014]: (k2_partfun1(k4_subset_1(A_2012, C_2013, '#skF_5'), '#skF_3', k1_tmap_1(A_2012, '#skF_3', C_2013, '#skF_5', E_2014, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_2012, '#skF_3', C_2013, '#skF_5', E_2014, '#skF_7')) | k2_partfun1(C_2013, '#skF_3', E_2014, k9_subset_1(A_2012, C_2013, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_2012, C_2013, '#skF_5')) | ~m1_subset_1(E_2014, k1_zfmisc_1(k2_zfmisc_1(C_2013, '#skF_3'))) | ~v1_funct_2(E_2014, C_2013, '#skF_3') | ~v1_funct_1(E_2014) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2012)) | ~m1_subset_1(C_2013, k1_zfmisc_1(A_2012)) | v1_xboole_0(C_2013) | v1_xboole_0(A_2012))), inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_62164])).
% 27.65/16.92  tff(c_62608, plain, (![A_2012]: (k2_partfun1(k4_subset_1(A_2012, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_2012, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_2012, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | k2_partfun1('#skF_4', '#skF_3', '#skF_4', k9_subset_1(A_2012, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_2012, '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_4', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2012)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2012)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_2012))), inference(resolution, [status(thm)], [c_47840, c_62603])).
% 27.65/16.92  tff(c_62616, plain, (![A_2012]: (k2_partfun1(k4_subset_1(A_2012, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_2012, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_2012, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_2012, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_4', k9_subset_1(A_2012, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2012)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2012)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_2012))), inference(demodulation, [status(thm), theory('equality')], [c_47842, c_47841, c_48080, c_62608])).
% 27.65/16.92  tff(c_64456, plain, (![A_2040]: (k2_partfun1(k4_subset_1(A_2040, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_2040, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_2040, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_2040, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_4', k9_subset_1(A_2040, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2040)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2040)) | v1_xboole_0(A_2040))), inference(negUnitSimplification, [status(thm)], [c_88, c_62616])).
% 27.65/16.92  tff(c_47826, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), '#skF_5')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_47813, c_6995])).
% 27.65/16.92  tff(c_64465, plain, (~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k7_relat_1('#skF_4', k9_subset_1('#skF_2', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_64456, c_47826])).
% 27.65/16.92  tff(c_64478, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_47834, c_48651, c_47258, c_48425, c_48651, c_47258, c_48798, c_64465])).
% 27.65/16.92  tff(c_64480, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_64478])).
% 27.65/16.92  tff(c_64481, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_6549])).
% 27.65/16.92  tff(c_64499, plain, (![C_2043, A_2044, B_2045]: (v4_relat_1(C_2043, A_2044) | ~m1_subset_1(C_2043, k1_zfmisc_1(k2_zfmisc_1(A_2044, B_2045))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 27.65/16.92  tff(c_64507, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_74, c_64499])).
% 27.65/16.92  tff(c_64683, plain, (![B_2067, A_2068]: (k1_relat_1(B_2067)=A_2068 | ~v1_partfun1(B_2067, A_2068) | ~v4_relat_1(B_2067, A_2068) | ~v1_relat_1(B_2067))), inference(cnfTransformation, [status(thm)], [f_130])).
% 27.65/16.92  tff(c_64686, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_64507, c_64683])).
% 27.65/16.92  tff(c_64692, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6977, c_64686])).
% 27.65/16.92  tff(c_64696, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_64692])).
% 27.65/16.92  tff(c_65085, plain, (![C_2099, A_2100, B_2101]: (v1_partfun1(C_2099, A_2100) | ~v1_funct_2(C_2099, A_2100, B_2101) | ~v1_funct_1(C_2099) | ~m1_subset_1(C_2099, k1_zfmisc_1(k2_zfmisc_1(A_2100, B_2101))) | v1_xboole_0(B_2101))), inference(cnfTransformation, [status(thm)], [f_122])).
% 27.65/16.92  tff(c_65091, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_74, c_65085])).
% 27.65/16.92  tff(c_65098, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_65091])).
% 27.65/16.92  tff(c_65100, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_64696, c_65098])).
% 27.65/16.92  tff(c_65101, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_64692])).
% 27.65/16.92  tff(c_64483, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_6993])).
% 27.65/16.92  tff(c_65103, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_65101, c_64483])).
% 27.65/16.92  tff(c_65107, plain, (![B_18]: (k7_relat_1('#skF_6', B_18)=k1_xboole_0 | ~r1_xboole_0(B_18, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_65101, c_16])).
% 27.65/16.92  tff(c_65439, plain, (![B_2119]: (k7_relat_1('#skF_6', B_2119)=k1_xboole_0 | ~r1_xboole_0(B_2119, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6977, c_65107])).
% 27.65/16.92  tff(c_65451, plain, (k7_relat_1('#skF_6', '#skF_1'('#skF_4'))=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_40, c_65439])).
% 27.65/16.92  tff(c_65458, plain, (k7_relat_1('#skF_6', '#skF_1'('#skF_4'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_65103, c_65451])).
% 27.65/16.92  tff(c_65462, plain, (r1_tarski(k1_relat_1(k1_xboole_0), '#skF_1'('#skF_4')) | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_65458, c_26])).
% 27.65/16.92  tff(c_65469, plain, (r1_tarski(k1_xboole_0, '#skF_1'('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6977, c_20, c_65462])).
% 27.65/16.92  tff(c_65473, plain, (![C_2120, B_2121, A_2122]: (k7_relat_1(k7_relat_1(C_2120, B_2121), A_2122)=k7_relat_1(C_2120, A_2122) | ~r1_tarski(A_2122, B_2121) | ~v1_relat_1(C_2120))), inference(cnfTransformation, [status(thm)], [f_52])).
% 27.65/16.92  tff(c_65498, plain, (![A_2122]: (k7_relat_1(k1_xboole_0, A_2122)=k7_relat_1('#skF_6', A_2122) | ~r1_tarski(A_2122, '#skF_1'('#skF_4')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_65458, c_65473])).
% 27.65/16.92  tff(c_65933, plain, (![A_2151]: (k7_relat_1(k1_xboole_0, A_2151)=k7_relat_1('#skF_6', A_2151) | ~r1_tarski(A_2151, '#skF_1'('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_6977, c_65498])).
% 27.65/16.92  tff(c_65944, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k7_relat_1('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_65469, c_65933])).
% 27.65/16.92  tff(c_65958, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6880, c_65944])).
% 27.65/16.92  tff(c_64517, plain, (![A_2049, B_2050]: (r1_xboole_0(A_2049, B_2050) | ~r1_subset_1(A_2049, B_2050) | v1_xboole_0(B_2050) | v1_xboole_0(A_2049))), inference(cnfTransformation, [status(thm)], [f_88])).
% 27.65/16.92  tff(c_66096, plain, (![A_2162, B_2163]: (k3_xboole_0(A_2162, B_2163)=k1_xboole_0 | ~r1_subset_1(A_2162, B_2163) | v1_xboole_0(B_2163) | v1_xboole_0(A_2162))), inference(resolution, [status(thm)], [c_64517, c_2])).
% 27.65/16.92  tff(c_66099, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0 | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_80, c_66096])).
% 27.65/16.92  tff(c_66102, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_88, c_84, c_66099])).
% 27.65/16.92  tff(c_64591, plain, (![A_2058, B_2059, C_2060]: (k9_subset_1(A_2058, B_2059, C_2060)=k3_xboole_0(B_2059, C_2060) | ~m1_subset_1(C_2060, k1_zfmisc_1(A_2058)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 27.65/16.92  tff(c_64603, plain, (![B_2059]: (k9_subset_1('#skF_2', B_2059, '#skF_5')=k3_xboole_0(B_2059, '#skF_5'))), inference(resolution, [status(thm)], [c_82, c_64591])).
% 27.65/16.92  tff(c_64506, plain, (v4_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_68, c_64499])).
% 27.65/16.92  tff(c_64689, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_64506, c_64683])).
% 27.65/16.92  tff(c_64695, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6976, c_64689])).
% 27.65/16.92  tff(c_65153, plain, (~v1_partfun1('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_64695])).
% 27.65/16.92  tff(c_65379, plain, (![C_2116, A_2117, B_2118]: (v1_partfun1(C_2116, A_2117) | ~v1_funct_2(C_2116, A_2117, B_2118) | ~v1_funct_1(C_2116) | ~m1_subset_1(C_2116, k1_zfmisc_1(k2_zfmisc_1(A_2117, B_2118))) | v1_xboole_0(B_2118))), inference(cnfTransformation, [status(thm)], [f_122])).
% 27.65/16.92  tff(c_65382, plain, (v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_68, c_65379])).
% 27.65/16.92  tff(c_65388, plain, (v1_partfun1('#skF_7', '#skF_5') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_65382])).
% 27.65/16.92  tff(c_65390, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_65153, c_65388])).
% 27.65/16.92  tff(c_65391, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitRight, [status(thm)], [c_64695])).
% 27.65/16.92  tff(c_65397, plain, (![B_18]: (k7_relat_1('#skF_7', B_18)=k1_xboole_0 | ~r1_xboole_0(B_18, '#skF_5') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_65391, c_16])).
% 27.65/16.92  tff(c_65535, plain, (![B_2123]: (k7_relat_1('#skF_7', B_2123)=k1_xboole_0 | ~r1_xboole_0(B_2123, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_6976, c_65397])).
% 27.65/16.92  tff(c_65539, plain, (![A_23]: (k7_relat_1('#skF_7', A_23)=k1_xboole_0 | ~r1_subset_1(A_23, '#skF_5') | v1_xboole_0('#skF_5') | v1_xboole_0(A_23))), inference(resolution, [status(thm)], [c_32, c_65535])).
% 27.65/16.92  tff(c_65638, plain, (![A_2131]: (k7_relat_1('#skF_7', A_2131)=k1_xboole_0 | ~r1_subset_1(A_2131, '#skF_5') | v1_xboole_0(A_2131))), inference(negUnitSimplification, [status(thm)], [c_84, c_65539])).
% 27.65/16.92  tff(c_65641, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_80, c_65638])).
% 27.65/16.92  tff(c_65644, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_88, c_65641])).
% 27.65/16.92  tff(c_65654, plain, (r1_tarski(k1_relat_1(k1_xboole_0), '#skF_4') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_65644, c_26])).
% 27.65/16.92  tff(c_65667, plain, (r1_tarski(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6976, c_20, c_65654])).
% 27.65/16.92  tff(c_65651, plain, (![A_13]: (k7_relat_1(k1_xboole_0, A_13)=k7_relat_1('#skF_7', A_13) | ~r1_tarski(A_13, '#skF_4') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_65644, c_14])).
% 27.65/16.92  tff(c_65757, plain, (![A_2138]: (k7_relat_1(k1_xboole_0, A_2138)=k7_relat_1('#skF_7', A_2138) | ~r1_tarski(A_2138, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6976, c_65651])).
% 27.65/16.92  tff(c_65760, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k7_relat_1('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_65667, c_65757])).
% 27.65/16.92  tff(c_65777, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6880, c_65760])).
% 27.65/16.92  tff(c_65626, plain, (![A_2126, B_2127, C_2128, D_2129]: (k2_partfun1(A_2126, B_2127, C_2128, D_2129)=k7_relat_1(C_2128, D_2129) | ~m1_subset_1(C_2128, k1_zfmisc_1(k2_zfmisc_1(A_2126, B_2127))) | ~v1_funct_1(C_2128))), inference(cnfTransformation, [status(thm)], [f_136])).
% 27.65/16.92  tff(c_65628, plain, (![D_2129]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_2129)=k7_relat_1('#skF_7', D_2129) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_68, c_65626])).
% 27.65/16.92  tff(c_65633, plain, (![D_2129]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_2129)=k7_relat_1('#skF_7', D_2129))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_65628])).
% 27.65/16.92  tff(c_65630, plain, (![D_2129]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_2129)=k7_relat_1('#skF_6', D_2129) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_74, c_65626])).
% 27.65/16.92  tff(c_65636, plain, (![D_2129]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_2129)=k7_relat_1('#skF_6', D_2129))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_65630])).
% 27.65/16.92  tff(c_65847, plain, (![F_2145, E_2141, A_2140, C_2143, B_2144, D_2142]: (v1_funct_1(k1_tmap_1(A_2140, B_2144, C_2143, D_2142, E_2141, F_2145)) | ~m1_subset_1(F_2145, k1_zfmisc_1(k2_zfmisc_1(D_2142, B_2144))) | ~v1_funct_2(F_2145, D_2142, B_2144) | ~v1_funct_1(F_2145) | ~m1_subset_1(E_2141, k1_zfmisc_1(k2_zfmisc_1(C_2143, B_2144))) | ~v1_funct_2(E_2141, C_2143, B_2144) | ~v1_funct_1(E_2141) | ~m1_subset_1(D_2142, k1_zfmisc_1(A_2140)) | v1_xboole_0(D_2142) | ~m1_subset_1(C_2143, k1_zfmisc_1(A_2140)) | v1_xboole_0(C_2143) | v1_xboole_0(B_2144) | v1_xboole_0(A_2140))), inference(cnfTransformation, [status(thm)], [f_218])).
% 27.65/16.92  tff(c_65849, plain, (![A_2140, C_2143, E_2141]: (v1_funct_1(k1_tmap_1(A_2140, '#skF_3', C_2143, '#skF_5', E_2141, '#skF_7')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_2141, k1_zfmisc_1(k2_zfmisc_1(C_2143, '#skF_3'))) | ~v1_funct_2(E_2141, C_2143, '#skF_3') | ~v1_funct_1(E_2141) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2140)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_2143, k1_zfmisc_1(A_2140)) | v1_xboole_0(C_2143) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2140))), inference(resolution, [status(thm)], [c_68, c_65847])).
% 27.65/16.92  tff(c_65854, plain, (![A_2140, C_2143, E_2141]: (v1_funct_1(k1_tmap_1(A_2140, '#skF_3', C_2143, '#skF_5', E_2141, '#skF_7')) | ~m1_subset_1(E_2141, k1_zfmisc_1(k2_zfmisc_1(C_2143, '#skF_3'))) | ~v1_funct_2(E_2141, C_2143, '#skF_3') | ~v1_funct_1(E_2141) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2140)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_2143, k1_zfmisc_1(A_2140)) | v1_xboole_0(C_2143) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2140))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_65849])).
% 27.65/16.92  tff(c_66592, plain, (![A_2188, C_2189, E_2190]: (v1_funct_1(k1_tmap_1(A_2188, '#skF_3', C_2189, '#skF_5', E_2190, '#skF_7')) | ~m1_subset_1(E_2190, k1_zfmisc_1(k2_zfmisc_1(C_2189, '#skF_3'))) | ~v1_funct_2(E_2190, C_2189, '#skF_3') | ~v1_funct_1(E_2190) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2188)) | ~m1_subset_1(C_2189, k1_zfmisc_1(A_2188)) | v1_xboole_0(C_2189) | v1_xboole_0(A_2188))), inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_65854])).
% 27.65/16.92  tff(c_66599, plain, (![A_2188]: (v1_funct_1(k1_tmap_1(A_2188, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2188)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2188)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_2188))), inference(resolution, [status(thm)], [c_74, c_66592])).
% 27.65/16.92  tff(c_66609, plain, (![A_2188]: (v1_funct_1(k1_tmap_1(A_2188, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2188)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2188)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_2188))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_66599])).
% 27.65/16.92  tff(c_67303, plain, (![A_2215]: (v1_funct_1(k1_tmap_1(A_2215, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2215)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2215)) | v1_xboole_0(A_2215))), inference(negUnitSimplification, [status(thm)], [c_88, c_66609])).
% 27.65/16.92  tff(c_67306, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_82, c_67303])).
% 27.65/16.92  tff(c_67309, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_67306])).
% 27.65/16.92  tff(c_67310, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_92, c_67309])).
% 27.65/16.92  tff(c_66855, plain, (![A_2197, C_2199, E_2200, B_2198, D_2196, F_2195]: (k2_partfun1(k4_subset_1(A_2197, C_2199, D_2196), B_2198, k1_tmap_1(A_2197, B_2198, C_2199, D_2196, E_2200, F_2195), C_2199)=E_2200 | ~m1_subset_1(k1_tmap_1(A_2197, B_2198, C_2199, D_2196, E_2200, F_2195), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_2197, C_2199, D_2196), B_2198))) | ~v1_funct_2(k1_tmap_1(A_2197, B_2198, C_2199, D_2196, E_2200, F_2195), k4_subset_1(A_2197, C_2199, D_2196), B_2198) | ~v1_funct_1(k1_tmap_1(A_2197, B_2198, C_2199, D_2196, E_2200, F_2195)) | k2_partfun1(D_2196, B_2198, F_2195, k9_subset_1(A_2197, C_2199, D_2196))!=k2_partfun1(C_2199, B_2198, E_2200, k9_subset_1(A_2197, C_2199, D_2196)) | ~m1_subset_1(F_2195, k1_zfmisc_1(k2_zfmisc_1(D_2196, B_2198))) | ~v1_funct_2(F_2195, D_2196, B_2198) | ~v1_funct_1(F_2195) | ~m1_subset_1(E_2200, k1_zfmisc_1(k2_zfmisc_1(C_2199, B_2198))) | ~v1_funct_2(E_2200, C_2199, B_2198) | ~v1_funct_1(E_2200) | ~m1_subset_1(D_2196, k1_zfmisc_1(A_2197)) | v1_xboole_0(D_2196) | ~m1_subset_1(C_2199, k1_zfmisc_1(A_2197)) | v1_xboole_0(C_2199) | v1_xboole_0(B_2198) | v1_xboole_0(A_2197))), inference(cnfTransformation, [status(thm)], [f_184])).
% 27.65/16.92  tff(c_73030, plain, (![A_2378, B_2382, E_2379, D_2380, F_2383, C_2381]: (k2_partfun1(k4_subset_1(A_2378, C_2381, D_2380), B_2382, k1_tmap_1(A_2378, B_2382, C_2381, D_2380, E_2379, F_2383), C_2381)=E_2379 | ~v1_funct_2(k1_tmap_1(A_2378, B_2382, C_2381, D_2380, E_2379, F_2383), k4_subset_1(A_2378, C_2381, D_2380), B_2382) | ~v1_funct_1(k1_tmap_1(A_2378, B_2382, C_2381, D_2380, E_2379, F_2383)) | k2_partfun1(D_2380, B_2382, F_2383, k9_subset_1(A_2378, C_2381, D_2380))!=k2_partfun1(C_2381, B_2382, E_2379, k9_subset_1(A_2378, C_2381, D_2380)) | ~m1_subset_1(F_2383, k1_zfmisc_1(k2_zfmisc_1(D_2380, B_2382))) | ~v1_funct_2(F_2383, D_2380, B_2382) | ~v1_funct_1(F_2383) | ~m1_subset_1(E_2379, k1_zfmisc_1(k2_zfmisc_1(C_2381, B_2382))) | ~v1_funct_2(E_2379, C_2381, B_2382) | ~v1_funct_1(E_2379) | ~m1_subset_1(D_2380, k1_zfmisc_1(A_2378)) | v1_xboole_0(D_2380) | ~m1_subset_1(C_2381, k1_zfmisc_1(A_2378)) | v1_xboole_0(C_2381) | v1_xboole_0(B_2382) | v1_xboole_0(A_2378))), inference(resolution, [status(thm)], [c_60, c_66855])).
% 27.65/16.92  tff(c_87351, plain, (![A_2560, B_2564, E_2561, C_2563, D_2562, F_2565]: (k2_partfun1(k4_subset_1(A_2560, C_2563, D_2562), B_2564, k1_tmap_1(A_2560, B_2564, C_2563, D_2562, E_2561, F_2565), C_2563)=E_2561 | ~v1_funct_1(k1_tmap_1(A_2560, B_2564, C_2563, D_2562, E_2561, F_2565)) | k2_partfun1(D_2562, B_2564, F_2565, k9_subset_1(A_2560, C_2563, D_2562))!=k2_partfun1(C_2563, B_2564, E_2561, k9_subset_1(A_2560, C_2563, D_2562)) | ~m1_subset_1(F_2565, k1_zfmisc_1(k2_zfmisc_1(D_2562, B_2564))) | ~v1_funct_2(F_2565, D_2562, B_2564) | ~v1_funct_1(F_2565) | ~m1_subset_1(E_2561, k1_zfmisc_1(k2_zfmisc_1(C_2563, B_2564))) | ~v1_funct_2(E_2561, C_2563, B_2564) | ~v1_funct_1(E_2561) | ~m1_subset_1(D_2562, k1_zfmisc_1(A_2560)) | v1_xboole_0(D_2562) | ~m1_subset_1(C_2563, k1_zfmisc_1(A_2560)) | v1_xboole_0(C_2563) | v1_xboole_0(B_2564) | v1_xboole_0(A_2560))), inference(resolution, [status(thm)], [c_62, c_73030])).
% 27.65/16.92  tff(c_87355, plain, (![A_2560, C_2563, E_2561]: (k2_partfun1(k4_subset_1(A_2560, C_2563, '#skF_5'), '#skF_3', k1_tmap_1(A_2560, '#skF_3', C_2563, '#skF_5', E_2561, '#skF_7'), C_2563)=E_2561 | ~v1_funct_1(k1_tmap_1(A_2560, '#skF_3', C_2563, '#skF_5', E_2561, '#skF_7')) | k2_partfun1(C_2563, '#skF_3', E_2561, k9_subset_1(A_2560, C_2563, '#skF_5'))!=k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1(A_2560, C_2563, '#skF_5')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_2561, k1_zfmisc_1(k2_zfmisc_1(C_2563, '#skF_3'))) | ~v1_funct_2(E_2561, C_2563, '#skF_3') | ~v1_funct_1(E_2561) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2560)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_2563, k1_zfmisc_1(A_2560)) | v1_xboole_0(C_2563) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2560))), inference(resolution, [status(thm)], [c_68, c_87351])).
% 27.65/16.92  tff(c_87361, plain, (![A_2560, C_2563, E_2561]: (k2_partfun1(k4_subset_1(A_2560, C_2563, '#skF_5'), '#skF_3', k1_tmap_1(A_2560, '#skF_3', C_2563, '#skF_5', E_2561, '#skF_7'), C_2563)=E_2561 | ~v1_funct_1(k1_tmap_1(A_2560, '#skF_3', C_2563, '#skF_5', E_2561, '#skF_7')) | k2_partfun1(C_2563, '#skF_3', E_2561, k9_subset_1(A_2560, C_2563, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_2560, C_2563, '#skF_5')) | ~m1_subset_1(E_2561, k1_zfmisc_1(k2_zfmisc_1(C_2563, '#skF_3'))) | ~v1_funct_2(E_2561, C_2563, '#skF_3') | ~v1_funct_1(E_2561) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2560)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_2563, k1_zfmisc_1(A_2560)) | v1_xboole_0(C_2563) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2560))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_65633, c_87355])).
% 27.65/16.92  tff(c_99324, plain, (![A_2673, C_2674, E_2675]: (k2_partfun1(k4_subset_1(A_2673, C_2674, '#skF_5'), '#skF_3', k1_tmap_1(A_2673, '#skF_3', C_2674, '#skF_5', E_2675, '#skF_7'), C_2674)=E_2675 | ~v1_funct_1(k1_tmap_1(A_2673, '#skF_3', C_2674, '#skF_5', E_2675, '#skF_7')) | k2_partfun1(C_2674, '#skF_3', E_2675, k9_subset_1(A_2673, C_2674, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_2673, C_2674, '#skF_5')) | ~m1_subset_1(E_2675, k1_zfmisc_1(k2_zfmisc_1(C_2674, '#skF_3'))) | ~v1_funct_2(E_2675, C_2674, '#skF_3') | ~v1_funct_1(E_2675) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2673)) | ~m1_subset_1(C_2674, k1_zfmisc_1(A_2673)) | v1_xboole_0(C_2674) | v1_xboole_0(A_2673))), inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_87361])).
% 27.65/16.92  tff(c_99331, plain, (![A_2673]: (k2_partfun1(k4_subset_1(A_2673, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_2673, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_2673, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1(A_2673, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_2673, '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2673)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2673)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_2673))), inference(resolution, [status(thm)], [c_74, c_99324])).
% 27.65/16.92  tff(c_99341, plain, (![A_2673]: (k2_partfun1(k4_subset_1(A_2673, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_2673, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_2673, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_2673, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_2673, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2673)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2673)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_2673))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_65636, c_99331])).
% 27.65/16.92  tff(c_100460, plain, (![A_2685]: (k2_partfun1(k4_subset_1(A_2685, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_2685, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_2685, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_2685, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_2685, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2685)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2685)) | v1_xboole_0(A_2685))), inference(negUnitSimplification, [status(thm)], [c_88, c_99341])).
% 27.65/16.92  tff(c_64482, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')='#skF_7'), inference(splitRight, [status(thm)], [c_6549])).
% 27.65/16.92  tff(c_67083, plain, (![C_2211, B_2210, D_2208, G_2207, A_2209]: (k1_tmap_1(A_2209, B_2210, C_2211, D_2208, k2_partfun1(k4_subset_1(A_2209, C_2211, D_2208), B_2210, G_2207, C_2211), k2_partfun1(k4_subset_1(A_2209, C_2211, D_2208), B_2210, G_2207, D_2208))=G_2207 | ~m1_subset_1(G_2207, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_2209, C_2211, D_2208), B_2210))) | ~v1_funct_2(G_2207, k4_subset_1(A_2209, C_2211, D_2208), B_2210) | ~v1_funct_1(G_2207) | k2_partfun1(D_2208, B_2210, k2_partfun1(k4_subset_1(A_2209, C_2211, D_2208), B_2210, G_2207, D_2208), k9_subset_1(A_2209, C_2211, D_2208))!=k2_partfun1(C_2211, B_2210, k2_partfun1(k4_subset_1(A_2209, C_2211, D_2208), B_2210, G_2207, C_2211), k9_subset_1(A_2209, C_2211, D_2208)) | ~m1_subset_1(k2_partfun1(k4_subset_1(A_2209, C_2211, D_2208), B_2210, G_2207, D_2208), k1_zfmisc_1(k2_zfmisc_1(D_2208, B_2210))) | ~v1_funct_2(k2_partfun1(k4_subset_1(A_2209, C_2211, D_2208), B_2210, G_2207, D_2208), D_2208, B_2210) | ~v1_funct_1(k2_partfun1(k4_subset_1(A_2209, C_2211, D_2208), B_2210, G_2207, D_2208)) | ~m1_subset_1(k2_partfun1(k4_subset_1(A_2209, C_2211, D_2208), B_2210, G_2207, C_2211), k1_zfmisc_1(k2_zfmisc_1(C_2211, B_2210))) | ~v1_funct_2(k2_partfun1(k4_subset_1(A_2209, C_2211, D_2208), B_2210, G_2207, C_2211), C_2211, B_2210) | ~v1_funct_1(k2_partfun1(k4_subset_1(A_2209, C_2211, D_2208), B_2210, G_2207, C_2211)) | ~m1_subset_1(D_2208, k1_zfmisc_1(A_2209)) | v1_xboole_0(D_2208) | ~m1_subset_1(C_2211, k1_zfmisc_1(A_2209)) | v1_xboole_0(C_2211) | v1_xboole_0(B_2210) | v1_xboole_0(A_2209))), inference(cnfTransformation, [status(thm)], [f_184])).
% 27.65/16.92  tff(c_67085, plain, (k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5'))=k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7') | ~m1_subset_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3'))) | ~v1_funct_2(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3') | ~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k2_partfun1('#skF_5', '#skF_3', k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5'), k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), k9_subset_1('#skF_2', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3'))) | ~v1_funct_2(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5'), '#skF_5', '#skF_3') | ~v1_funct_1(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')) | ~m1_subset_1(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_64482, c_67083])).
% 27.65/16.92  tff(c_67087, plain, (k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), '#skF_7')=k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7') | ~m1_subset_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3'))) | ~v1_funct_2(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3') | ~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k2_partfun1('#skF_4', '#skF_3', k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), k1_xboole_0)!=k1_xboole_0 | ~m1_subset_1(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')) | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_72, c_64482, c_70, c_64482, c_68, c_65777, c_66102, c_66102, c_65633, c_64482, c_64603, c_64603, c_64482, c_67085])).
% 27.65/16.92  tff(c_67088, plain, (k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), '#skF_7')=k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7') | ~m1_subset_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3'))) | ~v1_funct_2(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3') | ~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k2_partfun1('#skF_4', '#skF_3', k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), k1_xboole_0)!=k1_xboole_0 | ~m1_subset_1(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_92, c_90, c_88, c_84, c_67087])).
% 27.65/16.92  tff(c_68873, plain, (k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), '#skF_7')=k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7') | ~m1_subset_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3'))) | ~v1_funct_2(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3') | k2_partfun1('#skF_4', '#skF_3', k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), k1_xboole_0)!=k1_xboole_0 | ~m1_subset_1(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_67310, c_67088])).
% 27.65/16.92  tff(c_68874, plain, (~v1_funct_1(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'))), inference(splitLeft, [status(thm)], [c_68873])).
% 27.65/16.92  tff(c_100469, plain, (~v1_funct_1('#skF_6') | ~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_100460, c_68874])).
% 27.65/16.92  tff(c_100482, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_65958, c_66102, c_65777, c_66102, c_64603, c_64603, c_67310, c_78, c_100469])).
% 27.65/16.92  tff(c_100484, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_100482])).
% 27.65/16.92  tff(c_100485, plain, (~v1_funct_2(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), '#skF_4', '#skF_3') | ~m1_subset_1(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | k2_partfun1('#skF_4', '#skF_3', k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), k1_xboole_0)!=k1_xboole_0 | ~v1_funct_2(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3') | ~m1_subset_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3'))) | k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), '#skF_7')=k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_68873])).
% 27.65/16.92  tff(c_101339, plain, (~m1_subset_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3')))), inference(splitLeft, [status(thm)], [c_100485])).
% 27.65/16.92  tff(c_104969, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3'))) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_101339])).
% 27.65/16.92  tff(c_104972, plain, (v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_78, c_76, c_74, c_72, c_70, c_68, c_104969])).
% 27.65/16.92  tff(c_104974, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_90, c_88, c_84, c_104972])).
% 27.65/16.92  tff(c_104976, plain, (m1_subset_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3')))), inference(splitRight, [status(thm)], [c_100485])).
% 27.65/16.92  tff(c_44, plain, (![C_36, A_33, B_34]: (v1_partfun1(C_36, A_33) | ~v1_funct_2(C_36, A_33, B_34) | ~v1_funct_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))) | v1_xboole_0(B_34))), inference(cnfTransformation, [status(thm)], [f_122])).
% 27.65/16.92  tff(c_108626, plain, (v1_partfun1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k4_subset_1('#skF_2', '#skF_4', '#skF_5')) | ~v1_funct_2(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3') | ~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_104976, c_44])).
% 27.65/16.92  tff(c_108679, plain, (v1_partfun1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k4_subset_1('#skF_2', '#skF_4', '#skF_5')) | ~v1_funct_2(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_67310, c_108626])).
% 27.65/16.92  tff(c_108680, plain, (v1_partfun1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k4_subset_1('#skF_2', '#skF_4', '#skF_5')) | ~v1_funct_2(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_90, c_108679])).
% 27.65/16.92  tff(c_109054, plain, (~v1_funct_2(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_108680])).
% 27.65/16.92  tff(c_109838, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3'))) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_62, c_109054])).
% 27.65/16.92  tff(c_109841, plain, (v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_78, c_76, c_74, c_72, c_70, c_68, c_109838])).
% 27.65/16.92  tff(c_109843, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_90, c_88, c_84, c_109841])).
% 27.65/16.92  tff(c_109845, plain, (v1_funct_2(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3')), inference(splitRight, [status(thm)], [c_108680])).
% 27.65/16.92  tff(c_66858, plain, (![A_170, D_173, E_174, B_171, C_172, F_175]: (k2_partfun1(k4_subset_1(A_170, C_172, D_173), B_171, k1_tmap_1(A_170, B_171, C_172, D_173, E_174, F_175), C_172)=E_174 | ~v1_funct_2(k1_tmap_1(A_170, B_171, C_172, D_173, E_174, F_175), k4_subset_1(A_170, C_172, D_173), B_171) | ~v1_funct_1(k1_tmap_1(A_170, B_171, C_172, D_173, E_174, F_175)) | k2_partfun1(D_173, B_171, F_175, k9_subset_1(A_170, C_172, D_173))!=k2_partfun1(C_172, B_171, E_174, k9_subset_1(A_170, C_172, D_173)) | ~m1_subset_1(F_175, k1_zfmisc_1(k2_zfmisc_1(D_173, B_171))) | ~v1_funct_2(F_175, D_173, B_171) | ~v1_funct_1(F_175) | ~m1_subset_1(E_174, k1_zfmisc_1(k2_zfmisc_1(C_172, B_171))) | ~v1_funct_2(E_174, C_172, B_171) | ~v1_funct_1(E_174) | ~m1_subset_1(D_173, k1_zfmisc_1(A_170)) | v1_xboole_0(D_173) | ~m1_subset_1(C_172, k1_zfmisc_1(A_170)) | v1_xboole_0(C_172) | v1_xboole_0(B_171) | v1_xboole_0(A_170))), inference(resolution, [status(thm)], [c_60, c_66855])).
% 27.65/16.92  tff(c_111781, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3'))) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_109845, c_66858])).
% 27.65/16.92  tff(c_111789, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_78, c_76, c_74, c_72, c_70, c_68, c_65958, c_66102, c_64603, c_65777, c_66102, c_64603, c_65633, c_65636, c_67310, c_111781])).
% 27.65/16.92  tff(c_111791, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_90, c_88, c_84, c_64481, c_111789])).
% 27.65/16.92  tff(c_111792, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_6993])).
% 27.65/16.92  tff(c_111793, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_6993])).
% 27.65/16.92  tff(c_111820, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_111792, c_111793])).
% 27.65/16.92  tff(c_111886, plain, (![C_3045, A_3046, B_3047]: (v4_relat_1(C_3045, A_3046) | ~m1_subset_1(C_3045, k1_zfmisc_1(k2_zfmisc_1(A_3046, B_3047))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 27.65/16.92  tff(c_111894, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_74, c_111886])).
% 27.65/16.92  tff(c_113088, plain, (![B_3133, A_3134]: (k1_relat_1(B_3133)=A_3134 | ~v1_partfun1(B_3133, A_3134) | ~v4_relat_1(B_3133, A_3134) | ~v1_relat_1(B_3133))), inference(cnfTransformation, [status(thm)], [f_130])).
% 27.65/16.92  tff(c_113094, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_111894, c_113088])).
% 27.65/16.92  tff(c_113103, plain, ('#skF_6'='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6977, c_111820, c_113094])).
% 27.65/16.92  tff(c_113107, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_113103])).
% 27.65/16.92  tff(c_113844, plain, (![C_3180, A_3181, B_3182]: (v1_partfun1(C_3180, A_3181) | ~v1_funct_2(C_3180, A_3181, B_3182) | ~v1_funct_1(C_3180) | ~m1_subset_1(C_3180, k1_zfmisc_1(k2_zfmisc_1(A_3181, B_3182))) | v1_xboole_0(B_3182))), inference(cnfTransformation, [status(thm)], [f_122])).
% 27.65/16.92  tff(c_113850, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_74, c_113844])).
% 27.65/16.92  tff(c_113857, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_113850])).
% 27.65/16.92  tff(c_113859, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_113107, c_113857])).
% 27.65/16.92  tff(c_113860, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_113103])).
% 27.65/16.92  tff(c_113889, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_113860, c_78])).
% 27.65/16.92  tff(c_113888, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_113860, c_76])).
% 27.65/16.92  tff(c_113887, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_113860, c_74])).
% 27.65/16.92  tff(c_114278, plain, (![F_3217, A_3212, B_3216, E_3213, C_3215, D_3214]: (v1_funct_1(k1_tmap_1(A_3212, B_3216, C_3215, D_3214, E_3213, F_3217)) | ~m1_subset_1(F_3217, k1_zfmisc_1(k2_zfmisc_1(D_3214, B_3216))) | ~v1_funct_2(F_3217, D_3214, B_3216) | ~v1_funct_1(F_3217) | ~m1_subset_1(E_3213, k1_zfmisc_1(k2_zfmisc_1(C_3215, B_3216))) | ~v1_funct_2(E_3213, C_3215, B_3216) | ~v1_funct_1(E_3213) | ~m1_subset_1(D_3214, k1_zfmisc_1(A_3212)) | v1_xboole_0(D_3214) | ~m1_subset_1(C_3215, k1_zfmisc_1(A_3212)) | v1_xboole_0(C_3215) | v1_xboole_0(B_3216) | v1_xboole_0(A_3212))), inference(cnfTransformation, [status(thm)], [f_218])).
% 27.65/16.92  tff(c_114282, plain, (![A_3212, C_3215, E_3213]: (v1_funct_1(k1_tmap_1(A_3212, '#skF_3', C_3215, '#skF_5', E_3213, '#skF_7')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_3213, k1_zfmisc_1(k2_zfmisc_1(C_3215, '#skF_3'))) | ~v1_funct_2(E_3213, C_3215, '#skF_3') | ~v1_funct_1(E_3213) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3212)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_3215, k1_zfmisc_1(A_3212)) | v1_xboole_0(C_3215) | v1_xboole_0('#skF_3') | v1_xboole_0(A_3212))), inference(resolution, [status(thm)], [c_68, c_114278])).
% 27.65/16.92  tff(c_114289, plain, (![A_3212, C_3215, E_3213]: (v1_funct_1(k1_tmap_1(A_3212, '#skF_3', C_3215, '#skF_5', E_3213, '#skF_7')) | ~m1_subset_1(E_3213, k1_zfmisc_1(k2_zfmisc_1(C_3215, '#skF_3'))) | ~v1_funct_2(E_3213, C_3215, '#skF_3') | ~v1_funct_1(E_3213) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3212)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_3215, k1_zfmisc_1(A_3212)) | v1_xboole_0(C_3215) | v1_xboole_0('#skF_3') | v1_xboole_0(A_3212))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_114282])).
% 27.65/16.92  tff(c_114572, plain, (![A_3242, C_3243, E_3244]: (v1_funct_1(k1_tmap_1(A_3242, '#skF_3', C_3243, '#skF_5', E_3244, '#skF_7')) | ~m1_subset_1(E_3244, k1_zfmisc_1(k2_zfmisc_1(C_3243, '#skF_3'))) | ~v1_funct_2(E_3244, C_3243, '#skF_3') | ~v1_funct_1(E_3244) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3242)) | ~m1_subset_1(C_3243, k1_zfmisc_1(A_3242)) | v1_xboole_0(C_3243) | v1_xboole_0(A_3242))), inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_114289])).
% 27.65/16.92  tff(c_114577, plain, (![A_3242]: (v1_funct_1(k1_tmap_1(A_3242, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~v1_funct_2('#skF_4', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3242)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3242)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_3242))), inference(resolution, [status(thm)], [c_113887, c_114572])).
% 27.65/16.92  tff(c_114585, plain, (![A_3242]: (v1_funct_1(k1_tmap_1(A_3242, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3242)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3242)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_3242))), inference(demodulation, [status(thm), theory('equality')], [c_113889, c_113888, c_114577])).
% 27.65/16.92  tff(c_114854, plain, (![A_3271]: (v1_funct_1(k1_tmap_1(A_3271, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3271)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3271)) | v1_xboole_0(A_3271))), inference(negUnitSimplification, [status(thm)], [c_88, c_114585])).
% 27.65/16.92  tff(c_114857, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_82, c_114854])).
% 27.65/16.92  tff(c_114860, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_114857])).
% 27.65/16.92  tff(c_114861, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_92, c_114860])).
% 27.65/16.92  tff(c_114518, plain, (![A_3234, F_3239, D_3236, B_3238, C_3237, E_3235]: (m1_subset_1(k1_tmap_1(A_3234, B_3238, C_3237, D_3236, E_3235, F_3239), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_3234, C_3237, D_3236), B_3238))) | ~m1_subset_1(F_3239, k1_zfmisc_1(k2_zfmisc_1(D_3236, B_3238))) | ~v1_funct_2(F_3239, D_3236, B_3238) | ~v1_funct_1(F_3239) | ~m1_subset_1(E_3235, k1_zfmisc_1(k2_zfmisc_1(C_3237, B_3238))) | ~v1_funct_2(E_3235, C_3237, B_3238) | ~v1_funct_1(E_3235) | ~m1_subset_1(D_3236, k1_zfmisc_1(A_3234)) | v1_xboole_0(D_3236) | ~m1_subset_1(C_3237, k1_zfmisc_1(A_3234)) | v1_xboole_0(C_3237) | v1_xboole_0(B_3238) | v1_xboole_0(A_3234))), inference(cnfTransformation, [status(thm)], [f_218])).
% 27.65/16.92  tff(c_127627, plain, (![F_3620, A_3618, D_3622, C_3624, B_3619, D_3621, E_3623]: (k2_partfun1(k4_subset_1(A_3618, C_3624, D_3621), B_3619, k1_tmap_1(A_3618, B_3619, C_3624, D_3621, E_3623, F_3620), D_3622)=k7_relat_1(k1_tmap_1(A_3618, B_3619, C_3624, D_3621, E_3623, F_3620), D_3622) | ~v1_funct_1(k1_tmap_1(A_3618, B_3619, C_3624, D_3621, E_3623, F_3620)) | ~m1_subset_1(F_3620, k1_zfmisc_1(k2_zfmisc_1(D_3621, B_3619))) | ~v1_funct_2(F_3620, D_3621, B_3619) | ~v1_funct_1(F_3620) | ~m1_subset_1(E_3623, k1_zfmisc_1(k2_zfmisc_1(C_3624, B_3619))) | ~v1_funct_2(E_3623, C_3624, B_3619) | ~v1_funct_1(E_3623) | ~m1_subset_1(D_3621, k1_zfmisc_1(A_3618)) | v1_xboole_0(D_3621) | ~m1_subset_1(C_3624, k1_zfmisc_1(A_3618)) | v1_xboole_0(C_3624) | v1_xboole_0(B_3619) | v1_xboole_0(A_3618))), inference(resolution, [status(thm)], [c_114518, c_52])).
% 27.65/16.92  tff(c_127633, plain, (![A_3618, C_3624, E_3623, D_3622]: (k2_partfun1(k4_subset_1(A_3618, C_3624, '#skF_5'), '#skF_3', k1_tmap_1(A_3618, '#skF_3', C_3624, '#skF_5', E_3623, '#skF_7'), D_3622)=k7_relat_1(k1_tmap_1(A_3618, '#skF_3', C_3624, '#skF_5', E_3623, '#skF_7'), D_3622) | ~v1_funct_1(k1_tmap_1(A_3618, '#skF_3', C_3624, '#skF_5', E_3623, '#skF_7')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_3623, k1_zfmisc_1(k2_zfmisc_1(C_3624, '#skF_3'))) | ~v1_funct_2(E_3623, C_3624, '#skF_3') | ~v1_funct_1(E_3623) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3618)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_3624, k1_zfmisc_1(A_3618)) | v1_xboole_0(C_3624) | v1_xboole_0('#skF_3') | v1_xboole_0(A_3618))), inference(resolution, [status(thm)], [c_68, c_127627])).
% 27.65/16.92  tff(c_127641, plain, (![A_3618, C_3624, E_3623, D_3622]: (k2_partfun1(k4_subset_1(A_3618, C_3624, '#skF_5'), '#skF_3', k1_tmap_1(A_3618, '#skF_3', C_3624, '#skF_5', E_3623, '#skF_7'), D_3622)=k7_relat_1(k1_tmap_1(A_3618, '#skF_3', C_3624, '#skF_5', E_3623, '#skF_7'), D_3622) | ~v1_funct_1(k1_tmap_1(A_3618, '#skF_3', C_3624, '#skF_5', E_3623, '#skF_7')) | ~m1_subset_1(E_3623, k1_zfmisc_1(k2_zfmisc_1(C_3624, '#skF_3'))) | ~v1_funct_2(E_3623, C_3624, '#skF_3') | ~v1_funct_1(E_3623) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3618)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_3624, k1_zfmisc_1(A_3618)) | v1_xboole_0(C_3624) | v1_xboole_0('#skF_3') | v1_xboole_0(A_3618))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_127633])).
% 27.65/16.92  tff(c_129779, plain, (![A_3683, C_3684, E_3685, D_3686]: (k2_partfun1(k4_subset_1(A_3683, C_3684, '#skF_5'), '#skF_3', k1_tmap_1(A_3683, '#skF_3', C_3684, '#skF_5', E_3685, '#skF_7'), D_3686)=k7_relat_1(k1_tmap_1(A_3683, '#skF_3', C_3684, '#skF_5', E_3685, '#skF_7'), D_3686) | ~v1_funct_1(k1_tmap_1(A_3683, '#skF_3', C_3684, '#skF_5', E_3685, '#skF_7')) | ~m1_subset_1(E_3685, k1_zfmisc_1(k2_zfmisc_1(C_3684, '#skF_3'))) | ~v1_funct_2(E_3685, C_3684, '#skF_3') | ~v1_funct_1(E_3685) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3683)) | ~m1_subset_1(C_3684, k1_zfmisc_1(A_3683)) | v1_xboole_0(C_3684) | v1_xboole_0(A_3683))), inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_127641])).
% 27.65/16.92  tff(c_129784, plain, (![A_3683, D_3686]: (k2_partfun1(k4_subset_1(A_3683, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_3683, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), D_3686)=k7_relat_1(k1_tmap_1(A_3683, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), D_3686) | ~v1_funct_1(k1_tmap_1(A_3683, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~v1_funct_2('#skF_4', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3683)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3683)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_3683))), inference(resolution, [status(thm)], [c_113887, c_129779])).
% 27.65/16.92  tff(c_129792, plain, (![A_3683, D_3686]: (k2_partfun1(k4_subset_1(A_3683, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_3683, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), D_3686)=k7_relat_1(k1_tmap_1(A_3683, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), D_3686) | ~v1_funct_1(k1_tmap_1(A_3683, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3683)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3683)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_3683))), inference(demodulation, [status(thm), theory('equality')], [c_113889, c_113888, c_129784])).
% 27.65/16.92  tff(c_131306, plain, (![A_3705, D_3706]: (k2_partfun1(k4_subset_1(A_3705, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_3705, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), D_3706)=k7_relat_1(k1_tmap_1(A_3705, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), D_3706) | ~v1_funct_1(k1_tmap_1(A_3705, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3705)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3705)) | v1_xboole_0(A_3705))), inference(negUnitSimplification, [status(thm)], [c_88, c_129792])).
% 27.65/16.92  tff(c_113863, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_113860, c_113860, c_64481])).
% 27.65/16.92  tff(c_131315, plain, (k7_relat_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), '#skF_4')!='#skF_4' | ~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_131306, c_113863])).
% 27.65/16.92  tff(c_131333, plain, (k7_relat_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), '#skF_4')!='#skF_4' | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_114861, c_131315])).
% 27.65/16.92  tff(c_131334, plain, (k7_relat_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), '#skF_4')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_92, c_131333])).
% 27.65/16.92  tff(c_34, plain, (![C_27, A_25, B_26]: (v1_relat_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 27.65/16.92  tff(c_126097, plain, (![D_3557, B_3555, F_3556, C_3559, E_3558, A_3554]: (v1_relat_1(k1_tmap_1(A_3554, B_3555, C_3559, D_3557, E_3558, F_3556)) | ~m1_subset_1(F_3556, k1_zfmisc_1(k2_zfmisc_1(D_3557, B_3555))) | ~v1_funct_2(F_3556, D_3557, B_3555) | ~v1_funct_1(F_3556) | ~m1_subset_1(E_3558, k1_zfmisc_1(k2_zfmisc_1(C_3559, B_3555))) | ~v1_funct_2(E_3558, C_3559, B_3555) | ~v1_funct_1(E_3558) | ~m1_subset_1(D_3557, k1_zfmisc_1(A_3554)) | v1_xboole_0(D_3557) | ~m1_subset_1(C_3559, k1_zfmisc_1(A_3554)) | v1_xboole_0(C_3559) | v1_xboole_0(B_3555) | v1_xboole_0(A_3554))), inference(resolution, [status(thm)], [c_114518, c_34])).
% 27.65/16.92  tff(c_126103, plain, (![A_3554, C_3559, E_3558]: (v1_relat_1(k1_tmap_1(A_3554, '#skF_3', C_3559, '#skF_5', E_3558, '#skF_7')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_3558, k1_zfmisc_1(k2_zfmisc_1(C_3559, '#skF_3'))) | ~v1_funct_2(E_3558, C_3559, '#skF_3') | ~v1_funct_1(E_3558) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3554)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_3559, k1_zfmisc_1(A_3554)) | v1_xboole_0(C_3559) | v1_xboole_0('#skF_3') | v1_xboole_0(A_3554))), inference(resolution, [status(thm)], [c_68, c_126097])).
% 27.65/16.92  tff(c_126111, plain, (![A_3554, C_3559, E_3558]: (v1_relat_1(k1_tmap_1(A_3554, '#skF_3', C_3559, '#skF_5', E_3558, '#skF_7')) | ~m1_subset_1(E_3558, k1_zfmisc_1(k2_zfmisc_1(C_3559, '#skF_3'))) | ~v1_funct_2(E_3558, C_3559, '#skF_3') | ~v1_funct_1(E_3558) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3554)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_3559, k1_zfmisc_1(A_3554)) | v1_xboole_0(C_3559) | v1_xboole_0('#skF_3') | v1_xboole_0(A_3554))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_126103])).
% 27.65/16.92  tff(c_126122, plain, (![A_3560, C_3561, E_3562]: (v1_relat_1(k1_tmap_1(A_3560, '#skF_3', C_3561, '#skF_5', E_3562, '#skF_7')) | ~m1_subset_1(E_3562, k1_zfmisc_1(k2_zfmisc_1(C_3561, '#skF_3'))) | ~v1_funct_2(E_3562, C_3561, '#skF_3') | ~v1_funct_1(E_3562) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3560)) | ~m1_subset_1(C_3561, k1_zfmisc_1(A_3560)) | v1_xboole_0(C_3561) | v1_xboole_0(A_3560))), inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_126111])).
% 27.65/16.92  tff(c_126127, plain, (![A_3560]: (v1_relat_1(k1_tmap_1(A_3560, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~v1_funct_2('#skF_4', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3560)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3560)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_3560))), inference(resolution, [status(thm)], [c_113887, c_126122])).
% 27.65/16.92  tff(c_126135, plain, (![A_3560]: (v1_relat_1(k1_tmap_1(A_3560, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3560)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3560)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_3560))), inference(demodulation, [status(thm), theory('equality')], [c_113889, c_113888, c_126127])).
% 27.65/16.92  tff(c_126675, plain, (![A_3586]: (v1_relat_1(k1_tmap_1(A_3586, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3586)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3586)) | v1_xboole_0(A_3586))), inference(negUnitSimplification, [status(thm)], [c_88, c_126135])).
% 27.65/16.92  tff(c_126678, plain, (v1_relat_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_82, c_126675])).
% 27.65/16.92  tff(c_126681, plain, (v1_relat_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_126678])).
% 27.65/16.92  tff(c_126682, plain, (v1_relat_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_92, c_126681])).
% 27.65/16.92  tff(c_18, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 27.65/16.92  tff(c_111814, plain, (k2_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_111792, c_111792, c_18])).
% 27.65/16.92  tff(c_113883, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_113860, c_113860, c_111814])).
% 27.65/16.92  tff(c_113884, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_113860, c_113860, c_111820])).
% 27.65/16.92  tff(c_28, plain, (![A_22]: (k7_relat_1(A_22, k1_relat_1(A_22))=A_22 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_78])).
% 27.65/16.92  tff(c_113885, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_113860, c_111792])).
% 27.65/16.92  tff(c_6901, plain, (![A_799]: (k1_relat_1(A_799)!=k1_xboole_0 | k1_xboole_0=A_799 | ~v1_relat_1(A_799))), inference(cnfTransformation, [status(thm)], [f_70])).
% 27.65/16.92  tff(c_6912, plain, (![A_11, B_12]: (k1_relat_1(k7_relat_1(A_11, B_12))!=k1_xboole_0 | k7_relat_1(A_11, B_12)=k1_xboole_0 | ~v1_relat_1(A_11))), inference(resolution, [status(thm)], [c_12, c_6901])).
% 27.65/16.92  tff(c_114653, plain, (![A_3248, B_3249]: (k1_relat_1(k7_relat_1(A_3248, B_3249))!='#skF_4' | k7_relat_1(A_3248, B_3249)='#skF_4' | ~v1_relat_1(A_3248))), inference(demodulation, [status(thm), theory('equality')], [c_113885, c_113885, c_6912])).
% 27.65/16.92  tff(c_115056, plain, (![A_3283]: (k1_relat_1(A_3283)!='#skF_4' | k7_relat_1(A_3283, k1_relat_1(A_3283))='#skF_4' | ~v1_relat_1(A_3283) | ~v1_relat_1(A_3283))), inference(superposition, [status(thm), theory('equality')], [c_28, c_114653])).
% 27.65/16.92  tff(c_114652, plain, (![A_11, B_12]: (k1_relat_1(k7_relat_1(A_11, B_12))!='#skF_4' | k7_relat_1(A_11, B_12)='#skF_4' | ~v1_relat_1(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_113885, c_113885, c_6912])).
% 27.65/16.92  tff(c_115065, plain, (![A_3283]: (k1_relat_1('#skF_4')!='#skF_4' | k7_relat_1(A_3283, k1_relat_1(A_3283))='#skF_4' | ~v1_relat_1(A_3283) | k1_relat_1(A_3283)!='#skF_4' | ~v1_relat_1(A_3283) | ~v1_relat_1(A_3283))), inference(superposition, [status(thm), theory('equality')], [c_115056, c_114652])).
% 27.65/16.92  tff(c_115123, plain, (![A_3283]: (k7_relat_1(A_3283, k1_relat_1(A_3283))='#skF_4' | k1_relat_1(A_3283)!='#skF_4' | ~v1_relat_1(A_3283))), inference(demodulation, [status(thm), theory('equality')], [c_113884, c_115065])).
% 27.65/16.92  tff(c_111809, plain, (k7_relat_1('#skF_6', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_111792, c_111792, c_111792, c_6880])).
% 27.65/16.92  tff(c_113879, plain, (k7_relat_1('#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_113860, c_113860, c_113860, c_111809])).
% 27.65/16.92  tff(c_6913, plain, (![A_800]: (k2_relat_1(A_800)!=k1_xboole_0 | k1_xboole_0=A_800 | ~v1_relat_1(A_800))), inference(cnfTransformation, [status(thm)], [f_70])).
% 27.65/16.92  tff(c_6924, plain, (![A_11, B_12]: (k2_relat_1(k7_relat_1(A_11, B_12))!=k1_xboole_0 | k7_relat_1(A_11, B_12)=k1_xboole_0 | ~v1_relat_1(A_11))), inference(resolution, [status(thm)], [c_12, c_6913])).
% 27.65/16.92  tff(c_114615, plain, (![A_3246, B_3247]: (k2_relat_1(k7_relat_1(A_3246, B_3247))!='#skF_4' | k7_relat_1(A_3246, B_3247)='#skF_4' | ~v1_relat_1(A_3246))), inference(demodulation, [status(thm), theory('equality')], [c_113885, c_113885, c_6924])).
% 27.65/16.92  tff(c_114866, plain, (![A_3277]: (k2_relat_1(A_3277)!='#skF_4' | k7_relat_1(A_3277, k1_relat_1(A_3277))='#skF_4' | ~v1_relat_1(A_3277) | ~v1_relat_1(A_3277))), inference(superposition, [status(thm), theory('equality')], [c_28, c_114615])).
% 27.65/16.92  tff(c_114872, plain, (![A_3277]: (k1_relat_1('#skF_4')!='#skF_4' | k7_relat_1(A_3277, k1_relat_1(A_3277))='#skF_4' | ~v1_relat_1(A_3277) | k2_relat_1(A_3277)!='#skF_4' | ~v1_relat_1(A_3277) | ~v1_relat_1(A_3277))), inference(superposition, [status(thm), theory('equality')], [c_114866, c_114652])).
% 27.65/16.92  tff(c_114946, plain, (![A_3278]: (k7_relat_1(A_3278, k1_relat_1(A_3278))='#skF_4' | k2_relat_1(A_3278)!='#skF_4' | ~v1_relat_1(A_3278))), inference(demodulation, [status(thm), theory('equality')], [c_113884, c_114872])).
% 27.65/16.92  tff(c_114973, plain, (![A_3278]: (r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(A_3278)) | ~v1_relat_1(A_3278) | k2_relat_1(A_3278)!='#skF_4' | ~v1_relat_1(A_3278))), inference(superposition, [status(thm), theory('equality')], [c_114946, c_26])).
% 27.65/16.92  tff(c_115014, plain, (![A_3278]: (r1_tarski('#skF_4', k1_relat_1(A_3278)) | ~v1_relat_1(A_3278) | k2_relat_1(A_3278)!='#skF_4' | ~v1_relat_1(A_3278))), inference(demodulation, [status(thm), theory('equality')], [c_113884, c_114973])).
% 27.65/16.92  tff(c_130477, plain, (![A_3700, A_3701]: (k7_relat_1(A_3700, A_3701)=k7_relat_1('#skF_4', A_3701) | ~r1_tarski(A_3701, k1_relat_1(A_3700)) | ~v1_relat_1(A_3700) | k2_relat_1(A_3700)!='#skF_4' | ~v1_relat_1(A_3700))), inference(superposition, [status(thm), theory('equality')], [c_114946, c_14])).
% 27.65/16.92  tff(c_130530, plain, (![A_3278]: (k7_relat_1(A_3278, '#skF_4')=k7_relat_1('#skF_4', '#skF_4') | k2_relat_1(A_3278)!='#skF_4' | ~v1_relat_1(A_3278))), inference(resolution, [status(thm)], [c_115014, c_130477])).
% 27.65/16.92  tff(c_130588, plain, (![A_3702]: (k7_relat_1(A_3702, '#skF_4')='#skF_4' | k2_relat_1(A_3702)!='#skF_4' | ~v1_relat_1(A_3702))), inference(demodulation, [status(thm), theory('equality')], [c_113879, c_130530])).
% 27.65/16.92  tff(c_131873, plain, (![A_3715, B_3716]: (k7_relat_1(k7_relat_1(A_3715, B_3716), '#skF_4')='#skF_4' | k2_relat_1(k7_relat_1(A_3715, B_3716))!='#skF_4' | ~v1_relat_1(A_3715))), inference(resolution, [status(thm)], [c_12, c_130588])).
% 27.65/16.92  tff(c_132568, plain, (![A_3721]: (k7_relat_1(A_3721, '#skF_4')='#skF_4' | k2_relat_1(k7_relat_1(A_3721, k1_relat_1(A_3721)))!='#skF_4' | ~v1_relat_1(A_3721) | ~v1_relat_1(A_3721))), inference(superposition, [status(thm), theory('equality')], [c_28, c_131873])).
% 27.65/16.92  tff(c_132602, plain, (![A_3283]: (k7_relat_1(A_3283, '#skF_4')='#skF_4' | k2_relat_1('#skF_4')!='#skF_4' | ~v1_relat_1(A_3283) | ~v1_relat_1(A_3283) | k1_relat_1(A_3283)!='#skF_4' | ~v1_relat_1(A_3283))), inference(superposition, [status(thm), theory('equality')], [c_115123, c_132568])).
% 27.65/16.92  tff(c_132645, plain, (![A_3722]: (k7_relat_1(A_3722, '#skF_4')='#skF_4' | k1_relat_1(A_3722)!='#skF_4' | ~v1_relat_1(A_3722))), inference(demodulation, [status(thm), theory('equality')], [c_113883, c_132602])).
% 27.65/16.92  tff(c_132687, plain, (k7_relat_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), '#skF_4')='#skF_4' | k1_relat_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'))!='#skF_4'), inference(resolution, [status(thm)], [c_126682, c_132645])).
% 27.65/16.92  tff(c_132736, plain, (k1_relat_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'))!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_131334, c_132687])).
% 27.65/16.92  tff(c_111812, plain, (![A_31]: (r1_xboole_0('#skF_1'(A_31), A_31) | A_31='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_111792, c_40])).
% 27.65/16.92  tff(c_113876, plain, (![A_31]: (r1_xboole_0('#skF_1'(A_31), A_31) | A_31='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_113860, c_111812])).
% 27.65/16.92  tff(c_112966, plain, (![A_16, B_18]: (k7_relat_1(A_16, B_18)='#skF_6' | ~r1_xboole_0(B_18, k1_relat_1(A_16)) | ~v1_relat_1(A_16))), inference(demodulation, [status(thm), theory('equality')], [c_111792, c_16])).
% 27.65/16.92  tff(c_114367, plain, (![A_3223, B_3224]: (k7_relat_1(A_3223, B_3224)='#skF_4' | ~r1_xboole_0(B_3224, k1_relat_1(A_3223)) | ~v1_relat_1(A_3223))), inference(demodulation, [status(thm), theory('equality')], [c_113860, c_112966])).
% 27.65/16.92  tff(c_114769, plain, (![A_3264]: (k7_relat_1(A_3264, '#skF_1'(k1_relat_1(A_3264)))='#skF_4' | ~v1_relat_1(A_3264) | k1_relat_1(A_3264)='#skF_4')), inference(resolution, [status(thm)], [c_113876, c_114367])).
% 27.65/16.92  tff(c_114796, plain, (![A_3264]: (r1_tarski(k1_relat_1('#skF_4'), '#skF_1'(k1_relat_1(A_3264))) | ~v1_relat_1(A_3264) | ~v1_relat_1(A_3264) | k1_relat_1(A_3264)='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_114769, c_26])).
% 27.65/16.92  tff(c_114833, plain, (![A_3264]: (r1_tarski('#skF_4', '#skF_1'(k1_relat_1(A_3264))) | ~v1_relat_1(A_3264) | ~v1_relat_1(A_3264) | k1_relat_1(A_3264)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_113884, c_114796])).
% 27.65/16.92  tff(c_114387, plain, (![A_3223]: (k7_relat_1(A_3223, '#skF_1'(k1_relat_1(A_3223)))='#skF_4' | ~v1_relat_1(A_3223) | k1_relat_1(A_3223)='#skF_4')), inference(resolution, [status(thm)], [c_113876, c_114367])).
% 27.65/16.92  tff(c_134191, plain, (![A_3748, B_3749]: (k7_relat_1(A_3748, '#skF_4')='#skF_4' | ~r1_tarski('#skF_4', B_3749) | ~v1_relat_1(A_3748) | k2_relat_1(k7_relat_1(A_3748, B_3749))!='#skF_4' | ~v1_relat_1(A_3748))), inference(superposition, [status(thm), theory('equality')], [c_131873, c_14])).
% 27.65/16.92  tff(c_134269, plain, (![A_3223]: (k7_relat_1(A_3223, '#skF_4')='#skF_4' | ~r1_tarski('#skF_4', '#skF_1'(k1_relat_1(A_3223))) | ~v1_relat_1(A_3223) | k2_relat_1('#skF_4')!='#skF_4' | ~v1_relat_1(A_3223) | ~v1_relat_1(A_3223) | k1_relat_1(A_3223)='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_114387, c_134191])).
% 27.65/16.92  tff(c_134562, plain, (![A_3766]: (k7_relat_1(A_3766, '#skF_4')='#skF_4' | ~r1_tarski('#skF_4', '#skF_1'(k1_relat_1(A_3766))) | ~v1_relat_1(A_3766) | k1_relat_1(A_3766)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_113883, c_134269])).
% 27.65/16.92  tff(c_134602, plain, (![A_3773]: (k7_relat_1(A_3773, '#skF_4')='#skF_4' | ~v1_relat_1(A_3773) | k1_relat_1(A_3773)='#skF_4')), inference(resolution, [status(thm)], [c_114833, c_134562])).
% 27.65/16.92  tff(c_134650, plain, (k7_relat_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), '#skF_4')='#skF_4' | k1_relat_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'))='#skF_4'), inference(resolution, [status(thm)], [c_126682, c_134602])).
% 27.65/16.92  tff(c_134704, plain, $false, inference(negUnitSimplification, [status(thm)], [c_132736, c_131334, c_134650])).
% 27.65/16.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.65/16.92  
% 27.65/16.92  Inference rules
% 27.65/16.92  ----------------------
% 27.65/16.92  #Ref     : 0
% 27.65/16.92  #Sup     : 29202
% 27.65/16.92  #Fact    : 0
% 27.65/16.92  #Define  : 0
% 27.65/16.92  #Split   : 173
% 27.65/16.92  #Chain   : 0
% 27.65/16.92  #Close   : 0
% 27.65/16.92  
% 27.65/16.92  Ordering : KBO
% 27.65/16.92  
% 27.65/16.92  Simplification rules
% 27.65/16.92  ----------------------
% 27.65/16.92  #Subsume      : 5864
% 27.65/16.92  #Demod        : 55837
% 27.65/16.92  #Tautology    : 12973
% 27.65/16.92  #SimpNegUnit  : 1041
% 27.65/16.92  #BackRed      : 295
% 27.65/16.92  
% 27.65/16.92  #Partial instantiations: 0
% 27.65/16.92  #Strategies tried      : 1
% 27.65/16.92  
% 27.65/16.92  Timing (in seconds)
% 27.65/16.92  ----------------------
% 27.65/16.92  Preprocessing        : 0.44
% 27.65/16.92  Parsing              : 0.21
% 27.65/16.92  CNF conversion       : 0.06
% 27.65/16.92  Main loop            : 15.58
% 27.65/16.92  Inferencing          : 3.26
% 27.65/16.92  Reduction            : 6.49
% 27.65/16.92  Demodulation         : 5.08
% 27.65/16.92  BG Simplification    : 0.36
% 27.65/16.92  Subsumption          : 4.76
% 27.65/16.92  Abstraction          : 0.52
% 27.65/16.92  MUC search           : 0.00
% 27.65/16.92  Cooper               : 0.00
% 27.65/16.92  Total                : 16.18
% 27.65/16.92  Index Insertion      : 0.00
% 27.65/16.92  Index Deletion       : 0.00
% 27.65/16.92  Index Matching       : 0.00
% 27.65/16.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
