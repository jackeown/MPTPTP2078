%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:10 EST 2020

% Result     : Theorem 26.90s
% Output     : CNFRefutation 27.55s
% Verified   : 
% Statistics : Number of formulae       :  597 (8216 expanded)
%              Number of leaves         :   58 (2716 expanded)
%              Depth                    :   24
%              Number of atoms          : 1534 (30731 expanded)
%              Number of equality atoms :  451 (7690 expanded)
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

tff(f_282,negated_conjecture,(
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

tff(f_114,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_86,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_100,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_152,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_144,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_130,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_240,axiom,(
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

tff(f_96,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

tff(f_110,axiom,(
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

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_158,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_206,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(c_98,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_282])).

tff(c_100,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_282])).

tff(c_84,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_282])).

tff(c_73633,plain,(
    ! [C_1870,A_1871,B_1872] :
      ( v1_relat_1(C_1870)
      | ~ m1_subset_1(C_1870,k1_zfmisc_1(k2_zfmisc_1(A_1871,B_1872))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_73641,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_84,c_73633])).

tff(c_78,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_282])).

tff(c_9292,plain,(
    ! [C_798,A_799,B_800] :
      ( v1_relat_1(C_798)
      | ~ m1_subset_1(C_798,k1_zfmisc_1(k2_zfmisc_1(A_799,B_800))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_9299,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_78,c_9292])).

tff(c_30,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_114,plain,(
    ! [A_244] :
      ( k7_relat_1(A_244,k1_relat_1(A_244)) = A_244
      | ~ v1_relat_1(A_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_126,plain,
    ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_114])).

tff(c_9239,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_9372,plain,(
    ! [C_813,A_814,B_815] :
      ( v4_relat_1(C_813,A_814)
      | ~ m1_subset_1(C_813,k1_zfmisc_1(k2_zfmisc_1(A_814,B_815))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_9379,plain,(
    v4_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_9372])).

tff(c_9535,plain,(
    ! [B_831,A_832] :
      ( k1_relat_1(B_831) = A_832
      | ~ v1_partfun1(B_831,A_832)
      | ~ v4_relat_1(B_831,A_832)
      | ~ v1_relat_1(B_831) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_9541,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_9379,c_9535])).

tff(c_9547,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9299,c_9541])).

tff(c_9549,plain,(
    ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_9547])).

tff(c_82,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_282])).

tff(c_80,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_282])).

tff(c_9831,plain,(
    ! [C_863,A_864,B_865] :
      ( v1_partfun1(C_863,A_864)
      | ~ v1_funct_2(C_863,A_864,B_865)
      | ~ v1_funct_1(C_863)
      | ~ m1_subset_1(C_863,k1_zfmisc_1(k2_zfmisc_1(A_864,B_865)))
      | v1_xboole_0(B_865) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_9834,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_9831])).

tff(c_9840,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_9834])).

tff(c_9842,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_9549,c_9840])).

tff(c_9843,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_9547])).

tff(c_9316,plain,(
    ! [A_802] :
      ( k1_relat_1(A_802) = k1_xboole_0
      | k2_relat_1(A_802) != k1_xboole_0
      | ~ v1_relat_1(A_802) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_9327,plain,
    ( k1_relat_1('#skF_7') = k1_xboole_0
    | k2_relat_1('#skF_7') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9299,c_9316])).

tff(c_9334,plain,(
    k2_relat_1('#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_9327])).

tff(c_9345,plain,(
    ! [A_807] :
      ( k2_relat_1(A_807) = k1_xboole_0
      | k1_relat_1(A_807) != k1_xboole_0
      | ~ v1_relat_1(A_807) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_9351,plain,
    ( k2_relat_1('#skF_7') = k1_xboole_0
    | k1_relat_1('#skF_7') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9299,c_9345])).

tff(c_9360,plain,(
    k1_relat_1('#skF_7') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_9334,c_9351])).

tff(c_9847,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9843,c_9360])).

tff(c_50,plain,(
    ! [A_38] :
      ( r1_xboole_0('#skF_1'(A_38),A_38)
      | k1_xboole_0 = A_38 ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_24,plain,(
    ! [A_21,B_23] :
      ( k7_relat_1(A_21,B_23) = k1_xboole_0
      | ~ r1_xboole_0(B_23,k1_relat_1(A_21))
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_9866,plain,(
    ! [B_23] :
      ( k7_relat_1('#skF_7',B_23) = k1_xboole_0
      | ~ r1_xboole_0(B_23,'#skF_5')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9843,c_24])).

tff(c_9968,plain,(
    ! [B_873] :
      ( k7_relat_1('#skF_7',B_873) = k1_xboole_0
      | ~ r1_xboole_0(B_873,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9299,c_9866])).

tff(c_9988,plain,
    ( k7_relat_1('#skF_7','#skF_1'('#skF_5')) = k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_50,c_9968])).

tff(c_9998,plain,(
    k7_relat_1('#skF_7','#skF_1'('#skF_5')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_9847,c_9988])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( v1_relat_1(k7_relat_1(A_13,B_14))
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10005,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_9998,c_14])).

tff(c_10011,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9299,c_10005])).

tff(c_10013,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9239,c_10011])).

tff(c_10015,plain,(
    k2_relat_1('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_9327])).

tff(c_10014,plain,(
    k1_relat_1('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_9327])).

tff(c_18,plain,(
    ! [A_18] :
      ( k9_relat_1(A_18,k1_relat_1(A_18)) = k2_relat_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_10019,plain,
    ( k9_relat_1('#skF_7',k1_xboole_0) = k2_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_10014,c_18])).

tff(c_10026,plain,(
    k9_relat_1('#skF_7',k1_xboole_0) = k2_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9299,c_10019])).

tff(c_10057,plain,(
    k9_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10015,c_10026])).

tff(c_38,plain,(
    ! [A_29] :
      ( k7_relat_1(A_29,k1_relat_1(A_29)) = A_29
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_10022,plain,
    ( k7_relat_1('#skF_7',k1_xboole_0) = '#skF_7'
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_10014,c_38])).

tff(c_10028,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9299,c_10022])).

tff(c_10348,plain,(
    ! [B_903,A_904] :
      ( r1_xboole_0(k1_relat_1(B_903),A_904)
      | k9_relat_1(B_903,A_904) != k1_xboole_0
      | ~ v1_relat_1(B_903) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10360,plain,(
    ! [A_904] :
      ( r1_xboole_0(k1_xboole_0,A_904)
      | k9_relat_1('#skF_7',A_904) != k1_xboole_0
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10014,c_10348])).

tff(c_10368,plain,(
    ! [A_904] :
      ( r1_xboole_0(k1_xboole_0,A_904)
      | k9_relat_1('#skF_7',A_904) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9299,c_10360])).

tff(c_10425,plain,(
    ! [A_911,B_912] :
      ( k7_relat_1(A_911,B_912) = k1_xboole_0
      | ~ r1_xboole_0(B_912,k1_relat_1(A_911))
      | ~ v1_relat_1(A_911) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_10436,plain,(
    ! [B_912] :
      ( k7_relat_1('#skF_7',B_912) = k1_xboole_0
      | ~ r1_xboole_0(B_912,k1_xboole_0)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10014,c_10425])).

tff(c_10454,plain,(
    ! [B_913] :
      ( k7_relat_1('#skF_7',B_913) = k1_xboole_0
      | ~ r1_xboole_0(B_913,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9299,c_10436])).

tff(c_10458,plain,
    ( k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0
    | k9_relat_1('#skF_7',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10368,c_10454])).

tff(c_10473,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10057,c_10028,c_10458])).

tff(c_10505,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10473,c_9239])).

tff(c_10512,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9299,c_10505])).

tff(c_10514,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_28,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_127995,plain,(
    ! [A_2699] :
      ( k9_relat_1(A_2699,k1_relat_1(A_2699)) = k2_relat_1(A_2699)
      | ~ v1_relat_1(A_2699) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_128004,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_127995])).

tff(c_128008,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10514,c_28,c_128004])).

tff(c_102,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_282])).

tff(c_94,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_282])).

tff(c_96,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_282])).

tff(c_92,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_282])).

tff(c_88,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_282])).

tff(c_86,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_282])).

tff(c_72,plain,(
    ! [E_181,B_178,A_177,D_180,C_179,F_182] :
      ( v1_funct_2(k1_tmap_1(A_177,B_178,C_179,D_180,E_181,F_182),k4_subset_1(A_177,C_179,D_180),B_178)
      | ~ m1_subset_1(F_182,k1_zfmisc_1(k2_zfmisc_1(D_180,B_178)))
      | ~ v1_funct_2(F_182,D_180,B_178)
      | ~ v1_funct_1(F_182)
      | ~ m1_subset_1(E_181,k1_zfmisc_1(k2_zfmisc_1(C_179,B_178)))
      | ~ v1_funct_2(E_181,C_179,B_178)
      | ~ v1_funct_1(E_181)
      | ~ m1_subset_1(D_180,k1_zfmisc_1(A_177))
      | v1_xboole_0(D_180)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(A_177))
      | v1_xboole_0(C_179)
      | v1_xboole_0(B_178)
      | v1_xboole_0(A_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_10599,plain,(
    ! [C_926,A_927,B_928] :
      ( v1_relat_1(C_926)
      | ~ m1_subset_1(C_926,k1_zfmisc_1(k2_zfmisc_1(A_927,B_928))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_10607,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_84,c_10599])).

tff(c_10513,plain,(
    k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_10668,plain,(
    ! [C_933,A_934,B_935] :
      ( v4_relat_1(C_933,A_934)
      | ~ m1_subset_1(C_933,k1_zfmisc_1(k2_zfmisc_1(A_934,B_935))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_10676,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_10668])).

tff(c_11027,plain,(
    ! [B_963,A_964] :
      ( k1_relat_1(B_963) = A_964
      | ~ v1_partfun1(B_963,A_964)
      | ~ v4_relat_1(B_963,A_964)
      | ~ v1_relat_1(B_963) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_11030,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_10676,c_11027])).

tff(c_11036,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10607,c_11030])).

tff(c_11040,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_11036])).

tff(c_11965,plain,(
    ! [C_1028,A_1029,B_1030] :
      ( v1_partfun1(C_1028,A_1029)
      | ~ v1_funct_2(C_1028,A_1029,B_1030)
      | ~ v1_funct_1(C_1028)
      | ~ m1_subset_1(C_1028,k1_zfmisc_1(k2_zfmisc_1(A_1029,B_1030)))
      | v1_xboole_0(B_1030) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_11971,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_11965])).

tff(c_11978,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_11971])).

tff(c_11980,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_11040,c_11978])).

tff(c_11981,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_11036])).

tff(c_32,plain,(
    ! [A_26] :
      ( k1_relat_1(A_26) = k1_xboole_0
      | k2_relat_1(A_26) != k1_xboole_0
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_10629,plain,
    ( k1_relat_1('#skF_6') = k1_xboole_0
    | k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10607,c_32])).

tff(c_10635,plain,(
    k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_10629])).

tff(c_10636,plain,(
    ! [A_930] :
      ( k2_relat_1(A_930) = k1_xboole_0
      | k1_relat_1(A_930) != k1_xboole_0
      | ~ v1_relat_1(A_930) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_10639,plain,
    ( k2_relat_1('#skF_6') = k1_xboole_0
    | k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10607,c_10636])).

tff(c_10651,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_10635,c_10639])).

tff(c_11985,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11981,c_10651])).

tff(c_12001,plain,(
    ! [B_23] :
      ( k7_relat_1('#skF_6',B_23) = k1_xboole_0
      | ~ r1_xboole_0(B_23,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11981,c_24])).

tff(c_12602,plain,(
    ! [B_1067] :
      ( k7_relat_1('#skF_6',B_1067) = k1_xboole_0
      | ~ r1_xboole_0(B_1067,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10607,c_12001])).

tff(c_12622,plain,
    ( k7_relat_1('#skF_6','#skF_1'('#skF_4')) = k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50,c_12602])).

tff(c_12631,plain,(
    k7_relat_1('#skF_6','#skF_1'('#skF_4')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_11985,c_12622])).

tff(c_36,plain,(
    ! [B_28,A_27] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_28,A_27)),A_27)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_12638,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),'#skF_1'('#skF_4'))
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_12631,c_36])).

tff(c_12647,plain,(
    r1_tarski(k1_xboole_0,'#skF_1'('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10607,c_30,c_12638])).

tff(c_16,plain,(
    ! [C_17,B_16,A_15] :
      ( k7_relat_1(k7_relat_1(C_17,B_16),A_15) = k7_relat_1(C_17,A_15)
      | ~ r1_tarski(A_15,B_16)
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_12635,plain,(
    ! [A_15] :
      ( k7_relat_1(k1_xboole_0,A_15) = k7_relat_1('#skF_6',A_15)
      | ~ r1_tarski(A_15,'#skF_1'('#skF_4'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12631,c_16])).

tff(c_13666,plain,(
    ! [A_1150] :
      ( k7_relat_1(k1_xboole_0,A_1150) = k7_relat_1('#skF_6',A_1150)
      | ~ r1_tarski(A_1150,'#skF_1'('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10607,c_12635])).

tff(c_13677,plain,(
    k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12647,c_13666])).

tff(c_13691,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10513,c_13677])).

tff(c_22,plain,(
    ! [B_20,A_19] :
      ( r1_xboole_0(k1_relat_1(B_20),A_19)
      | k9_relat_1(B_20,A_19) != k1_xboole_0
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_12004,plain,(
    ! [A_19] :
      ( r1_xboole_0('#skF_4',A_19)
      | k9_relat_1('#skF_6',A_19) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11981,c_22])).

tff(c_12024,plain,(
    ! [A_19] :
      ( r1_xboole_0('#skF_4',A_19)
      | k9_relat_1('#skF_6',A_19) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10607,c_12004])).

tff(c_10606,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_78,c_10599])).

tff(c_10675,plain,(
    v4_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_10668])).

tff(c_11033,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_10675,c_11027])).

tff(c_11039,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10606,c_11033])).

tff(c_12030,plain,(
    ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_11039])).

tff(c_12426,plain,(
    ! [C_1056,A_1057,B_1058] :
      ( v1_partfun1(C_1056,A_1057)
      | ~ v1_funct_2(C_1056,A_1057,B_1058)
      | ~ v1_funct_1(C_1056)
      | ~ m1_subset_1(C_1056,k1_zfmisc_1(k2_zfmisc_1(A_1057,B_1058)))
      | v1_xboole_0(B_1058) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_12429,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_12426])).

tff(c_12435,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_12429])).

tff(c_12437,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_12030,c_12435])).

tff(c_12438,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_11039])).

tff(c_12458,plain,(
    ! [B_23] :
      ( k7_relat_1('#skF_7',B_23) = k1_xboole_0
      | ~ r1_xboole_0(B_23,'#skF_5')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12438,c_24])).

tff(c_12698,plain,(
    ! [B_1070] :
      ( k7_relat_1('#skF_7',B_1070) = k1_xboole_0
      | ~ r1_xboole_0(B_1070,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10606,c_12458])).

tff(c_12723,plain,
    ( k7_relat_1('#skF_7','#skF_4') = k1_xboole_0
    | k9_relat_1('#skF_6','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12024,c_12698])).

tff(c_12998,plain,(
    k9_relat_1('#skF_6','#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_12723])).

tff(c_90,plain,(
    r1_subset_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_282])).

tff(c_42,plain,(
    ! [A_30,B_31] :
      ( r1_xboole_0(A_30,B_31)
      | ~ r1_subset_1(A_30,B_31)
      | v1_xboole_0(B_31)
      | v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_20,plain,(
    ! [B_20,A_19] :
      ( k9_relat_1(B_20,A_19) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_20),A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_11989,plain,(
    ! [A_19] :
      ( k9_relat_1('#skF_6',A_19) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_19)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11981,c_20])).

tff(c_12806,plain,(
    ! [A_1076] :
      ( k9_relat_1('#skF_6',A_1076) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_1076) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10607,c_11989])).

tff(c_12813,plain,(
    ! [B_31] :
      ( k9_relat_1('#skF_6',B_31) = k1_xboole_0
      | ~ r1_subset_1('#skF_4',B_31)
      | v1_xboole_0(B_31)
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_12806])).

tff(c_13124,plain,(
    ! [B_1106] :
      ( k9_relat_1('#skF_6',B_1106) = k1_xboole_0
      | ~ r1_subset_1('#skF_4',B_1106)
      | v1_xboole_0(B_1106) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_12813])).

tff(c_13127,plain,
    ( k9_relat_1('#skF_6','#skF_5') = k1_xboole_0
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_90,c_13124])).

tff(c_13131,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_12998,c_13127])).

tff(c_13133,plain,(
    k9_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_12723])).

tff(c_12665,plain,(
    ! [A_1069] :
      ( r1_xboole_0('#skF_4',A_1069)
      | k9_relat_1('#skF_6',A_1069) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10607,c_12004])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_13188,plain,(
    ! [A_1113] :
      ( k3_xboole_0('#skF_4',A_1113) = k1_xboole_0
      | k9_relat_1('#skF_6',A_1113) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12665,c_2])).

tff(c_13202,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_13133,c_13188])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_13259,plain,(
    ! [A_1116] :
      ( k7_relat_1('#skF_7',A_1116) = k1_xboole_0
      | k3_xboole_0(A_1116,'#skF_5') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_12698])).

tff(c_13277,plain,(
    ! [A_1116] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),A_1116)
      | ~ v1_relat_1('#skF_7')
      | k3_xboole_0(A_1116,'#skF_5') != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13259,c_36])).

tff(c_13309,plain,(
    ! [A_1116] :
      ( r1_tarski(k1_xboole_0,A_1116)
      | k3_xboole_0(A_1116,'#skF_5') != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10606,c_30,c_13277])).

tff(c_13132,plain,(
    k7_relat_1('#skF_7','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_12723])).

tff(c_13137,plain,(
    ! [A_15] :
      ( k7_relat_1(k1_xboole_0,A_15) = k7_relat_1('#skF_7',A_15)
      | ~ r1_tarski(A_15,'#skF_4')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13132,c_16])).

tff(c_13434,plain,(
    ! [A_1138] :
      ( k7_relat_1(k1_xboole_0,A_1138) = k7_relat_1('#skF_7',A_1138)
      | ~ r1_tarski(A_1138,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10606,c_13137])).

tff(c_13438,plain,
    ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1('#skF_7',k1_xboole_0)
    | k3_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_13309,c_13434])).

tff(c_13459,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13202,c_10513,c_13438])).

tff(c_12503,plain,(
    ! [A_1059,B_1060,C_1061] :
      ( k9_subset_1(A_1059,B_1060,C_1061) = k3_xboole_0(B_1060,C_1061)
      | ~ m1_subset_1(C_1061,k1_zfmisc_1(A_1059)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12515,plain,(
    ! [B_1060] : k9_subset_1('#skF_2',B_1060,'#skF_5') = k3_xboole_0(B_1060,'#skF_5') ),
    inference(resolution,[status(thm)],[c_92,c_12503])).

tff(c_13175,plain,(
    ! [D_1107,F_1109,E_1112,A_1110,C_1108,B_1111] :
      ( v1_funct_1(k1_tmap_1(A_1110,B_1111,C_1108,D_1107,E_1112,F_1109))
      | ~ m1_subset_1(F_1109,k1_zfmisc_1(k2_zfmisc_1(D_1107,B_1111)))
      | ~ v1_funct_2(F_1109,D_1107,B_1111)
      | ~ v1_funct_1(F_1109)
      | ~ m1_subset_1(E_1112,k1_zfmisc_1(k2_zfmisc_1(C_1108,B_1111)))
      | ~ v1_funct_2(E_1112,C_1108,B_1111)
      | ~ v1_funct_1(E_1112)
      | ~ m1_subset_1(D_1107,k1_zfmisc_1(A_1110))
      | v1_xboole_0(D_1107)
      | ~ m1_subset_1(C_1108,k1_zfmisc_1(A_1110))
      | v1_xboole_0(C_1108)
      | v1_xboole_0(B_1111)
      | v1_xboole_0(A_1110) ) ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_13177,plain,(
    ! [A_1110,C_1108,E_1112] :
      ( v1_funct_1(k1_tmap_1(A_1110,'#skF_3',C_1108,'#skF_5',E_1112,'#skF_7'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_1112,k1_zfmisc_1(k2_zfmisc_1(C_1108,'#skF_3')))
      | ~ v1_funct_2(E_1112,C_1108,'#skF_3')
      | ~ v1_funct_1(E_1112)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1110))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1108,k1_zfmisc_1(A_1110))
      | v1_xboole_0(C_1108)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1110) ) ),
    inference(resolution,[status(thm)],[c_78,c_13175])).

tff(c_13182,plain,(
    ! [A_1110,C_1108,E_1112] :
      ( v1_funct_1(k1_tmap_1(A_1110,'#skF_3',C_1108,'#skF_5',E_1112,'#skF_7'))
      | ~ m1_subset_1(E_1112,k1_zfmisc_1(k2_zfmisc_1(C_1108,'#skF_3')))
      | ~ v1_funct_2(E_1112,C_1108,'#skF_3')
      | ~ v1_funct_1(E_1112)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1110))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1108,k1_zfmisc_1(A_1110))
      | v1_xboole_0(C_1108)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_13177])).

tff(c_13415,plain,(
    ! [A_1135,C_1136,E_1137] :
      ( v1_funct_1(k1_tmap_1(A_1135,'#skF_3',C_1136,'#skF_5',E_1137,'#skF_7'))
      | ~ m1_subset_1(E_1137,k1_zfmisc_1(k2_zfmisc_1(C_1136,'#skF_3')))
      | ~ v1_funct_2(E_1137,C_1136,'#skF_3')
      | ~ v1_funct_1(E_1137)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1135))
      | ~ m1_subset_1(C_1136,k1_zfmisc_1(A_1135))
      | v1_xboole_0(C_1136)
      | v1_xboole_0(A_1135) ) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_94,c_13182])).

tff(c_13422,plain,(
    ! [A_1135] :
      ( v1_funct_1(k1_tmap_1(A_1135,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1135))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1135))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1135) ) ),
    inference(resolution,[status(thm)],[c_84,c_13415])).

tff(c_13432,plain,(
    ! [A_1135] :
      ( v1_funct_1(k1_tmap_1(A_1135,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1135))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1135))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_13422])).

tff(c_13757,plain,(
    ! [A_1158] :
      ( v1_funct_1(k1_tmap_1(A_1158,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1158))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1158))
      | v1_xboole_0(A_1158) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_13432])).

tff(c_13760,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_92,c_13757])).

tff(c_13763,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_13760])).

tff(c_13764,plain,(
    v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_13763])).

tff(c_12757,plain,(
    ! [A_1071,B_1072,C_1073,D_1074] :
      ( k2_partfun1(A_1071,B_1072,C_1073,D_1074) = k7_relat_1(C_1073,D_1074)
      | ~ m1_subset_1(C_1073,k1_zfmisc_1(k2_zfmisc_1(A_1071,B_1072)))
      | ~ v1_funct_1(C_1073) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_12761,plain,(
    ! [D_1074] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_6',D_1074) = k7_relat_1('#skF_6',D_1074)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_84,c_12757])).

tff(c_12767,plain,(
    ! [D_1074] : k2_partfun1('#skF_4','#skF_3','#skF_6',D_1074) = k7_relat_1('#skF_6',D_1074) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_12761])).

tff(c_12759,plain,(
    ! [D_1074] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_7',D_1074) = k7_relat_1('#skF_7',D_1074)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_78,c_12757])).

tff(c_12764,plain,(
    ! [D_1074] : k2_partfun1('#skF_5','#skF_3','#skF_7',D_1074) = k7_relat_1('#skF_7',D_1074) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_12759])).

tff(c_70,plain,(
    ! [E_181,B_178,A_177,D_180,C_179,F_182] :
      ( m1_subset_1(k1_tmap_1(A_177,B_178,C_179,D_180,E_181,F_182),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_177,C_179,D_180),B_178)))
      | ~ m1_subset_1(F_182,k1_zfmisc_1(k2_zfmisc_1(D_180,B_178)))
      | ~ v1_funct_2(F_182,D_180,B_178)
      | ~ v1_funct_1(F_182)
      | ~ m1_subset_1(E_181,k1_zfmisc_1(k2_zfmisc_1(C_179,B_178)))
      | ~ v1_funct_2(E_181,C_179,B_178)
      | ~ v1_funct_1(E_181)
      | ~ m1_subset_1(D_180,k1_zfmisc_1(A_177))
      | v1_xboole_0(D_180)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(A_177))
      | v1_xboole_0(C_179)
      | v1_xboole_0(B_178)
      | v1_xboole_0(A_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_13721,plain,(
    ! [D_1155,C_1153,E_1156,B_1151,F_1154,A_1152] :
      ( k2_partfun1(k4_subset_1(A_1152,C_1153,D_1155),B_1151,k1_tmap_1(A_1152,B_1151,C_1153,D_1155,E_1156,F_1154),D_1155) = F_1154
      | ~ m1_subset_1(k1_tmap_1(A_1152,B_1151,C_1153,D_1155,E_1156,F_1154),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1152,C_1153,D_1155),B_1151)))
      | ~ v1_funct_2(k1_tmap_1(A_1152,B_1151,C_1153,D_1155,E_1156,F_1154),k4_subset_1(A_1152,C_1153,D_1155),B_1151)
      | ~ v1_funct_1(k1_tmap_1(A_1152,B_1151,C_1153,D_1155,E_1156,F_1154))
      | k2_partfun1(D_1155,B_1151,F_1154,k9_subset_1(A_1152,C_1153,D_1155)) != k2_partfun1(C_1153,B_1151,E_1156,k9_subset_1(A_1152,C_1153,D_1155))
      | ~ m1_subset_1(F_1154,k1_zfmisc_1(k2_zfmisc_1(D_1155,B_1151)))
      | ~ v1_funct_2(F_1154,D_1155,B_1151)
      | ~ v1_funct_1(F_1154)
      | ~ m1_subset_1(E_1156,k1_zfmisc_1(k2_zfmisc_1(C_1153,B_1151)))
      | ~ v1_funct_2(E_1156,C_1153,B_1151)
      | ~ v1_funct_1(E_1156)
      | ~ m1_subset_1(D_1155,k1_zfmisc_1(A_1152))
      | v1_xboole_0(D_1155)
      | ~ m1_subset_1(C_1153,k1_zfmisc_1(A_1152))
      | v1_xboole_0(C_1153)
      | v1_xboole_0(B_1151)
      | v1_xboole_0(A_1152) ) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_24839,plain,(
    ! [C_1404,E_1408,B_1407,F_1405,D_1403,A_1406] :
      ( k2_partfun1(k4_subset_1(A_1406,C_1404,D_1403),B_1407,k1_tmap_1(A_1406,B_1407,C_1404,D_1403,E_1408,F_1405),D_1403) = F_1405
      | ~ v1_funct_2(k1_tmap_1(A_1406,B_1407,C_1404,D_1403,E_1408,F_1405),k4_subset_1(A_1406,C_1404,D_1403),B_1407)
      | ~ v1_funct_1(k1_tmap_1(A_1406,B_1407,C_1404,D_1403,E_1408,F_1405))
      | k2_partfun1(D_1403,B_1407,F_1405,k9_subset_1(A_1406,C_1404,D_1403)) != k2_partfun1(C_1404,B_1407,E_1408,k9_subset_1(A_1406,C_1404,D_1403))
      | ~ m1_subset_1(F_1405,k1_zfmisc_1(k2_zfmisc_1(D_1403,B_1407)))
      | ~ v1_funct_2(F_1405,D_1403,B_1407)
      | ~ v1_funct_1(F_1405)
      | ~ m1_subset_1(E_1408,k1_zfmisc_1(k2_zfmisc_1(C_1404,B_1407)))
      | ~ v1_funct_2(E_1408,C_1404,B_1407)
      | ~ v1_funct_1(E_1408)
      | ~ m1_subset_1(D_1403,k1_zfmisc_1(A_1406))
      | v1_xboole_0(D_1403)
      | ~ m1_subset_1(C_1404,k1_zfmisc_1(A_1406))
      | v1_xboole_0(C_1404)
      | v1_xboole_0(B_1407)
      | v1_xboole_0(A_1406) ) ),
    inference(resolution,[status(thm)],[c_70,c_13721])).

tff(c_46434,plain,(
    ! [D_1615,A_1618,E_1620,F_1617,B_1619,C_1616] :
      ( k2_partfun1(k4_subset_1(A_1618,C_1616,D_1615),B_1619,k1_tmap_1(A_1618,B_1619,C_1616,D_1615,E_1620,F_1617),D_1615) = F_1617
      | ~ v1_funct_1(k1_tmap_1(A_1618,B_1619,C_1616,D_1615,E_1620,F_1617))
      | k2_partfun1(D_1615,B_1619,F_1617,k9_subset_1(A_1618,C_1616,D_1615)) != k2_partfun1(C_1616,B_1619,E_1620,k9_subset_1(A_1618,C_1616,D_1615))
      | ~ m1_subset_1(F_1617,k1_zfmisc_1(k2_zfmisc_1(D_1615,B_1619)))
      | ~ v1_funct_2(F_1617,D_1615,B_1619)
      | ~ v1_funct_1(F_1617)
      | ~ m1_subset_1(E_1620,k1_zfmisc_1(k2_zfmisc_1(C_1616,B_1619)))
      | ~ v1_funct_2(E_1620,C_1616,B_1619)
      | ~ v1_funct_1(E_1620)
      | ~ m1_subset_1(D_1615,k1_zfmisc_1(A_1618))
      | v1_xboole_0(D_1615)
      | ~ m1_subset_1(C_1616,k1_zfmisc_1(A_1618))
      | v1_xboole_0(C_1616)
      | v1_xboole_0(B_1619)
      | v1_xboole_0(A_1618) ) ),
    inference(resolution,[status(thm)],[c_72,c_24839])).

tff(c_46438,plain,(
    ! [A_1618,C_1616,E_1620] :
      ( k2_partfun1(k4_subset_1(A_1618,C_1616,'#skF_5'),'#skF_3',k1_tmap_1(A_1618,'#skF_3',C_1616,'#skF_5',E_1620,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1618,'#skF_3',C_1616,'#skF_5',E_1620,'#skF_7'))
      | k2_partfun1(C_1616,'#skF_3',E_1620,k9_subset_1(A_1618,C_1616,'#skF_5')) != k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1(A_1618,C_1616,'#skF_5'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_1620,k1_zfmisc_1(k2_zfmisc_1(C_1616,'#skF_3')))
      | ~ v1_funct_2(E_1620,C_1616,'#skF_3')
      | ~ v1_funct_1(E_1620)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1618))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1616,k1_zfmisc_1(A_1618))
      | v1_xboole_0(C_1616)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1618) ) ),
    inference(resolution,[status(thm)],[c_78,c_46434])).

tff(c_46444,plain,(
    ! [A_1618,C_1616,E_1620] :
      ( k2_partfun1(k4_subset_1(A_1618,C_1616,'#skF_5'),'#skF_3',k1_tmap_1(A_1618,'#skF_3',C_1616,'#skF_5',E_1620,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1618,'#skF_3',C_1616,'#skF_5',E_1620,'#skF_7'))
      | k2_partfun1(C_1616,'#skF_3',E_1620,k9_subset_1(A_1618,C_1616,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_1618,C_1616,'#skF_5'))
      | ~ m1_subset_1(E_1620,k1_zfmisc_1(k2_zfmisc_1(C_1616,'#skF_3')))
      | ~ v1_funct_2(E_1620,C_1616,'#skF_3')
      | ~ v1_funct_1(E_1620)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1618))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1616,k1_zfmisc_1(A_1618))
      | v1_xboole_0(C_1616)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1618) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_12764,c_46438])).

tff(c_69925,plain,(
    ! [A_1750,C_1751,E_1752] :
      ( k2_partfun1(k4_subset_1(A_1750,C_1751,'#skF_5'),'#skF_3',k1_tmap_1(A_1750,'#skF_3',C_1751,'#skF_5',E_1752,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1750,'#skF_3',C_1751,'#skF_5',E_1752,'#skF_7'))
      | k2_partfun1(C_1751,'#skF_3',E_1752,k9_subset_1(A_1750,C_1751,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_1750,C_1751,'#skF_5'))
      | ~ m1_subset_1(E_1752,k1_zfmisc_1(k2_zfmisc_1(C_1751,'#skF_3')))
      | ~ v1_funct_2(E_1752,C_1751,'#skF_3')
      | ~ v1_funct_1(E_1752)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1750))
      | ~ m1_subset_1(C_1751,k1_zfmisc_1(A_1750))
      | v1_xboole_0(C_1751)
      | v1_xboole_0(A_1750) ) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_94,c_46444])).

tff(c_69932,plain,(
    ! [A_1750] :
      ( k2_partfun1(k4_subset_1(A_1750,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_1750,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1750,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1(A_1750,'#skF_4','#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_1750,'#skF_4','#skF_5'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1750))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1750))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1750) ) ),
    inference(resolution,[status(thm)],[c_84,c_69925])).

tff(c_69942,plain,(
    ! [A_1750] :
      ( k2_partfun1(k4_subset_1(A_1750,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_1750,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1750,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_1750,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_1750,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1750))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1750))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1750) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_12767,c_69932])).

tff(c_71990,plain,(
    ! [A_1759] :
      ( k2_partfun1(k4_subset_1(A_1759,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_1759,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1759,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_1759,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_1759,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1759))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1759))
      | v1_xboole_0(A_1759) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_69942])).

tff(c_1191,plain,(
    ! [C_355,A_356,B_357] :
      ( v1_relat_1(C_355)
      | ~ m1_subset_1(C_355,k1_zfmisc_1(k2_zfmisc_1(A_356,B_357))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1199,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_84,c_1191])).

tff(c_150,plain,(
    ! [C_251,A_252,B_253] :
      ( v1_relat_1(C_251)
      | ~ m1_subset_1(C_251,k1_zfmisc_1(k2_zfmisc_1(A_252,B_253))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_158,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_84,c_150])).

tff(c_190,plain,(
    ! [A_257] :
      ( k1_relat_1(A_257) = k1_xboole_0
      | k2_relat_1(A_257) != k1_xboole_0
      | ~ v1_relat_1(A_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_200,plain,
    ( k1_relat_1('#skF_6') = k1_xboole_0
    | k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_158,c_190])).

tff(c_203,plain,(
    k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_200])).

tff(c_231,plain,(
    ! [A_263] :
      ( k2_relat_1(A_263) = k1_xboole_0
      | k1_relat_1(A_263) != k1_xboole_0
      | ~ v1_relat_1(A_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_234,plain,
    ( k2_relat_1('#skF_6') = k1_xboole_0
    | k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_158,c_231])).

tff(c_243,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_203,c_234])).

tff(c_130,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_397,plain,(
    ! [A_285,B_286] :
      ( k7_relat_1(A_285,B_286) = k1_xboole_0
      | ~ r1_xboole_0(B_286,k1_relat_1(A_285))
      | ~ v1_relat_1(A_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_563,plain,(
    ! [A_302] :
      ( k7_relat_1(A_302,'#skF_1'(k1_relat_1(A_302))) = k1_xboole_0
      | ~ v1_relat_1(A_302)
      | k1_relat_1(A_302) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_50,c_397])).

tff(c_579,plain,(
    ! [A_302] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_302)
      | ~ v1_relat_1(A_302)
      | k1_relat_1(A_302) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_563,c_14])).

tff(c_595,plain,(
    ! [A_303] :
      ( ~ v1_relat_1(A_303)
      | ~ v1_relat_1(A_303)
      | k1_relat_1(A_303) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_579])).

tff(c_597,plain,
    ( ~ v1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_158,c_595])).

tff(c_604,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_597])).

tff(c_606,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_243,c_604])).

tff(c_608,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_200])).

tff(c_607,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_200])).

tff(c_667,plain,(
    ! [A_309] :
      ( k9_relat_1(A_309,k1_relat_1(A_309)) = k2_relat_1(A_309)
      | ~ v1_relat_1(A_309) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_676,plain,
    ( k9_relat_1('#skF_6',k1_xboole_0) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_607,c_667])).

tff(c_683,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_608,c_676])).

tff(c_613,plain,
    ( k7_relat_1('#skF_6',k1_xboole_0) = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_607,c_38])).

tff(c_617,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_613])).

tff(c_974,plain,(
    ! [B_336,A_337] :
      ( r1_xboole_0(k1_relat_1(B_336),A_337)
      | k9_relat_1(B_336,A_337) != k1_xboole_0
      | ~ v1_relat_1(B_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_997,plain,(
    ! [A_337] :
      ( r1_xboole_0(k1_xboole_0,A_337)
      | k9_relat_1('#skF_6',A_337) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_607,c_974])).

tff(c_1009,plain,(
    ! [A_338] :
      ( r1_xboole_0(k1_xboole_0,A_338)
      | k9_relat_1('#skF_6',A_338) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_997])).

tff(c_859,plain,(
    ! [A_329,B_330] :
      ( k7_relat_1(A_329,B_330) = k1_xboole_0
      | ~ r1_xboole_0(B_330,k1_relat_1(A_329))
      | ~ v1_relat_1(A_329) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_862,plain,(
    ! [B_330] :
      ( k7_relat_1('#skF_6',B_330) = k1_xboole_0
      | ~ r1_xboole_0(B_330,k1_xboole_0)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_607,c_859])).

tff(c_875,plain,(
    ! [B_330] :
      ( k7_relat_1('#skF_6',B_330) = k1_xboole_0
      | ~ r1_xboole_0(B_330,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_862])).

tff(c_1013,plain,
    ( k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0
    | k9_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1009,c_875])).

tff(c_1032,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_683,c_617,c_1013])).

tff(c_1064,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1032,c_130])).

tff(c_1071,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_1064])).

tff(c_1072,plain,(
    k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_1219,plain,(
    ! [C_358,A_359,B_360] :
      ( v4_relat_1(C_358,A_359)
      | ~ m1_subset_1(C_358,k1_zfmisc_1(k2_zfmisc_1(A_359,B_360))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1227,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_1219])).

tff(c_1624,plain,(
    ! [B_392,A_393] :
      ( k1_relat_1(B_392) = A_393
      | ~ v1_partfun1(B_392,A_393)
      | ~ v4_relat_1(B_392,A_393)
      | ~ v1_relat_1(B_392) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1627,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1227,c_1624])).

tff(c_1633,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1199,c_1627])).

tff(c_1637,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1633])).

tff(c_2547,plain,(
    ! [C_460,A_461,B_462] :
      ( v1_partfun1(C_460,A_461)
      | ~ v1_funct_2(C_460,A_461,B_462)
      | ~ v1_funct_1(C_460)
      | ~ m1_subset_1(C_460,k1_zfmisc_1(k2_zfmisc_1(A_461,B_462)))
      | v1_xboole_0(B_462) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2553,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_2547])).

tff(c_2560,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_2553])).

tff(c_2562,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_1637,c_2560])).

tff(c_2563,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1633])).

tff(c_34,plain,(
    ! [A_26] :
      ( k2_relat_1(A_26) = k1_xboole_0
      | k1_relat_1(A_26) != k1_xboole_0
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1214,plain,
    ( k2_relat_1('#skF_6') = k1_xboole_0
    | k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1199,c_34])).

tff(c_1218,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1214])).

tff(c_2567,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2563,c_1218])).

tff(c_2580,plain,(
    ! [B_23] :
      ( k7_relat_1('#skF_6',B_23) = k1_xboole_0
      | ~ r1_xboole_0(B_23,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2563,c_24])).

tff(c_3186,plain,(
    ! [B_501] :
      ( k7_relat_1('#skF_6',B_501) = k1_xboole_0
      | ~ r1_xboole_0(B_501,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1199,c_2580])).

tff(c_3206,plain,
    ( k7_relat_1('#skF_6','#skF_1'('#skF_4')) = k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50,c_3186])).

tff(c_3215,plain,(
    k7_relat_1('#skF_6','#skF_1'('#skF_4')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_2567,c_3206])).

tff(c_3231,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),'#skF_1'('#skF_4'))
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3215,c_36])).

tff(c_3240,plain,(
    r1_tarski(k1_xboole_0,'#skF_1'('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1199,c_30,c_3231])).

tff(c_3228,plain,(
    ! [A_15] :
      ( k7_relat_1(k1_xboole_0,A_15) = k7_relat_1('#skF_6',A_15)
      | ~ r1_tarski(A_15,'#skF_1'('#skF_4'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3215,c_16])).

tff(c_4186,plain,(
    ! [A_573] :
      ( k7_relat_1(k1_xboole_0,A_573) = k7_relat_1('#skF_6',A_573)
      | ~ r1_tarski(A_573,'#skF_1'('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1199,c_3228])).

tff(c_4197,plain,(
    k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3240,c_4186])).

tff(c_4211,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1072,c_4197])).

tff(c_1198,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_78,c_1191])).

tff(c_2571,plain,(
    ! [A_19] :
      ( r1_xboole_0('#skF_4',A_19)
      | k9_relat_1('#skF_6',A_19) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2563,c_22])).

tff(c_2596,plain,(
    ! [A_19] :
      ( r1_xboole_0('#skF_4',A_19)
      | k9_relat_1('#skF_6',A_19) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1199,c_2571])).

tff(c_1226,plain,(
    v4_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_1219])).

tff(c_1630,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_1226,c_1624])).

tff(c_1636,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1198,c_1630])).

tff(c_2612,plain,(
    ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1636])).

tff(c_2997,plain,(
    ! [C_489,A_490,B_491] :
      ( v1_partfun1(C_489,A_490)
      | ~ v1_funct_2(C_489,A_490,B_491)
      | ~ v1_funct_1(C_489)
      | ~ m1_subset_1(C_489,k1_zfmisc_1(k2_zfmisc_1(A_490,B_491)))
      | v1_xboole_0(B_491) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_3000,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_2997])).

tff(c_3006,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_3000])).

tff(c_3008,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_2612,c_3006])).

tff(c_3009,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1636])).

tff(c_3026,plain,(
    ! [B_23] :
      ( k7_relat_1('#skF_7',B_23) = k1_xboole_0
      | ~ r1_xboole_0(B_23,'#skF_5')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3009,c_24])).

tff(c_3318,plain,(
    ! [B_505] :
      ( k7_relat_1('#skF_7',B_505) = k1_xboole_0
      | ~ r1_xboole_0(B_505,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1198,c_3026])).

tff(c_3347,plain,
    ( k7_relat_1('#skF_7','#skF_4') = k1_xboole_0
    | k9_relat_1('#skF_6','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2596,c_3318])).

tff(c_3696,plain,(
    k9_relat_1('#skF_6','#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3347])).

tff(c_2574,plain,(
    ! [A_19] :
      ( k9_relat_1('#skF_6',A_19) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_19)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2563,c_20])).

tff(c_3394,plain,(
    ! [A_510] :
      ( k9_relat_1('#skF_6',A_510) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_510) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1199,c_2574])).

tff(c_3401,plain,(
    ! [B_31] :
      ( k9_relat_1('#skF_6',B_31) = k1_xboole_0
      | ~ r1_subset_1('#skF_4',B_31)
      | v1_xboole_0(B_31)
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_3394])).

tff(c_3766,plain,(
    ! [B_549] :
      ( k9_relat_1('#skF_6',B_549) = k1_xboole_0
      | ~ r1_subset_1('#skF_4',B_549)
      | v1_xboole_0(B_549) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_3401])).

tff(c_3772,plain,
    ( k9_relat_1('#skF_6','#skF_5') = k1_xboole_0
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_90,c_3766])).

tff(c_3777,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_3696,c_3772])).

tff(c_3778,plain,(
    k7_relat_1('#skF_7','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3347])).

tff(c_3803,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),'#skF_4')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_3778,c_36])).

tff(c_3816,plain,(
    r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1198,c_30,c_3803])).

tff(c_3800,plain,(
    ! [A_15] :
      ( k7_relat_1(k1_xboole_0,A_15) = k7_relat_1('#skF_7',A_15)
      | ~ r1_tarski(A_15,'#skF_4')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3778,c_16])).

tff(c_3932,plain,(
    ! [A_561] :
      ( k7_relat_1(k1_xboole_0,A_561) = k7_relat_1('#skF_7',A_561)
      | ~ r1_tarski(A_561,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1198,c_3800])).

tff(c_3935,plain,(
    k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3816,c_3932])).

tff(c_3956,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1072,c_3935])).

tff(c_3779,plain,(
    k9_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3347])).

tff(c_3285,plain,(
    ! [A_504] :
      ( r1_xboole_0('#skF_4',A_504)
      | k9_relat_1('#skF_6',A_504) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1199,c_2571])).

tff(c_3317,plain,(
    ! [A_504] :
      ( k3_xboole_0('#skF_4',A_504) = k1_xboole_0
      | k9_relat_1('#skF_6',A_504) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3285,c_2])).

tff(c_3838,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3779,c_3317])).

tff(c_3359,plain,(
    ! [A_506,B_507,C_508,D_509] :
      ( k2_partfun1(A_506,B_507,C_508,D_509) = k7_relat_1(C_508,D_509)
      | ~ m1_subset_1(C_508,k1_zfmisc_1(k2_zfmisc_1(A_506,B_507)))
      | ~ v1_funct_1(C_508) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_3361,plain,(
    ! [D_509] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_7',D_509) = k7_relat_1('#skF_7',D_509)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_78,c_3359])).

tff(c_3366,plain,(
    ! [D_509] : k2_partfun1('#skF_5','#skF_3','#skF_7',D_509) = k7_relat_1('#skF_7',D_509) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_3361])).

tff(c_3363,plain,(
    ! [D_509] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_6',D_509) = k7_relat_1('#skF_6',D_509)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_84,c_3359])).

tff(c_3369,plain,(
    ! [D_509] : k2_partfun1('#skF_4','#skF_3','#skF_6',D_509) = k7_relat_1('#skF_6',D_509) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_3363])).

tff(c_3074,plain,(
    ! [A_492,B_493,C_494] :
      ( k9_subset_1(A_492,B_493,C_494) = k3_xboole_0(B_493,C_494)
      | ~ m1_subset_1(C_494,k1_zfmisc_1(A_492)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3086,plain,(
    ! [B_493] : k9_subset_1('#skF_2',B_493,'#skF_5') = k3_xboole_0(B_493,'#skF_5') ),
    inference(resolution,[status(thm)],[c_92,c_3074])).

tff(c_76,plain,
    ( k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') != '#skF_7'
    | k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') != '#skF_6'
    | k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_282])).

tff(c_129,plain,(
    k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_3163,plain,(
    k2_partfun1('#skF_5','#skF_3','#skF_7',k3_xboole_0('#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3','#skF_6',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3086,c_3086,c_129])).

tff(c_7149,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4211,c_3956,c_3838,c_3838,c_3366,c_3369,c_3163])).

tff(c_7150,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1214])).

tff(c_1215,plain,
    ( k1_relat_1('#skF_6') = k1_xboole_0
    | k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1199,c_32])).

tff(c_7157,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7150,c_1215])).

tff(c_7161,plain,
    ( k9_relat_1('#skF_6',k1_xboole_0) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_7157,c_18])).

tff(c_7168,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1199,c_7150,c_7161])).

tff(c_7164,plain,
    ( k7_relat_1('#skF_6',k1_xboole_0) = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_7157,c_38])).

tff(c_7170,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1199,c_7164])).

tff(c_7448,plain,(
    ! [B_664,A_665] :
      ( r1_xboole_0(k1_relat_1(B_664),A_665)
      | k9_relat_1(B_664,A_665) != k1_xboole_0
      | ~ v1_relat_1(B_664) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_7472,plain,(
    ! [A_665] :
      ( r1_xboole_0(k1_xboole_0,A_665)
      | k9_relat_1('#skF_6',A_665) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7157,c_7448])).

tff(c_7487,plain,(
    ! [A_666] :
      ( r1_xboole_0(k1_xboole_0,A_666)
      | k9_relat_1('#skF_6',A_666) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1199,c_7472])).

tff(c_7305,plain,(
    ! [A_656,B_657] :
      ( k7_relat_1(A_656,B_657) = k1_xboole_0
      | ~ r1_xboole_0(B_657,k1_relat_1(A_656))
      | ~ v1_relat_1(A_656) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_7308,plain,(
    ! [B_657] :
      ( k7_relat_1('#skF_6',B_657) = k1_xboole_0
      | ~ r1_xboole_0(B_657,k1_xboole_0)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7157,c_7305])).

tff(c_7321,plain,(
    ! [B_657] :
      ( k7_relat_1('#skF_6',B_657) = k1_xboole_0
      | ~ r1_xboole_0(B_657,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1199,c_7308])).

tff(c_7495,plain,
    ( k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0
    | k9_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7487,c_7321])).

tff(c_7514,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7168,c_7170,c_7495])).

tff(c_1073,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_1171,plain,(
    ! [B_352,A_353] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_352,A_353)),A_353)
      | ~ v1_relat_1(B_352) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1174,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1072,c_1171])).

tff(c_1179,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1073,c_30,c_1174])).

tff(c_1151,plain,(
    ! [B_349,A_350] :
      ( ~ r1_xboole_0(B_349,A_350)
      | ~ r1_tarski(B_349,A_350)
      | v1_xboole_0(B_349) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_7260,plain,(
    ! [A_653,B_654] :
      ( ~ r1_tarski(A_653,B_654)
      | v1_xboole_0(A_653)
      | k3_xboole_0(A_653,B_654) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_1151])).

tff(c_7275,plain,
    ( v1_xboole_0(k1_xboole_0)
    | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1179,c_7260])).

tff(c_7277,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7275])).

tff(c_7532,plain,(
    k3_xboole_0('#skF_6','#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7514,c_7514,c_7514,c_7277])).

tff(c_7537,plain,(
    k9_relat_1('#skF_6','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7514,c_7514,c_7168])).

tff(c_7518,plain,(
    ! [A_666] :
      ( k3_xboole_0(k1_xboole_0,A_666) = k1_xboole_0
      | k9_relat_1('#skF_6',A_666) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_7487,c_2])).

tff(c_7898,plain,(
    ! [A_694] :
      ( k3_xboole_0('#skF_6',A_694) = '#skF_6'
      | k9_relat_1('#skF_6',A_694) != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7514,c_7514,c_7514,c_7518])).

tff(c_7901,plain,(
    k3_xboole_0('#skF_6','#skF_6') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_7537,c_7898])).

tff(c_7909,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7532,c_7901])).

tff(c_7911,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_7275])).

tff(c_7918,plain,(
    ! [A_695,B_696] :
      ( k7_relat_1(A_695,B_696) = k1_xboole_0
      | ~ r1_xboole_0(B_696,k1_relat_1(A_695))
      | ~ v1_relat_1(A_695) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_7921,plain,(
    ! [B_696] :
      ( k7_relat_1('#skF_6',B_696) = k1_xboole_0
      | ~ r1_xboole_0(B_696,k1_xboole_0)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7157,c_7918])).

tff(c_7951,plain,(
    ! [B_698] :
      ( k7_relat_1('#skF_6',B_698) = k1_xboole_0
      | ~ r1_xboole_0(B_698,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1199,c_7921])).

tff(c_8008,plain,(
    ! [A_700] :
      ( k7_relat_1('#skF_6',A_700) = k1_xboole_0
      | k3_xboole_0(A_700,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_7951])).

tff(c_8017,plain,
    ( k1_xboole_0 = '#skF_6'
    | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8008,c_7170])).

tff(c_8043,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7911,c_8017])).

tff(c_8084,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8043,c_8043,c_30])).

tff(c_7191,plain,(
    ! [C_642,A_643,B_644] :
      ( v4_relat_1(C_642,A_643)
      | ~ m1_subset_1(C_642,k1_zfmisc_1(k2_zfmisc_1(A_643,B_644))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_7199,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_7191])).

tff(c_8499,plain,(
    ! [B_732,A_733] :
      ( k1_relat_1(B_732) = A_733
      | ~ v1_partfun1(B_732,A_733)
      | ~ v4_relat_1(B_732,A_733)
      | ~ v1_relat_1(B_732) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_8502,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_7199,c_8499])).

tff(c_8508,plain,
    ( '#skF_6' = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1199,c_8084,c_8502])).

tff(c_8512,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_8508])).

tff(c_9179,plain,(
    ! [C_786,A_787,B_788] :
      ( v1_partfun1(C_786,A_787)
      | ~ v1_funct_2(C_786,A_787,B_788)
      | ~ v1_funct_1(C_786)
      | ~ m1_subset_1(C_786,k1_zfmisc_1(k2_zfmisc_1(A_787,B_788)))
      | v1_xboole_0(B_788) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_9185,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_9179])).

tff(c_9192,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_9185])).

tff(c_9194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_8512,c_9192])).

tff(c_9195,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_8508])).

tff(c_7910,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_7275])).

tff(c_8063,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8043,c_7910])).

tff(c_9226,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9195,c_8063])).

tff(c_9236,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_9226])).

tff(c_9237,plain,
    ( k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_10578,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_9237])).

tff(c_72001,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_71990,c_10578])).

tff(c_72015,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_92,c_13691,c_13459,c_13202,c_13202,c_12515,c_12515,c_13764,c_72001])).

tff(c_72017,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_72015])).

tff(c_72019,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_10629])).

tff(c_72018,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_10629])).

tff(c_72023,plain,
    ( k9_relat_1('#skF_6',k1_xboole_0) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_72018,c_18])).

tff(c_72030,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10607,c_72023])).

tff(c_72052,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72019,c_72030])).

tff(c_72026,plain,
    ( k7_relat_1('#skF_6',k1_xboole_0) = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_72018,c_38])).

tff(c_72032,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10607,c_72026])).

tff(c_72134,plain,(
    ! [B_1771,A_1772] :
      ( r1_xboole_0(k1_relat_1(B_1771),A_1772)
      | k9_relat_1(B_1771,A_1772) != k1_xboole_0
      | ~ v1_relat_1(B_1771) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_72143,plain,(
    ! [A_1772] :
      ( r1_xboole_0(k1_xboole_0,A_1772)
      | k9_relat_1('#skF_6',A_1772) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72018,c_72134])).

tff(c_72150,plain,(
    ! [A_1772] :
      ( r1_xboole_0(k1_xboole_0,A_1772)
      | k9_relat_1('#skF_6',A_1772) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10607,c_72143])).

tff(c_72201,plain,(
    ! [A_1776,B_1777] :
      ( k7_relat_1(A_1776,B_1777) = k1_xboole_0
      | ~ r1_xboole_0(B_1777,k1_relat_1(A_1776))
      | ~ v1_relat_1(A_1776) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_72216,plain,(
    ! [B_1777] :
      ( k7_relat_1('#skF_6',B_1777) = k1_xboole_0
      | ~ r1_xboole_0(B_1777,k1_xboole_0)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72018,c_72201])).

tff(c_72268,plain,(
    ! [B_1779] :
      ( k7_relat_1('#skF_6',B_1779) = k1_xboole_0
      | ~ r1_xboole_0(B_1779,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10607,c_72216])).

tff(c_72272,plain,
    ( k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0
    | k9_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_72150,c_72268])).

tff(c_72291,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72052,c_72032,c_72272])).

tff(c_72325,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72291,c_72291,c_30])).

tff(c_72089,plain,(
    ! [C_1763,A_1764,B_1765] :
      ( v4_relat_1(C_1763,A_1764)
      | ~ m1_subset_1(C_1763,k1_zfmisc_1(k2_zfmisc_1(A_1764,B_1765))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_72097,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_72089])).

tff(c_72759,plain,(
    ! [B_1815,A_1816] :
      ( k1_relat_1(B_1815) = A_1816
      | ~ v1_partfun1(B_1815,A_1816)
      | ~ v4_relat_1(B_1815,A_1816)
      | ~ v1_relat_1(B_1815) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_72762,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_72097,c_72759])).

tff(c_72768,plain,
    ( '#skF_6' = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10607,c_72325,c_72762])).

tff(c_72772,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_72768])).

tff(c_73539,plain,(
    ! [C_1862,A_1863,B_1864] :
      ( v1_partfun1(C_1862,A_1863)
      | ~ v1_funct_2(C_1862,A_1863,B_1864)
      | ~ v1_funct_1(C_1862)
      | ~ m1_subset_1(C_1862,k1_zfmisc_1(k2_zfmisc_1(A_1863,B_1864)))
      | v1_xboole_0(B_1864) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_73545,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_73539])).

tff(c_73552,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_73545])).

tff(c_73554,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_72772,c_73552])).

tff(c_73555,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_72768])).

tff(c_72310,plain,(
    k9_relat_1('#skF_6','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72291,c_72291,c_72052])).

tff(c_10579,plain,(
    ! [B_923,A_924] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_923,A_924)),A_924)
      | ~ v1_relat_1(B_923) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_10582,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10513,c_10579])).

tff(c_10587,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10514,c_30,c_10582])).

tff(c_72317,plain,(
    r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72291,c_72291,c_10587])).

tff(c_72176,plain,(
    ! [A_1774] :
      ( r1_xboole_0(k1_xboole_0,A_1774)
      | k9_relat_1('#skF_6',A_1774) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10607,c_72143])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( ~ r1_xboole_0(B_4,A_3)
      | ~ r1_tarski(B_4,A_3)
      | v1_xboole_0(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_72183,plain,(
    ! [A_1774] :
      ( ~ r1_tarski(k1_xboole_0,A_1774)
      | v1_xboole_0(k1_xboole_0)
      | k9_relat_1('#skF_6',A_1774) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_72176,c_6])).

tff(c_72608,plain,(
    ! [A_1774] :
      ( ~ r1_tarski('#skF_6',A_1774)
      | v1_xboole_0('#skF_6')
      | k9_relat_1('#skF_6',A_1774) != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72291,c_72291,c_72291,c_72183])).

tff(c_72610,plain,(
    ! [A_1802] :
      ( ~ r1_tarski('#skF_6',A_1802)
      | k9_relat_1('#skF_6',A_1802) != '#skF_6' ) ),
    inference(splitLeft,[status(thm)],[c_72608])).

tff(c_72619,plain,(
    k9_relat_1('#skF_6','#skF_6') != '#skF_6' ),
    inference(resolution,[status(thm)],[c_72317,c_72610])).

tff(c_72625,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72310,c_72619])).

tff(c_72626,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_72608])).

tff(c_73562,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73555,c_72626])).

tff(c_73597,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_73562])).

tff(c_73598,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_9237])).

tff(c_73691,plain,(
    ! [C_1875,A_1876,B_1877] :
      ( v4_relat_1(C_1875,A_1876)
      | ~ m1_subset_1(C_1875,k1_zfmisc_1(k2_zfmisc_1(A_1876,B_1877))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_73699,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_73691])).

tff(c_74272,plain,(
    ! [B_1924,A_1925] :
      ( k1_relat_1(B_1924) = A_1925
      | ~ v1_partfun1(B_1924,A_1925)
      | ~ v4_relat_1(B_1924,A_1925)
      | ~ v1_relat_1(B_1924) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_74275,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_73699,c_74272])).

tff(c_74281,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73641,c_74275])).

tff(c_74285,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_74281])).

tff(c_74843,plain,(
    ! [C_1960,A_1961,B_1962] :
      ( v1_partfun1(C_1960,A_1961)
      | ~ v1_funct_2(C_1960,A_1961,B_1962)
      | ~ v1_funct_1(C_1960)
      | ~ m1_subset_1(C_1960,k1_zfmisc_1(k2_zfmisc_1(A_1961,B_1962)))
      | v1_xboole_0(B_1962) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_74849,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_74843])).

tff(c_74856,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_74849])).

tff(c_74858,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_74285,c_74856])).

tff(c_74859,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_74281])).

tff(c_73668,plain,
    ( k1_relat_1('#skF_6') = k1_xboole_0
    | k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_73641,c_32])).

tff(c_73671,plain,(
    k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_73668])).

tff(c_73667,plain,
    ( k2_relat_1('#skF_6') = k1_xboole_0
    | k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_73641,c_34])).

tff(c_73672,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_73671,c_73667])).

tff(c_74864,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74859,c_73672])).

tff(c_74868,plain,(
    ! [B_23] :
      ( k7_relat_1('#skF_6',B_23) = k1_xboole_0
      | ~ r1_xboole_0(B_23,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74859,c_24])).

tff(c_75470,plain,(
    ! [B_1995] :
      ( k7_relat_1('#skF_6',B_1995) = k1_xboole_0
      | ~ r1_xboole_0(B_1995,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73641,c_74868])).

tff(c_75498,plain,
    ( k7_relat_1('#skF_6','#skF_1'('#skF_4')) = k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50,c_75470])).

tff(c_75510,plain,(
    k7_relat_1('#skF_6','#skF_1'('#skF_4')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_74864,c_75498])).

tff(c_75517,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),'#skF_1'('#skF_4'))
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_75510,c_36])).

tff(c_75526,plain,(
    r1_tarski(k1_xboole_0,'#skF_1'('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73641,c_30,c_75517])).

tff(c_75514,plain,(
    ! [A_15] :
      ( k7_relat_1(k1_xboole_0,A_15) = k7_relat_1('#skF_6',A_15)
      | ~ r1_tarski(A_15,'#skF_1'('#skF_4'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75510,c_16])).

tff(c_76547,plain,(
    ! [A_2082] :
      ( k7_relat_1(k1_xboole_0,A_2082) = k7_relat_1('#skF_6',A_2082)
      | ~ r1_tarski(A_2082,'#skF_1'('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73641,c_75514])).

tff(c_76558,plain,(
    k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_75526,c_76547])).

tff(c_76572,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10513,c_76558])).

tff(c_74871,plain,(
    ! [A_19] :
      ( r1_xboole_0('#skF_4',A_19)
      | k9_relat_1('#skF_6',A_19) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74859,c_22])).

tff(c_75438,plain,(
    ! [A_1994] :
      ( r1_xboole_0('#skF_4',A_1994)
      | k9_relat_1('#skF_6',A_1994) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73641,c_74871])).

tff(c_73640,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_78,c_73633])).

tff(c_73698,plain,(
    v4_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_73691])).

tff(c_74278,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_73698,c_74272])).

tff(c_74284,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73640,c_74278])).

tff(c_74985,plain,(
    ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_74284])).

tff(c_75209,plain,(
    ! [C_1980,A_1981,B_1982] :
      ( v1_partfun1(C_1980,A_1981)
      | ~ v1_funct_2(C_1980,A_1981,B_1982)
      | ~ v1_funct_1(C_1980)
      | ~ m1_subset_1(C_1980,k1_zfmisc_1(k2_zfmisc_1(A_1981,B_1982)))
      | v1_xboole_0(B_1982) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_75212,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_75209])).

tff(c_75218,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_75212])).

tff(c_75220,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_74985,c_75218])).

tff(c_75221,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_74284])).

tff(c_75230,plain,(
    ! [B_23] :
      ( k7_relat_1('#skF_7',B_23) = k1_xboole_0
      | ~ r1_xboole_0(B_23,'#skF_5')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75221,c_24])).

tff(c_75255,plain,(
    ! [B_23] :
      ( k7_relat_1('#skF_7',B_23) = k1_xboole_0
      | ~ r1_xboole_0(B_23,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73640,c_75230])).

tff(c_75460,plain,
    ( k7_relat_1('#skF_7','#skF_4') = k1_xboole_0
    | k9_relat_1('#skF_6','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_75438,c_75255])).

tff(c_75596,plain,(
    k9_relat_1('#skF_6','#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_75460])).

tff(c_74883,plain,(
    ! [A_19] :
      ( k9_relat_1('#skF_6',A_19) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_19)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74859,c_20])).

tff(c_75546,plain,(
    ! [A_1997] :
      ( k9_relat_1('#skF_6',A_1997) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_1997) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73641,c_74883])).

tff(c_75553,plain,(
    ! [B_31] :
      ( k9_relat_1('#skF_6',B_31) = k1_xboole_0
      | ~ r1_subset_1('#skF_4',B_31)
      | v1_xboole_0(B_31)
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_75546])).

tff(c_75963,plain,(
    ! [B_2037] :
      ( k9_relat_1('#skF_6',B_2037) = k1_xboole_0
      | ~ r1_subset_1('#skF_4',B_2037)
      | v1_xboole_0(B_2037) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_75553])).

tff(c_75969,plain,
    ( k9_relat_1('#skF_6','#skF_5') = k1_xboole_0
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_90,c_75963])).

tff(c_75974,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_75596,c_75969])).

tff(c_75976,plain,(
    k9_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_75460])).

tff(c_76291,plain,(
    ! [A_2066] :
      ( k3_xboole_0('#skF_4',A_2066) = k1_xboole_0
      | k9_relat_1('#skF_6',A_2066) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_75438,c_2])).

tff(c_76306,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_75976,c_76291])).

tff(c_74189,plain,(
    ! [A_1915,B_1916,C_1917] :
      ( k9_subset_1(A_1915,B_1916,C_1917) = k3_xboole_0(B_1916,C_1917)
      | ~ m1_subset_1(C_1917,k1_zfmisc_1(A_1915)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_74201,plain,(
    ! [B_1916] : k9_subset_1('#skF_2',B_1916,'#skF_5') = k3_xboole_0(B_1916,'#skF_5') ),
    inference(resolution,[status(thm)],[c_92,c_74189])).

tff(c_75327,plain,(
    ! [B_1989] :
      ( k7_relat_1('#skF_7',B_1989) = k1_xboole_0
      | ~ r1_xboole_0(B_1989,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73640,c_75230])).

tff(c_76147,plain,(
    ! [A_2055] :
      ( k7_relat_1('#skF_7',A_2055) = k1_xboole_0
      | k3_xboole_0(A_2055,'#skF_5') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_75327])).

tff(c_76165,plain,(
    ! [A_2055] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),A_2055)
      | ~ v1_relat_1('#skF_7')
      | k3_xboole_0(A_2055,'#skF_5') != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76147,c_36])).

tff(c_76195,plain,(
    ! [A_2055] :
      ( r1_tarski(k1_xboole_0,A_2055)
      | k3_xboole_0(A_2055,'#skF_5') != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73640,c_30,c_76165])).

tff(c_75975,plain,(
    k7_relat_1('#skF_7','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_75460])).

tff(c_75980,plain,(
    ! [A_15] :
      ( k7_relat_1(k1_xboole_0,A_15) = k7_relat_1('#skF_7',A_15)
      | ~ r1_tarski(A_15,'#skF_4')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75975,c_16])).

tff(c_76376,plain,(
    ! [A_2076] :
      ( k7_relat_1(k1_xboole_0,A_2076) = k7_relat_1('#skF_7',A_2076)
      | ~ r1_tarski(A_2076,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73640,c_75980])).

tff(c_76380,plain,
    ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1('#skF_7',k1_xboole_0)
    | k3_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_76195,c_76376])).

tff(c_76401,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_76306,c_10513,c_76380])).

tff(c_75285,plain,(
    ! [A_1983,B_1984,C_1985,D_1986] :
      ( k2_partfun1(A_1983,B_1984,C_1985,D_1986) = k7_relat_1(C_1985,D_1986)
      | ~ m1_subset_1(C_1985,k1_zfmisc_1(k2_zfmisc_1(A_1983,B_1984)))
      | ~ v1_funct_1(C_1985) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_75287,plain,(
    ! [D_1986] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_7',D_1986) = k7_relat_1('#skF_7',D_1986)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_78,c_75285])).

tff(c_75292,plain,(
    ! [D_1986] : k2_partfun1('#skF_5','#skF_3','#skF_7',D_1986) = k7_relat_1('#skF_7',D_1986) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_75287])).

tff(c_75289,plain,(
    ! [D_1986] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_6',D_1986) = k7_relat_1('#skF_6',D_1986)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_84,c_75285])).

tff(c_75295,plain,(
    ! [D_1986] : k2_partfun1('#skF_4','#skF_3','#skF_6',D_1986) = k7_relat_1('#skF_6',D_1986) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_75289])).

tff(c_75579,plain,(
    ! [E_2005,B_2004,D_2000,C_2001,F_2002,A_2003] :
      ( v1_funct_1(k1_tmap_1(A_2003,B_2004,C_2001,D_2000,E_2005,F_2002))
      | ~ m1_subset_1(F_2002,k1_zfmisc_1(k2_zfmisc_1(D_2000,B_2004)))
      | ~ v1_funct_2(F_2002,D_2000,B_2004)
      | ~ v1_funct_1(F_2002)
      | ~ m1_subset_1(E_2005,k1_zfmisc_1(k2_zfmisc_1(C_2001,B_2004)))
      | ~ v1_funct_2(E_2005,C_2001,B_2004)
      | ~ v1_funct_1(E_2005)
      | ~ m1_subset_1(D_2000,k1_zfmisc_1(A_2003))
      | v1_xboole_0(D_2000)
      | ~ m1_subset_1(C_2001,k1_zfmisc_1(A_2003))
      | v1_xboole_0(C_2001)
      | v1_xboole_0(B_2004)
      | v1_xboole_0(A_2003) ) ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_75581,plain,(
    ! [A_2003,C_2001,E_2005] :
      ( v1_funct_1(k1_tmap_1(A_2003,'#skF_3',C_2001,'#skF_5',E_2005,'#skF_7'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_2005,k1_zfmisc_1(k2_zfmisc_1(C_2001,'#skF_3')))
      | ~ v1_funct_2(E_2005,C_2001,'#skF_3')
      | ~ v1_funct_1(E_2005)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2003))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_2001,k1_zfmisc_1(A_2003))
      | v1_xboole_0(C_2001)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2003) ) ),
    inference(resolution,[status(thm)],[c_78,c_75579])).

tff(c_75586,plain,(
    ! [A_2003,C_2001,E_2005] :
      ( v1_funct_1(k1_tmap_1(A_2003,'#skF_3',C_2001,'#skF_5',E_2005,'#skF_7'))
      | ~ m1_subset_1(E_2005,k1_zfmisc_1(k2_zfmisc_1(C_2001,'#skF_3')))
      | ~ v1_funct_2(E_2005,C_2001,'#skF_3')
      | ~ v1_funct_1(E_2005)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2003))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_2001,k1_zfmisc_1(A_2003))
      | v1_xboole_0(C_2001)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2003) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_75581])).

tff(c_76436,plain,(
    ! [A_2077,C_2078,E_2079] :
      ( v1_funct_1(k1_tmap_1(A_2077,'#skF_3',C_2078,'#skF_5',E_2079,'#skF_7'))
      | ~ m1_subset_1(E_2079,k1_zfmisc_1(k2_zfmisc_1(C_2078,'#skF_3')))
      | ~ v1_funct_2(E_2079,C_2078,'#skF_3')
      | ~ v1_funct_1(E_2079)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2077))
      | ~ m1_subset_1(C_2078,k1_zfmisc_1(A_2077))
      | v1_xboole_0(C_2078)
      | v1_xboole_0(A_2077) ) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_94,c_75586])).

tff(c_76443,plain,(
    ! [A_2077] :
      ( v1_funct_1(k1_tmap_1(A_2077,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2077))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2077))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_2077) ) ),
    inference(resolution,[status(thm)],[c_84,c_76436])).

tff(c_76453,plain,(
    ! [A_2077] :
      ( v1_funct_1(k1_tmap_1(A_2077,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2077))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2077))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_2077) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_76443])).

tff(c_76865,plain,(
    ! [A_2099] :
      ( v1_funct_1(k1_tmap_1(A_2099,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2099))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2099))
      | v1_xboole_0(A_2099) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_76453])).

tff(c_76868,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_92,c_76865])).

tff(c_76871,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_76868])).

tff(c_76872,plain,(
    v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_76871])).

tff(c_76350,plain,(
    ! [B_2069,A_2070,E_2074,D_2073,F_2072,C_2071] :
      ( k2_partfun1(k4_subset_1(A_2070,C_2071,D_2073),B_2069,k1_tmap_1(A_2070,B_2069,C_2071,D_2073,E_2074,F_2072),C_2071) = E_2074
      | ~ m1_subset_1(k1_tmap_1(A_2070,B_2069,C_2071,D_2073,E_2074,F_2072),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_2070,C_2071,D_2073),B_2069)))
      | ~ v1_funct_2(k1_tmap_1(A_2070,B_2069,C_2071,D_2073,E_2074,F_2072),k4_subset_1(A_2070,C_2071,D_2073),B_2069)
      | ~ v1_funct_1(k1_tmap_1(A_2070,B_2069,C_2071,D_2073,E_2074,F_2072))
      | k2_partfun1(D_2073,B_2069,F_2072,k9_subset_1(A_2070,C_2071,D_2073)) != k2_partfun1(C_2071,B_2069,E_2074,k9_subset_1(A_2070,C_2071,D_2073))
      | ~ m1_subset_1(F_2072,k1_zfmisc_1(k2_zfmisc_1(D_2073,B_2069)))
      | ~ v1_funct_2(F_2072,D_2073,B_2069)
      | ~ v1_funct_1(F_2072)
      | ~ m1_subset_1(E_2074,k1_zfmisc_1(k2_zfmisc_1(C_2071,B_2069)))
      | ~ v1_funct_2(E_2074,C_2071,B_2069)
      | ~ v1_funct_1(E_2074)
      | ~ m1_subset_1(D_2073,k1_zfmisc_1(A_2070))
      | v1_xboole_0(D_2073)
      | ~ m1_subset_1(C_2071,k1_zfmisc_1(A_2070))
      | v1_xboole_0(C_2071)
      | v1_xboole_0(B_2069)
      | v1_xboole_0(A_2070) ) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_87574,plain,(
    ! [D_2325,B_2329,C_2326,E_2330,F_2327,A_2328] :
      ( k2_partfun1(k4_subset_1(A_2328,C_2326,D_2325),B_2329,k1_tmap_1(A_2328,B_2329,C_2326,D_2325,E_2330,F_2327),C_2326) = E_2330
      | ~ v1_funct_2(k1_tmap_1(A_2328,B_2329,C_2326,D_2325,E_2330,F_2327),k4_subset_1(A_2328,C_2326,D_2325),B_2329)
      | ~ v1_funct_1(k1_tmap_1(A_2328,B_2329,C_2326,D_2325,E_2330,F_2327))
      | k2_partfun1(D_2325,B_2329,F_2327,k9_subset_1(A_2328,C_2326,D_2325)) != k2_partfun1(C_2326,B_2329,E_2330,k9_subset_1(A_2328,C_2326,D_2325))
      | ~ m1_subset_1(F_2327,k1_zfmisc_1(k2_zfmisc_1(D_2325,B_2329)))
      | ~ v1_funct_2(F_2327,D_2325,B_2329)
      | ~ v1_funct_1(F_2327)
      | ~ m1_subset_1(E_2330,k1_zfmisc_1(k2_zfmisc_1(C_2326,B_2329)))
      | ~ v1_funct_2(E_2330,C_2326,B_2329)
      | ~ v1_funct_1(E_2330)
      | ~ m1_subset_1(D_2325,k1_zfmisc_1(A_2328))
      | v1_xboole_0(D_2325)
      | ~ m1_subset_1(C_2326,k1_zfmisc_1(A_2328))
      | v1_xboole_0(C_2326)
      | v1_xboole_0(B_2329)
      | v1_xboole_0(A_2328) ) ),
    inference(resolution,[status(thm)],[c_70,c_76350])).

tff(c_107524,plain,(
    ! [F_2541,A_2542,C_2540,B_2543,D_2539,E_2544] :
      ( k2_partfun1(k4_subset_1(A_2542,C_2540,D_2539),B_2543,k1_tmap_1(A_2542,B_2543,C_2540,D_2539,E_2544,F_2541),C_2540) = E_2544
      | ~ v1_funct_1(k1_tmap_1(A_2542,B_2543,C_2540,D_2539,E_2544,F_2541))
      | k2_partfun1(D_2539,B_2543,F_2541,k9_subset_1(A_2542,C_2540,D_2539)) != k2_partfun1(C_2540,B_2543,E_2544,k9_subset_1(A_2542,C_2540,D_2539))
      | ~ m1_subset_1(F_2541,k1_zfmisc_1(k2_zfmisc_1(D_2539,B_2543)))
      | ~ v1_funct_2(F_2541,D_2539,B_2543)
      | ~ v1_funct_1(F_2541)
      | ~ m1_subset_1(E_2544,k1_zfmisc_1(k2_zfmisc_1(C_2540,B_2543)))
      | ~ v1_funct_2(E_2544,C_2540,B_2543)
      | ~ v1_funct_1(E_2544)
      | ~ m1_subset_1(D_2539,k1_zfmisc_1(A_2542))
      | v1_xboole_0(D_2539)
      | ~ m1_subset_1(C_2540,k1_zfmisc_1(A_2542))
      | v1_xboole_0(C_2540)
      | v1_xboole_0(B_2543)
      | v1_xboole_0(A_2542) ) ),
    inference(resolution,[status(thm)],[c_72,c_87574])).

tff(c_107528,plain,(
    ! [A_2542,C_2540,E_2544] :
      ( k2_partfun1(k4_subset_1(A_2542,C_2540,'#skF_5'),'#skF_3',k1_tmap_1(A_2542,'#skF_3',C_2540,'#skF_5',E_2544,'#skF_7'),C_2540) = E_2544
      | ~ v1_funct_1(k1_tmap_1(A_2542,'#skF_3',C_2540,'#skF_5',E_2544,'#skF_7'))
      | k2_partfun1(C_2540,'#skF_3',E_2544,k9_subset_1(A_2542,C_2540,'#skF_5')) != k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1(A_2542,C_2540,'#skF_5'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_2544,k1_zfmisc_1(k2_zfmisc_1(C_2540,'#skF_3')))
      | ~ v1_funct_2(E_2544,C_2540,'#skF_3')
      | ~ v1_funct_1(E_2544)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2542))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_2540,k1_zfmisc_1(A_2542))
      | v1_xboole_0(C_2540)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2542) ) ),
    inference(resolution,[status(thm)],[c_78,c_107524])).

tff(c_107534,plain,(
    ! [A_2542,C_2540,E_2544] :
      ( k2_partfun1(k4_subset_1(A_2542,C_2540,'#skF_5'),'#skF_3',k1_tmap_1(A_2542,'#skF_3',C_2540,'#skF_5',E_2544,'#skF_7'),C_2540) = E_2544
      | ~ v1_funct_1(k1_tmap_1(A_2542,'#skF_3',C_2540,'#skF_5',E_2544,'#skF_7'))
      | k2_partfun1(C_2540,'#skF_3',E_2544,k9_subset_1(A_2542,C_2540,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_2542,C_2540,'#skF_5'))
      | ~ m1_subset_1(E_2544,k1_zfmisc_1(k2_zfmisc_1(C_2540,'#skF_3')))
      | ~ v1_funct_2(E_2544,C_2540,'#skF_3')
      | ~ v1_funct_1(E_2544)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2542))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_2540,k1_zfmisc_1(A_2542))
      | v1_xboole_0(C_2540)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2542) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_75292,c_107528])).

tff(c_119693,plain,(
    ! [A_2647,C_2648,E_2649] :
      ( k2_partfun1(k4_subset_1(A_2647,C_2648,'#skF_5'),'#skF_3',k1_tmap_1(A_2647,'#skF_3',C_2648,'#skF_5',E_2649,'#skF_7'),C_2648) = E_2649
      | ~ v1_funct_1(k1_tmap_1(A_2647,'#skF_3',C_2648,'#skF_5',E_2649,'#skF_7'))
      | k2_partfun1(C_2648,'#skF_3',E_2649,k9_subset_1(A_2647,C_2648,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_2647,C_2648,'#skF_5'))
      | ~ m1_subset_1(E_2649,k1_zfmisc_1(k2_zfmisc_1(C_2648,'#skF_3')))
      | ~ v1_funct_2(E_2649,C_2648,'#skF_3')
      | ~ v1_funct_1(E_2649)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2647))
      | ~ m1_subset_1(C_2648,k1_zfmisc_1(A_2647))
      | v1_xboole_0(C_2648)
      | v1_xboole_0(A_2647) ) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_94,c_107534])).

tff(c_119700,plain,(
    ! [A_2647] :
      ( k2_partfun1(k4_subset_1(A_2647,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_2647,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_2647,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1(A_2647,'#skF_4','#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_2647,'#skF_4','#skF_5'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2647))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2647))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_2647) ) ),
    inference(resolution,[status(thm)],[c_84,c_119693])).

tff(c_119710,plain,(
    ! [A_2647] :
      ( k2_partfun1(k4_subset_1(A_2647,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_2647,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_2647,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_2647,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_2647,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2647))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2647))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_2647) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_75295,c_119700])).

tff(c_124663,plain,(
    ! [A_2666] :
      ( k2_partfun1(k4_subset_1(A_2666,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_2666,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_2666,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_2666,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_2666,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2666))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2666))
      | v1_xboole_0(A_2666) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_119710])).

tff(c_73599,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_9237])).

tff(c_76576,plain,(
    ! [A_2084,D_2086,B_2083,G_2087,C_2085] :
      ( k1_tmap_1(A_2084,B_2083,C_2085,D_2086,k2_partfun1(k4_subset_1(A_2084,C_2085,D_2086),B_2083,G_2087,C_2085),k2_partfun1(k4_subset_1(A_2084,C_2085,D_2086),B_2083,G_2087,D_2086)) = G_2087
      | ~ m1_subset_1(G_2087,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_2084,C_2085,D_2086),B_2083)))
      | ~ v1_funct_2(G_2087,k4_subset_1(A_2084,C_2085,D_2086),B_2083)
      | ~ v1_funct_1(G_2087)
      | k2_partfun1(D_2086,B_2083,k2_partfun1(k4_subset_1(A_2084,C_2085,D_2086),B_2083,G_2087,D_2086),k9_subset_1(A_2084,C_2085,D_2086)) != k2_partfun1(C_2085,B_2083,k2_partfun1(k4_subset_1(A_2084,C_2085,D_2086),B_2083,G_2087,C_2085),k9_subset_1(A_2084,C_2085,D_2086))
      | ~ m1_subset_1(k2_partfun1(k4_subset_1(A_2084,C_2085,D_2086),B_2083,G_2087,D_2086),k1_zfmisc_1(k2_zfmisc_1(D_2086,B_2083)))
      | ~ v1_funct_2(k2_partfun1(k4_subset_1(A_2084,C_2085,D_2086),B_2083,G_2087,D_2086),D_2086,B_2083)
      | ~ v1_funct_1(k2_partfun1(k4_subset_1(A_2084,C_2085,D_2086),B_2083,G_2087,D_2086))
      | ~ m1_subset_1(k2_partfun1(k4_subset_1(A_2084,C_2085,D_2086),B_2083,G_2087,C_2085),k1_zfmisc_1(k2_zfmisc_1(C_2085,B_2083)))
      | ~ v1_funct_2(k2_partfun1(k4_subset_1(A_2084,C_2085,D_2086),B_2083,G_2087,C_2085),C_2085,B_2083)
      | ~ v1_funct_1(k2_partfun1(k4_subset_1(A_2084,C_2085,D_2086),B_2083,G_2087,C_2085))
      | ~ m1_subset_1(D_2086,k1_zfmisc_1(A_2084))
      | v1_xboole_0(D_2086)
      | ~ m1_subset_1(C_2085,k1_zfmisc_1(A_2084))
      | v1_xboole_0(C_2085)
      | v1_xboole_0(B_2083)
      | v1_xboole_0(A_2084) ) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_76578,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_73599,c_76576])).

tff(c_76580,plain,
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
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_92,c_82,c_73599,c_80,c_73599,c_78,c_76401,c_76306,c_76306,c_75292,c_73599,c_74201,c_74201,c_73599,c_76578])).

tff(c_76581,plain,
    ( k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5',k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),'#skF_7') = k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3')))
    | ~ v1_funct_2(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3')
    | ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | k2_partfun1('#skF_4','#skF_3',k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),k1_xboole_0) != k1_xboole_0
    | ~ m1_subset_1(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_100,c_98,c_94,c_76580])).

tff(c_80703,plain,
    ( k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5',k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),'#skF_7') = k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3')))
    | ~ v1_funct_2(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3')
    | k2_partfun1('#skF_4','#skF_3',k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),k1_xboole_0) != k1_xboole_0
    | ~ m1_subset_1(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76872,c_76581])).

tff(c_80704,plain,(
    ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_80703])).

tff(c_124672,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_124663,c_80704])).

tff(c_124685,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_92,c_76572,c_76401,c_76306,c_76306,c_74201,c_74201,c_76872,c_88,c_124672])).

tff(c_124687,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_124685])).

tff(c_124688,plain,
    ( ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | k2_partfun1('#skF_4','#skF_3',k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),k1_xboole_0) != k1_xboole_0
    | ~ v1_funct_2(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3')
    | ~ m1_subset_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3')))
    | k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5',k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),'#skF_7') = k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_80703])).

tff(c_126446,plain,(
    ~ m1_subset_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_124688])).

tff(c_127144,plain,
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
    inference(resolution,[status(thm)],[c_70,c_126446])).

tff(c_127147,plain,
    ( v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_92,c_88,c_86,c_84,c_82,c_80,c_78,c_127144])).

tff(c_127149,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_100,c_98,c_94,c_127147])).

tff(c_127151,plain,(
    m1_subset_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_124688])).

tff(c_68,plain,(
    ! [A_50,D_162,F_174,B_114,E_170,C_146] :
      ( k2_partfun1(k4_subset_1(A_50,C_146,D_162),B_114,k1_tmap_1(A_50,B_114,C_146,D_162,E_170,F_174),C_146) = E_170
      | ~ m1_subset_1(k1_tmap_1(A_50,B_114,C_146,D_162,E_170,F_174),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_50,C_146,D_162),B_114)))
      | ~ v1_funct_2(k1_tmap_1(A_50,B_114,C_146,D_162,E_170,F_174),k4_subset_1(A_50,C_146,D_162),B_114)
      | ~ v1_funct_1(k1_tmap_1(A_50,B_114,C_146,D_162,E_170,F_174))
      | k2_partfun1(D_162,B_114,F_174,k9_subset_1(A_50,C_146,D_162)) != k2_partfun1(C_146,B_114,E_170,k9_subset_1(A_50,C_146,D_162))
      | ~ m1_subset_1(F_174,k1_zfmisc_1(k2_zfmisc_1(D_162,B_114)))
      | ~ v1_funct_2(F_174,D_162,B_114)
      | ~ v1_funct_1(F_174)
      | ~ m1_subset_1(E_170,k1_zfmisc_1(k2_zfmisc_1(C_146,B_114)))
      | ~ v1_funct_2(E_170,C_146,B_114)
      | ~ v1_funct_1(E_170)
      | ~ m1_subset_1(D_162,k1_zfmisc_1(A_50))
      | v1_xboole_0(D_162)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(A_50))
      | v1_xboole_0(C_146)
      | v1_xboole_0(B_114)
      | v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_127852,plain,
    ( k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
    | ~ v1_funct_2(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3')
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
    inference(resolution,[status(thm)],[c_127151,c_68])).

tff(c_127884,plain,
    ( k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
    | ~ v1_funct_2(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3')
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_92,c_88,c_86,c_84,c_82,c_80,c_78,c_76572,c_76306,c_74201,c_76401,c_76306,c_74201,c_75292,c_75295,c_76872,c_127852])).

tff(c_127885,plain,(
    ~ v1_funct_2(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_100,c_98,c_94,c_73598,c_127884])).

tff(c_127987,plain,
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
    inference(resolution,[status(thm)],[c_72,c_127885])).

tff(c_127990,plain,
    ( v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_92,c_88,c_86,c_84,c_82,c_80,c_78,c_127987])).

tff(c_127992,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_100,c_98,c_94,c_127990])).

tff(c_127993,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_73668])).

tff(c_128015,plain,
    ( k7_relat_1('#skF_6',k1_xboole_0) = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_127993,c_38])).

tff(c_128021,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73641,c_128015])).

tff(c_128166,plain,(
    ! [B_2714,A_2715] :
      ( r1_xboole_0(k1_relat_1(B_2714),A_2715)
      | k9_relat_1(B_2714,A_2715) != k1_xboole_0
      | ~ v1_relat_1(B_2714) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_128178,plain,(
    ! [A_2715] :
      ( r1_xboole_0(k1_xboole_0,A_2715)
      | k9_relat_1(k1_xboole_0,A_2715) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_128166])).

tff(c_128184,plain,(
    ! [A_2715] :
      ( r1_xboole_0(k1_xboole_0,A_2715)
      | k9_relat_1(k1_xboole_0,A_2715) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10514,c_128178])).

tff(c_128185,plain,(
    ! [A_2716,B_2717] :
      ( k7_relat_1(A_2716,B_2717) = k1_xboole_0
      | ~ r1_xboole_0(B_2717,k1_relat_1(A_2716))
      | ~ v1_relat_1(A_2716) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_128196,plain,(
    ! [B_2717] :
      ( k7_relat_1('#skF_6',B_2717) = k1_xboole_0
      | ~ r1_xboole_0(B_2717,k1_xboole_0)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127993,c_128185])).

tff(c_128259,plain,(
    ! [B_2720] :
      ( k7_relat_1('#skF_6',B_2720) = k1_xboole_0
      | ~ r1_xboole_0(B_2720,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73641,c_128196])).

tff(c_128263,plain,
    ( k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0
    | k9_relat_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_128184,c_128259])).

tff(c_128282,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128008,c_128021,c_128263])).

tff(c_73600,plain,(
    ! [B_1865,A_1866] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_1865,A_1866)),A_1866)
      | ~ v1_relat_1(B_1865) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_73603,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10513,c_73600])).

tff(c_73608,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10514,c_30,c_73603])).

tff(c_73624,plain,(
    ! [B_1868,A_1869] :
      ( ~ r1_xboole_0(B_1868,A_1869)
      | ~ r1_tarski(B_1868,A_1869)
      | v1_xboole_0(B_1868) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_128142,plain,(
    ! [A_2712,B_2713] :
      ( ~ r1_tarski(A_2712,B_2713)
      | v1_xboole_0(A_2712)
      | k3_xboole_0(A_2712,B_2713) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_73624])).

tff(c_128161,plain,
    ( v1_xboole_0(k1_xboole_0)
    | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_73608,c_128142])).

tff(c_128163,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_128161])).

tff(c_128324,plain,(
    k3_xboole_0('#skF_6','#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128282,c_128282,c_128282,c_128163])).

tff(c_127994,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_73668])).

tff(c_128012,plain,
    ( k9_relat_1('#skF_6',k1_xboole_0) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_127993,c_18])).

tff(c_128019,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73641,c_128012])).

tff(c_128047,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_127994,c_128019])).

tff(c_128328,plain,(
    k9_relat_1('#skF_6','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128282,c_128282,c_128047])).

tff(c_128216,plain,(
    ! [A_2718] :
      ( r1_xboole_0(k1_xboole_0,A_2718)
      | k9_relat_1(k1_xboole_0,A_2718) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10514,c_128178])).

tff(c_128229,plain,(
    ! [A_2718] :
      ( k3_xboole_0(k1_xboole_0,A_2718) = k1_xboole_0
      | k9_relat_1(k1_xboole_0,A_2718) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_128216,c_2])).

tff(c_128572,plain,(
    ! [A_2743] :
      ( k3_xboole_0('#skF_6',A_2743) = '#skF_6'
      | k9_relat_1('#skF_6',A_2743) != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128282,c_128282,c_128282,c_128282,c_128229])).

tff(c_128575,plain,(
    k3_xboole_0('#skF_6','#skF_6') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_128328,c_128572])).

tff(c_128583,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128324,c_128575])).

tff(c_128585,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_128161])).

tff(c_128605,plain,(
    ! [A_2746,B_2747] :
      ( k7_relat_1(A_2746,B_2747) = k1_xboole_0
      | ~ r1_xboole_0(B_2747,k1_relat_1(A_2746))
      | ~ v1_relat_1(A_2746) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_128612,plain,(
    ! [B_2747] :
      ( k7_relat_1('#skF_6',B_2747) = k1_xboole_0
      | ~ r1_xboole_0(B_2747,k1_xboole_0)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127993,c_128605])).

tff(c_128649,plain,(
    ! [B_2749] :
      ( k7_relat_1('#skF_6',B_2749) = k1_xboole_0
      | ~ r1_xboole_0(B_2749,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73641,c_128612])).

tff(c_128718,plain,(
    ! [A_2752] :
      ( k7_relat_1('#skF_6',A_2752) = k1_xboole_0
      | k3_xboole_0(A_2752,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_128649])).

tff(c_128727,plain,
    ( k1_xboole_0 = '#skF_6'
    | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_128718,c_128021])).

tff(c_128753,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128585,c_128727])).

tff(c_128781,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128753,c_127993])).

tff(c_128052,plain,(
    ! [C_2700,A_2701,B_2702] :
      ( v4_relat_1(C_2700,A_2701)
      | ~ m1_subset_1(C_2700,k1_zfmisc_1(k2_zfmisc_1(A_2701,B_2702))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_128060,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_128052])).

tff(c_129018,plain,(
    ! [B_2773,A_2774] :
      ( k1_relat_1(B_2773) = A_2774
      | ~ v1_partfun1(B_2773,A_2774)
      | ~ v4_relat_1(B_2773,A_2774)
      | ~ v1_relat_1(B_2773) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_129021,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_128060,c_129018])).

tff(c_129027,plain,
    ( '#skF_6' = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73641,c_128781,c_129021])).

tff(c_129031,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_129027])).

tff(c_129734,plain,(
    ! [C_2819,A_2820,B_2821] :
      ( v1_partfun1(C_2819,A_2820)
      | ~ v1_funct_2(C_2819,A_2820,B_2821)
      | ~ v1_funct_1(C_2819)
      | ~ m1_subset_1(C_2819,k1_zfmisc_1(k2_zfmisc_1(A_2820,B_2821)))
      | v1_xboole_0(B_2821) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_129740,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_129734])).

tff(c_129747,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_129740])).

tff(c_129749,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_129031,c_129747])).

tff(c_129750,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_129027])).

tff(c_128584,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_128161])).

tff(c_128773,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128753,c_128584])).

tff(c_129771,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129750,c_128773])).

tff(c_129784,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_129771])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:13:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 26.90/17.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.25/17.65  
% 27.25/17.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.25/17.65  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 27.25/17.65  
% 27.25/17.65  %Foreground sorts:
% 27.25/17.65  
% 27.25/17.65  
% 27.25/17.65  %Background operators:
% 27.25/17.65  
% 27.25/17.65  
% 27.25/17.65  %Foreground operators:
% 27.25/17.65  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 27.25/17.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 27.25/17.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 27.25/17.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 27.25/17.65  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 27.25/17.65  tff('#skF_1', type, '#skF_1': $i > $i).
% 27.25/17.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 27.25/17.65  tff('#skF_7', type, '#skF_7': $i).
% 27.25/17.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 27.25/17.65  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 27.25/17.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 27.25/17.65  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 27.25/17.65  tff('#skF_5', type, '#skF_5': $i).
% 27.25/17.65  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 27.25/17.65  tff('#skF_6', type, '#skF_6': $i).
% 27.25/17.65  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 27.25/17.65  tff('#skF_2', type, '#skF_2': $i).
% 27.25/17.65  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 27.25/17.65  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 27.25/17.65  tff('#skF_3', type, '#skF_3': $i).
% 27.25/17.65  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 27.25/17.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 27.25/17.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 27.25/17.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 27.25/17.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 27.25/17.65  tff('#skF_4', type, '#skF_4': $i).
% 27.25/17.65  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 27.25/17.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 27.25/17.65  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 27.25/17.65  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 27.25/17.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 27.25/17.65  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 27.25/17.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 27.25/17.65  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 27.25/17.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 27.25/17.65  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 27.25/17.65  
% 27.55/17.71  tff(f_282, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 27.55/17.71  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 27.55/17.71  tff(f_86, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 27.55/17.71  tff(f_100, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 27.55/17.71  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 27.55/17.71  tff(f_152, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 27.55/17.71  tff(f_144, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 27.55/17.71  tff(f_92, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 27.55/17.71  tff(f_130, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 27.55/17.71  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 27.55/17.71  tff(f_54, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 27.55/17.71  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 27.55/17.71  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 27.55/17.71  tff(f_240, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 27.55/17.71  tff(f_96, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 27.55/17.71  tff(f_60, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_relat_1)).
% 27.55/17.71  tff(f_110, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 27.55/17.72  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 27.55/17.72  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 27.55/17.72  tff(f_158, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 27.55/17.72  tff(f_206, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 27.55/17.72  tff(f_37, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 27.55/17.72  tff(c_98, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_282])).
% 27.55/17.72  tff(c_100, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_282])).
% 27.55/17.72  tff(c_84, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_282])).
% 27.55/17.72  tff(c_73633, plain, (![C_1870, A_1871, B_1872]: (v1_relat_1(C_1870) | ~m1_subset_1(C_1870, k1_zfmisc_1(k2_zfmisc_1(A_1871, B_1872))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 27.55/17.72  tff(c_73641, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_84, c_73633])).
% 27.55/17.72  tff(c_78, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_282])).
% 27.55/17.72  tff(c_9292, plain, (![C_798, A_799, B_800]: (v1_relat_1(C_798) | ~m1_subset_1(C_798, k1_zfmisc_1(k2_zfmisc_1(A_799, B_800))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 27.55/17.72  tff(c_9299, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_78, c_9292])).
% 27.55/17.72  tff(c_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 27.55/17.72  tff(c_114, plain, (![A_244]: (k7_relat_1(A_244, k1_relat_1(A_244))=A_244 | ~v1_relat_1(A_244))), inference(cnfTransformation, [status(thm)], [f_100])).
% 27.55/17.72  tff(c_126, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30, c_114])).
% 27.55/17.72  tff(c_9239, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_126])).
% 27.55/17.72  tff(c_9372, plain, (![C_813, A_814, B_815]: (v4_relat_1(C_813, A_814) | ~m1_subset_1(C_813, k1_zfmisc_1(k2_zfmisc_1(A_814, B_815))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 27.55/17.72  tff(c_9379, plain, (v4_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_78, c_9372])).
% 27.55/17.72  tff(c_9535, plain, (![B_831, A_832]: (k1_relat_1(B_831)=A_832 | ~v1_partfun1(B_831, A_832) | ~v4_relat_1(B_831, A_832) | ~v1_relat_1(B_831))), inference(cnfTransformation, [status(thm)], [f_152])).
% 27.55/17.72  tff(c_9541, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_9379, c_9535])).
% 27.55/17.72  tff(c_9547, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_9299, c_9541])).
% 27.55/17.72  tff(c_9549, plain, (~v1_partfun1('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_9547])).
% 27.55/17.72  tff(c_82, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_282])).
% 27.55/17.72  tff(c_80, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_282])).
% 27.55/17.72  tff(c_9831, plain, (![C_863, A_864, B_865]: (v1_partfun1(C_863, A_864) | ~v1_funct_2(C_863, A_864, B_865) | ~v1_funct_1(C_863) | ~m1_subset_1(C_863, k1_zfmisc_1(k2_zfmisc_1(A_864, B_865))) | v1_xboole_0(B_865))), inference(cnfTransformation, [status(thm)], [f_144])).
% 27.55/17.72  tff(c_9834, plain, (v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_78, c_9831])).
% 27.55/17.72  tff(c_9840, plain, (v1_partfun1('#skF_7', '#skF_5') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_9834])).
% 27.55/17.72  tff(c_9842, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_9549, c_9840])).
% 27.55/17.72  tff(c_9843, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitRight, [status(thm)], [c_9547])).
% 27.55/17.72  tff(c_9316, plain, (![A_802]: (k1_relat_1(A_802)=k1_xboole_0 | k2_relat_1(A_802)!=k1_xboole_0 | ~v1_relat_1(A_802))), inference(cnfTransformation, [status(thm)], [f_92])).
% 27.55/17.72  tff(c_9327, plain, (k1_relat_1('#skF_7')=k1_xboole_0 | k2_relat_1('#skF_7')!=k1_xboole_0), inference(resolution, [status(thm)], [c_9299, c_9316])).
% 27.55/17.72  tff(c_9334, plain, (k2_relat_1('#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_9327])).
% 27.55/17.72  tff(c_9345, plain, (![A_807]: (k2_relat_1(A_807)=k1_xboole_0 | k1_relat_1(A_807)!=k1_xboole_0 | ~v1_relat_1(A_807))), inference(cnfTransformation, [status(thm)], [f_92])).
% 27.55/17.72  tff(c_9351, plain, (k2_relat_1('#skF_7')=k1_xboole_0 | k1_relat_1('#skF_7')!=k1_xboole_0), inference(resolution, [status(thm)], [c_9299, c_9345])).
% 27.55/17.72  tff(c_9360, plain, (k1_relat_1('#skF_7')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_9334, c_9351])).
% 27.55/17.72  tff(c_9847, plain, (k1_xboole_0!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_9843, c_9360])).
% 27.55/17.72  tff(c_50, plain, (![A_38]: (r1_xboole_0('#skF_1'(A_38), A_38) | k1_xboole_0=A_38)), inference(cnfTransformation, [status(thm)], [f_130])).
% 27.55/17.72  tff(c_24, plain, (![A_21, B_23]: (k7_relat_1(A_21, B_23)=k1_xboole_0 | ~r1_xboole_0(B_23, k1_relat_1(A_21)) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_77])).
% 27.55/17.72  tff(c_9866, plain, (![B_23]: (k7_relat_1('#skF_7', B_23)=k1_xboole_0 | ~r1_xboole_0(B_23, '#skF_5') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_9843, c_24])).
% 27.55/17.72  tff(c_9968, plain, (![B_873]: (k7_relat_1('#skF_7', B_873)=k1_xboole_0 | ~r1_xboole_0(B_873, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_9299, c_9866])).
% 27.55/17.72  tff(c_9988, plain, (k7_relat_1('#skF_7', '#skF_1'('#skF_5'))=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_50, c_9968])).
% 27.55/17.72  tff(c_9998, plain, (k7_relat_1('#skF_7', '#skF_1'('#skF_5'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_9847, c_9988])).
% 27.55/17.72  tff(c_14, plain, (![A_13, B_14]: (v1_relat_1(k7_relat_1(A_13, B_14)) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 27.55/17.72  tff(c_10005, plain, (v1_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_9998, c_14])).
% 27.55/17.72  tff(c_10011, plain, (v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_9299, c_10005])).
% 27.55/17.72  tff(c_10013, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9239, c_10011])).
% 27.55/17.72  tff(c_10015, plain, (k2_relat_1('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_9327])).
% 27.55/17.72  tff(c_10014, plain, (k1_relat_1('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_9327])).
% 27.55/17.72  tff(c_18, plain, (![A_18]: (k9_relat_1(A_18, k1_relat_1(A_18))=k2_relat_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_64])).
% 27.55/17.72  tff(c_10019, plain, (k9_relat_1('#skF_7', k1_xboole_0)=k2_relat_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_10014, c_18])).
% 27.55/17.72  tff(c_10026, plain, (k9_relat_1('#skF_7', k1_xboole_0)=k2_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_9299, c_10019])).
% 27.55/17.72  tff(c_10057, plain, (k9_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10015, c_10026])).
% 27.55/17.72  tff(c_38, plain, (![A_29]: (k7_relat_1(A_29, k1_relat_1(A_29))=A_29 | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_100])).
% 27.55/17.72  tff(c_10022, plain, (k7_relat_1('#skF_7', k1_xboole_0)='#skF_7' | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_10014, c_38])).
% 27.55/17.72  tff(c_10028, plain, (k7_relat_1('#skF_7', k1_xboole_0)='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_9299, c_10022])).
% 27.55/17.72  tff(c_10348, plain, (![B_903, A_904]: (r1_xboole_0(k1_relat_1(B_903), A_904) | k9_relat_1(B_903, A_904)!=k1_xboole_0 | ~v1_relat_1(B_903))), inference(cnfTransformation, [status(thm)], [f_70])).
% 27.55/17.72  tff(c_10360, plain, (![A_904]: (r1_xboole_0(k1_xboole_0, A_904) | k9_relat_1('#skF_7', A_904)!=k1_xboole_0 | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_10014, c_10348])).
% 27.55/17.72  tff(c_10368, plain, (![A_904]: (r1_xboole_0(k1_xboole_0, A_904) | k9_relat_1('#skF_7', A_904)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_9299, c_10360])).
% 27.55/17.72  tff(c_10425, plain, (![A_911, B_912]: (k7_relat_1(A_911, B_912)=k1_xboole_0 | ~r1_xboole_0(B_912, k1_relat_1(A_911)) | ~v1_relat_1(A_911))), inference(cnfTransformation, [status(thm)], [f_77])).
% 27.55/17.72  tff(c_10436, plain, (![B_912]: (k7_relat_1('#skF_7', B_912)=k1_xboole_0 | ~r1_xboole_0(B_912, k1_xboole_0) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_10014, c_10425])).
% 27.55/17.72  tff(c_10454, plain, (![B_913]: (k7_relat_1('#skF_7', B_913)=k1_xboole_0 | ~r1_xboole_0(B_913, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_9299, c_10436])).
% 27.55/17.72  tff(c_10458, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0 | k9_relat_1('#skF_7', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_10368, c_10454])).
% 27.55/17.72  tff(c_10473, plain, (k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_10057, c_10028, c_10458])).
% 27.55/17.72  tff(c_10505, plain, (~v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_10473, c_9239])).
% 27.55/17.72  tff(c_10512, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9299, c_10505])).
% 27.55/17.72  tff(c_10514, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_126])).
% 27.55/17.72  tff(c_28, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 27.55/17.72  tff(c_127995, plain, (![A_2699]: (k9_relat_1(A_2699, k1_relat_1(A_2699))=k2_relat_1(A_2699) | ~v1_relat_1(A_2699))), inference(cnfTransformation, [status(thm)], [f_64])).
% 27.55/17.72  tff(c_128004, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30, c_127995])).
% 27.55/17.72  tff(c_128008, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10514, c_28, c_128004])).
% 27.55/17.72  tff(c_102, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_282])).
% 27.55/17.72  tff(c_94, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_282])).
% 27.55/17.72  tff(c_96, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_282])).
% 27.55/17.72  tff(c_92, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_282])).
% 27.55/17.72  tff(c_88, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_282])).
% 27.55/17.72  tff(c_86, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_282])).
% 27.55/17.72  tff(c_72, plain, (![E_181, B_178, A_177, D_180, C_179, F_182]: (v1_funct_2(k1_tmap_1(A_177, B_178, C_179, D_180, E_181, F_182), k4_subset_1(A_177, C_179, D_180), B_178) | ~m1_subset_1(F_182, k1_zfmisc_1(k2_zfmisc_1(D_180, B_178))) | ~v1_funct_2(F_182, D_180, B_178) | ~v1_funct_1(F_182) | ~m1_subset_1(E_181, k1_zfmisc_1(k2_zfmisc_1(C_179, B_178))) | ~v1_funct_2(E_181, C_179, B_178) | ~v1_funct_1(E_181) | ~m1_subset_1(D_180, k1_zfmisc_1(A_177)) | v1_xboole_0(D_180) | ~m1_subset_1(C_179, k1_zfmisc_1(A_177)) | v1_xboole_0(C_179) | v1_xboole_0(B_178) | v1_xboole_0(A_177))), inference(cnfTransformation, [status(thm)], [f_240])).
% 27.55/17.72  tff(c_10599, plain, (![C_926, A_927, B_928]: (v1_relat_1(C_926) | ~m1_subset_1(C_926, k1_zfmisc_1(k2_zfmisc_1(A_927, B_928))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 27.55/17.72  tff(c_10607, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_84, c_10599])).
% 27.55/17.72  tff(c_10513, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_126])).
% 27.55/17.72  tff(c_10668, plain, (![C_933, A_934, B_935]: (v4_relat_1(C_933, A_934) | ~m1_subset_1(C_933, k1_zfmisc_1(k2_zfmisc_1(A_934, B_935))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 27.55/17.72  tff(c_10676, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_84, c_10668])).
% 27.55/17.72  tff(c_11027, plain, (![B_963, A_964]: (k1_relat_1(B_963)=A_964 | ~v1_partfun1(B_963, A_964) | ~v4_relat_1(B_963, A_964) | ~v1_relat_1(B_963))), inference(cnfTransformation, [status(thm)], [f_152])).
% 27.55/17.72  tff(c_11030, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_10676, c_11027])).
% 27.55/17.72  tff(c_11036, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10607, c_11030])).
% 27.55/17.72  tff(c_11040, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_11036])).
% 27.55/17.72  tff(c_11965, plain, (![C_1028, A_1029, B_1030]: (v1_partfun1(C_1028, A_1029) | ~v1_funct_2(C_1028, A_1029, B_1030) | ~v1_funct_1(C_1028) | ~m1_subset_1(C_1028, k1_zfmisc_1(k2_zfmisc_1(A_1029, B_1030))) | v1_xboole_0(B_1030))), inference(cnfTransformation, [status(thm)], [f_144])).
% 27.55/17.72  tff(c_11971, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_84, c_11965])).
% 27.55/17.72  tff(c_11978, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_11971])).
% 27.55/17.72  tff(c_11980, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_11040, c_11978])).
% 27.55/17.72  tff(c_11981, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_11036])).
% 27.55/17.72  tff(c_32, plain, (![A_26]: (k1_relat_1(A_26)=k1_xboole_0 | k2_relat_1(A_26)!=k1_xboole_0 | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_92])).
% 27.55/17.72  tff(c_10629, plain, (k1_relat_1('#skF_6')=k1_xboole_0 | k2_relat_1('#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_10607, c_32])).
% 27.55/17.72  tff(c_10635, plain, (k2_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_10629])).
% 27.55/17.72  tff(c_10636, plain, (![A_930]: (k2_relat_1(A_930)=k1_xboole_0 | k1_relat_1(A_930)!=k1_xboole_0 | ~v1_relat_1(A_930))), inference(cnfTransformation, [status(thm)], [f_92])).
% 27.55/17.72  tff(c_10639, plain, (k2_relat_1('#skF_6')=k1_xboole_0 | k1_relat_1('#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_10607, c_10636])).
% 27.55/17.72  tff(c_10651, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_10635, c_10639])).
% 27.55/17.72  tff(c_11985, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11981, c_10651])).
% 27.55/17.72  tff(c_12001, plain, (![B_23]: (k7_relat_1('#skF_6', B_23)=k1_xboole_0 | ~r1_xboole_0(B_23, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_11981, c_24])).
% 27.55/17.72  tff(c_12602, plain, (![B_1067]: (k7_relat_1('#skF_6', B_1067)=k1_xboole_0 | ~r1_xboole_0(B_1067, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10607, c_12001])).
% 27.55/17.72  tff(c_12622, plain, (k7_relat_1('#skF_6', '#skF_1'('#skF_4'))=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_50, c_12602])).
% 27.55/17.72  tff(c_12631, plain, (k7_relat_1('#skF_6', '#skF_1'('#skF_4'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_11985, c_12622])).
% 27.55/17.72  tff(c_36, plain, (![B_28, A_27]: (r1_tarski(k1_relat_1(k7_relat_1(B_28, A_27)), A_27) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_96])).
% 27.55/17.72  tff(c_12638, plain, (r1_tarski(k1_relat_1(k1_xboole_0), '#skF_1'('#skF_4')) | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_12631, c_36])).
% 27.55/17.72  tff(c_12647, plain, (r1_tarski(k1_xboole_0, '#skF_1'('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10607, c_30, c_12638])).
% 27.55/17.72  tff(c_16, plain, (![C_17, B_16, A_15]: (k7_relat_1(k7_relat_1(C_17, B_16), A_15)=k7_relat_1(C_17, A_15) | ~r1_tarski(A_15, B_16) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_60])).
% 27.55/17.72  tff(c_12635, plain, (![A_15]: (k7_relat_1(k1_xboole_0, A_15)=k7_relat_1('#skF_6', A_15) | ~r1_tarski(A_15, '#skF_1'('#skF_4')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_12631, c_16])).
% 27.55/17.72  tff(c_13666, plain, (![A_1150]: (k7_relat_1(k1_xboole_0, A_1150)=k7_relat_1('#skF_6', A_1150) | ~r1_tarski(A_1150, '#skF_1'('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_10607, c_12635])).
% 27.55/17.72  tff(c_13677, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k7_relat_1('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_12647, c_13666])).
% 27.55/17.72  tff(c_13691, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10513, c_13677])).
% 27.55/17.72  tff(c_22, plain, (![B_20, A_19]: (r1_xboole_0(k1_relat_1(B_20), A_19) | k9_relat_1(B_20, A_19)!=k1_xboole_0 | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 27.55/17.72  tff(c_12004, plain, (![A_19]: (r1_xboole_0('#skF_4', A_19) | k9_relat_1('#skF_6', A_19)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_11981, c_22])).
% 27.55/17.72  tff(c_12024, plain, (![A_19]: (r1_xboole_0('#skF_4', A_19) | k9_relat_1('#skF_6', A_19)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10607, c_12004])).
% 27.55/17.72  tff(c_10606, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_78, c_10599])).
% 27.55/17.72  tff(c_10675, plain, (v4_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_78, c_10668])).
% 27.55/17.72  tff(c_11033, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_10675, c_11027])).
% 27.55/17.72  tff(c_11039, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10606, c_11033])).
% 27.55/17.72  tff(c_12030, plain, (~v1_partfun1('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_11039])).
% 27.55/17.72  tff(c_12426, plain, (![C_1056, A_1057, B_1058]: (v1_partfun1(C_1056, A_1057) | ~v1_funct_2(C_1056, A_1057, B_1058) | ~v1_funct_1(C_1056) | ~m1_subset_1(C_1056, k1_zfmisc_1(k2_zfmisc_1(A_1057, B_1058))) | v1_xboole_0(B_1058))), inference(cnfTransformation, [status(thm)], [f_144])).
% 27.55/17.72  tff(c_12429, plain, (v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_78, c_12426])).
% 27.55/17.72  tff(c_12435, plain, (v1_partfun1('#skF_7', '#skF_5') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_12429])).
% 27.55/17.72  tff(c_12437, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_12030, c_12435])).
% 27.55/17.72  tff(c_12438, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitRight, [status(thm)], [c_11039])).
% 27.55/17.72  tff(c_12458, plain, (![B_23]: (k7_relat_1('#skF_7', B_23)=k1_xboole_0 | ~r1_xboole_0(B_23, '#skF_5') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_12438, c_24])).
% 27.55/17.72  tff(c_12698, plain, (![B_1070]: (k7_relat_1('#skF_7', B_1070)=k1_xboole_0 | ~r1_xboole_0(B_1070, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_10606, c_12458])).
% 27.55/17.72  tff(c_12723, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0 | k9_relat_1('#skF_6', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_12024, c_12698])).
% 27.55/17.72  tff(c_12998, plain, (k9_relat_1('#skF_6', '#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_12723])).
% 27.55/17.72  tff(c_90, plain, (r1_subset_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_282])).
% 27.55/17.72  tff(c_42, plain, (![A_30, B_31]: (r1_xboole_0(A_30, B_31) | ~r1_subset_1(A_30, B_31) | v1_xboole_0(B_31) | v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_110])).
% 27.55/17.72  tff(c_20, plain, (![B_20, A_19]: (k9_relat_1(B_20, A_19)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_20), A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 27.55/17.72  tff(c_11989, plain, (![A_19]: (k9_relat_1('#skF_6', A_19)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_19) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_11981, c_20])).
% 27.55/17.72  tff(c_12806, plain, (![A_1076]: (k9_relat_1('#skF_6', A_1076)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_1076))), inference(demodulation, [status(thm), theory('equality')], [c_10607, c_11989])).
% 27.55/17.72  tff(c_12813, plain, (![B_31]: (k9_relat_1('#skF_6', B_31)=k1_xboole_0 | ~r1_subset_1('#skF_4', B_31) | v1_xboole_0(B_31) | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_42, c_12806])).
% 27.55/17.72  tff(c_13124, plain, (![B_1106]: (k9_relat_1('#skF_6', B_1106)=k1_xboole_0 | ~r1_subset_1('#skF_4', B_1106) | v1_xboole_0(B_1106))), inference(negUnitSimplification, [status(thm)], [c_98, c_12813])).
% 27.55/17.72  tff(c_13127, plain, (k9_relat_1('#skF_6', '#skF_5')=k1_xboole_0 | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_90, c_13124])).
% 27.55/17.72  tff(c_13131, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_12998, c_13127])).
% 27.55/17.72  tff(c_13133, plain, (k9_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_12723])).
% 27.55/17.72  tff(c_12665, plain, (![A_1069]: (r1_xboole_0('#skF_4', A_1069) | k9_relat_1('#skF_6', A_1069)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10607, c_12004])).
% 27.55/17.72  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 27.55/17.72  tff(c_13188, plain, (![A_1113]: (k3_xboole_0('#skF_4', A_1113)=k1_xboole_0 | k9_relat_1('#skF_6', A_1113)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_12665, c_2])).
% 27.55/17.72  tff(c_13202, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_13133, c_13188])).
% 27.55/17.72  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 27.55/17.72  tff(c_13259, plain, (![A_1116]: (k7_relat_1('#skF_7', A_1116)=k1_xboole_0 | k3_xboole_0(A_1116, '#skF_5')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_12698])).
% 27.55/17.72  tff(c_13277, plain, (![A_1116]: (r1_tarski(k1_relat_1(k1_xboole_0), A_1116) | ~v1_relat_1('#skF_7') | k3_xboole_0(A_1116, '#skF_5')!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_13259, c_36])).
% 27.55/17.72  tff(c_13309, plain, (![A_1116]: (r1_tarski(k1_xboole_0, A_1116) | k3_xboole_0(A_1116, '#skF_5')!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10606, c_30, c_13277])).
% 27.55/17.72  tff(c_13132, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_12723])).
% 27.55/17.72  tff(c_13137, plain, (![A_15]: (k7_relat_1(k1_xboole_0, A_15)=k7_relat_1('#skF_7', A_15) | ~r1_tarski(A_15, '#skF_4') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_13132, c_16])).
% 27.55/17.72  tff(c_13434, plain, (![A_1138]: (k7_relat_1(k1_xboole_0, A_1138)=k7_relat_1('#skF_7', A_1138) | ~r1_tarski(A_1138, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10606, c_13137])).
% 27.55/17.72  tff(c_13438, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k7_relat_1('#skF_7', k1_xboole_0) | k3_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_13309, c_13434])).
% 27.55/17.72  tff(c_13459, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_13202, c_10513, c_13438])).
% 27.55/17.72  tff(c_12503, plain, (![A_1059, B_1060, C_1061]: (k9_subset_1(A_1059, B_1060, C_1061)=k3_xboole_0(B_1060, C_1061) | ~m1_subset_1(C_1061, k1_zfmisc_1(A_1059)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 27.55/17.72  tff(c_12515, plain, (![B_1060]: (k9_subset_1('#skF_2', B_1060, '#skF_5')=k3_xboole_0(B_1060, '#skF_5'))), inference(resolution, [status(thm)], [c_92, c_12503])).
% 27.55/17.72  tff(c_13175, plain, (![D_1107, F_1109, E_1112, A_1110, C_1108, B_1111]: (v1_funct_1(k1_tmap_1(A_1110, B_1111, C_1108, D_1107, E_1112, F_1109)) | ~m1_subset_1(F_1109, k1_zfmisc_1(k2_zfmisc_1(D_1107, B_1111))) | ~v1_funct_2(F_1109, D_1107, B_1111) | ~v1_funct_1(F_1109) | ~m1_subset_1(E_1112, k1_zfmisc_1(k2_zfmisc_1(C_1108, B_1111))) | ~v1_funct_2(E_1112, C_1108, B_1111) | ~v1_funct_1(E_1112) | ~m1_subset_1(D_1107, k1_zfmisc_1(A_1110)) | v1_xboole_0(D_1107) | ~m1_subset_1(C_1108, k1_zfmisc_1(A_1110)) | v1_xboole_0(C_1108) | v1_xboole_0(B_1111) | v1_xboole_0(A_1110))), inference(cnfTransformation, [status(thm)], [f_240])).
% 27.55/17.72  tff(c_13177, plain, (![A_1110, C_1108, E_1112]: (v1_funct_1(k1_tmap_1(A_1110, '#skF_3', C_1108, '#skF_5', E_1112, '#skF_7')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_1112, k1_zfmisc_1(k2_zfmisc_1(C_1108, '#skF_3'))) | ~v1_funct_2(E_1112, C_1108, '#skF_3') | ~v1_funct_1(E_1112) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1110)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1108, k1_zfmisc_1(A_1110)) | v1_xboole_0(C_1108) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1110))), inference(resolution, [status(thm)], [c_78, c_13175])).
% 27.55/17.72  tff(c_13182, plain, (![A_1110, C_1108, E_1112]: (v1_funct_1(k1_tmap_1(A_1110, '#skF_3', C_1108, '#skF_5', E_1112, '#skF_7')) | ~m1_subset_1(E_1112, k1_zfmisc_1(k2_zfmisc_1(C_1108, '#skF_3'))) | ~v1_funct_2(E_1112, C_1108, '#skF_3') | ~v1_funct_1(E_1112) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1110)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1108, k1_zfmisc_1(A_1110)) | v1_xboole_0(C_1108) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1110))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_13177])).
% 27.55/17.72  tff(c_13415, plain, (![A_1135, C_1136, E_1137]: (v1_funct_1(k1_tmap_1(A_1135, '#skF_3', C_1136, '#skF_5', E_1137, '#skF_7')) | ~m1_subset_1(E_1137, k1_zfmisc_1(k2_zfmisc_1(C_1136, '#skF_3'))) | ~v1_funct_2(E_1137, C_1136, '#skF_3') | ~v1_funct_1(E_1137) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1135)) | ~m1_subset_1(C_1136, k1_zfmisc_1(A_1135)) | v1_xboole_0(C_1136) | v1_xboole_0(A_1135))), inference(negUnitSimplification, [status(thm)], [c_100, c_94, c_13182])).
% 27.55/17.72  tff(c_13422, plain, (![A_1135]: (v1_funct_1(k1_tmap_1(A_1135, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1135)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1135)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1135))), inference(resolution, [status(thm)], [c_84, c_13415])).
% 27.55/17.72  tff(c_13432, plain, (![A_1135]: (v1_funct_1(k1_tmap_1(A_1135, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1135)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1135)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1135))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_13422])).
% 27.55/17.72  tff(c_13757, plain, (![A_1158]: (v1_funct_1(k1_tmap_1(A_1158, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1158)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1158)) | v1_xboole_0(A_1158))), inference(negUnitSimplification, [status(thm)], [c_98, c_13432])).
% 27.55/17.72  tff(c_13760, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_92, c_13757])).
% 27.55/17.72  tff(c_13763, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_13760])).
% 27.55/17.72  tff(c_13764, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_102, c_13763])).
% 27.55/17.72  tff(c_12757, plain, (![A_1071, B_1072, C_1073, D_1074]: (k2_partfun1(A_1071, B_1072, C_1073, D_1074)=k7_relat_1(C_1073, D_1074) | ~m1_subset_1(C_1073, k1_zfmisc_1(k2_zfmisc_1(A_1071, B_1072))) | ~v1_funct_1(C_1073))), inference(cnfTransformation, [status(thm)], [f_158])).
% 27.55/17.72  tff(c_12761, plain, (![D_1074]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_1074)=k7_relat_1('#skF_6', D_1074) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_84, c_12757])).
% 27.55/17.72  tff(c_12767, plain, (![D_1074]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_1074)=k7_relat_1('#skF_6', D_1074))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_12761])).
% 27.55/17.72  tff(c_12759, plain, (![D_1074]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_1074)=k7_relat_1('#skF_7', D_1074) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_78, c_12757])).
% 27.55/17.72  tff(c_12764, plain, (![D_1074]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_1074)=k7_relat_1('#skF_7', D_1074))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_12759])).
% 27.55/17.72  tff(c_70, plain, (![E_181, B_178, A_177, D_180, C_179, F_182]: (m1_subset_1(k1_tmap_1(A_177, B_178, C_179, D_180, E_181, F_182), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_177, C_179, D_180), B_178))) | ~m1_subset_1(F_182, k1_zfmisc_1(k2_zfmisc_1(D_180, B_178))) | ~v1_funct_2(F_182, D_180, B_178) | ~v1_funct_1(F_182) | ~m1_subset_1(E_181, k1_zfmisc_1(k2_zfmisc_1(C_179, B_178))) | ~v1_funct_2(E_181, C_179, B_178) | ~v1_funct_1(E_181) | ~m1_subset_1(D_180, k1_zfmisc_1(A_177)) | v1_xboole_0(D_180) | ~m1_subset_1(C_179, k1_zfmisc_1(A_177)) | v1_xboole_0(C_179) | v1_xboole_0(B_178) | v1_xboole_0(A_177))), inference(cnfTransformation, [status(thm)], [f_240])).
% 27.55/17.72  tff(c_13721, plain, (![D_1155, C_1153, E_1156, B_1151, F_1154, A_1152]: (k2_partfun1(k4_subset_1(A_1152, C_1153, D_1155), B_1151, k1_tmap_1(A_1152, B_1151, C_1153, D_1155, E_1156, F_1154), D_1155)=F_1154 | ~m1_subset_1(k1_tmap_1(A_1152, B_1151, C_1153, D_1155, E_1156, F_1154), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1152, C_1153, D_1155), B_1151))) | ~v1_funct_2(k1_tmap_1(A_1152, B_1151, C_1153, D_1155, E_1156, F_1154), k4_subset_1(A_1152, C_1153, D_1155), B_1151) | ~v1_funct_1(k1_tmap_1(A_1152, B_1151, C_1153, D_1155, E_1156, F_1154)) | k2_partfun1(D_1155, B_1151, F_1154, k9_subset_1(A_1152, C_1153, D_1155))!=k2_partfun1(C_1153, B_1151, E_1156, k9_subset_1(A_1152, C_1153, D_1155)) | ~m1_subset_1(F_1154, k1_zfmisc_1(k2_zfmisc_1(D_1155, B_1151))) | ~v1_funct_2(F_1154, D_1155, B_1151) | ~v1_funct_1(F_1154) | ~m1_subset_1(E_1156, k1_zfmisc_1(k2_zfmisc_1(C_1153, B_1151))) | ~v1_funct_2(E_1156, C_1153, B_1151) | ~v1_funct_1(E_1156) | ~m1_subset_1(D_1155, k1_zfmisc_1(A_1152)) | v1_xboole_0(D_1155) | ~m1_subset_1(C_1153, k1_zfmisc_1(A_1152)) | v1_xboole_0(C_1153) | v1_xboole_0(B_1151) | v1_xboole_0(A_1152))), inference(cnfTransformation, [status(thm)], [f_206])).
% 27.55/17.72  tff(c_24839, plain, (![C_1404, E_1408, B_1407, F_1405, D_1403, A_1406]: (k2_partfun1(k4_subset_1(A_1406, C_1404, D_1403), B_1407, k1_tmap_1(A_1406, B_1407, C_1404, D_1403, E_1408, F_1405), D_1403)=F_1405 | ~v1_funct_2(k1_tmap_1(A_1406, B_1407, C_1404, D_1403, E_1408, F_1405), k4_subset_1(A_1406, C_1404, D_1403), B_1407) | ~v1_funct_1(k1_tmap_1(A_1406, B_1407, C_1404, D_1403, E_1408, F_1405)) | k2_partfun1(D_1403, B_1407, F_1405, k9_subset_1(A_1406, C_1404, D_1403))!=k2_partfun1(C_1404, B_1407, E_1408, k9_subset_1(A_1406, C_1404, D_1403)) | ~m1_subset_1(F_1405, k1_zfmisc_1(k2_zfmisc_1(D_1403, B_1407))) | ~v1_funct_2(F_1405, D_1403, B_1407) | ~v1_funct_1(F_1405) | ~m1_subset_1(E_1408, k1_zfmisc_1(k2_zfmisc_1(C_1404, B_1407))) | ~v1_funct_2(E_1408, C_1404, B_1407) | ~v1_funct_1(E_1408) | ~m1_subset_1(D_1403, k1_zfmisc_1(A_1406)) | v1_xboole_0(D_1403) | ~m1_subset_1(C_1404, k1_zfmisc_1(A_1406)) | v1_xboole_0(C_1404) | v1_xboole_0(B_1407) | v1_xboole_0(A_1406))), inference(resolution, [status(thm)], [c_70, c_13721])).
% 27.55/17.72  tff(c_46434, plain, (![D_1615, A_1618, E_1620, F_1617, B_1619, C_1616]: (k2_partfun1(k4_subset_1(A_1618, C_1616, D_1615), B_1619, k1_tmap_1(A_1618, B_1619, C_1616, D_1615, E_1620, F_1617), D_1615)=F_1617 | ~v1_funct_1(k1_tmap_1(A_1618, B_1619, C_1616, D_1615, E_1620, F_1617)) | k2_partfun1(D_1615, B_1619, F_1617, k9_subset_1(A_1618, C_1616, D_1615))!=k2_partfun1(C_1616, B_1619, E_1620, k9_subset_1(A_1618, C_1616, D_1615)) | ~m1_subset_1(F_1617, k1_zfmisc_1(k2_zfmisc_1(D_1615, B_1619))) | ~v1_funct_2(F_1617, D_1615, B_1619) | ~v1_funct_1(F_1617) | ~m1_subset_1(E_1620, k1_zfmisc_1(k2_zfmisc_1(C_1616, B_1619))) | ~v1_funct_2(E_1620, C_1616, B_1619) | ~v1_funct_1(E_1620) | ~m1_subset_1(D_1615, k1_zfmisc_1(A_1618)) | v1_xboole_0(D_1615) | ~m1_subset_1(C_1616, k1_zfmisc_1(A_1618)) | v1_xboole_0(C_1616) | v1_xboole_0(B_1619) | v1_xboole_0(A_1618))), inference(resolution, [status(thm)], [c_72, c_24839])).
% 27.55/17.72  tff(c_46438, plain, (![A_1618, C_1616, E_1620]: (k2_partfun1(k4_subset_1(A_1618, C_1616, '#skF_5'), '#skF_3', k1_tmap_1(A_1618, '#skF_3', C_1616, '#skF_5', E_1620, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1618, '#skF_3', C_1616, '#skF_5', E_1620, '#skF_7')) | k2_partfun1(C_1616, '#skF_3', E_1620, k9_subset_1(A_1618, C_1616, '#skF_5'))!=k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1(A_1618, C_1616, '#skF_5')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_1620, k1_zfmisc_1(k2_zfmisc_1(C_1616, '#skF_3'))) | ~v1_funct_2(E_1620, C_1616, '#skF_3') | ~v1_funct_1(E_1620) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1618)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1616, k1_zfmisc_1(A_1618)) | v1_xboole_0(C_1616) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1618))), inference(resolution, [status(thm)], [c_78, c_46434])).
% 27.55/17.72  tff(c_46444, plain, (![A_1618, C_1616, E_1620]: (k2_partfun1(k4_subset_1(A_1618, C_1616, '#skF_5'), '#skF_3', k1_tmap_1(A_1618, '#skF_3', C_1616, '#skF_5', E_1620, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1618, '#skF_3', C_1616, '#skF_5', E_1620, '#skF_7')) | k2_partfun1(C_1616, '#skF_3', E_1620, k9_subset_1(A_1618, C_1616, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_1618, C_1616, '#skF_5')) | ~m1_subset_1(E_1620, k1_zfmisc_1(k2_zfmisc_1(C_1616, '#skF_3'))) | ~v1_funct_2(E_1620, C_1616, '#skF_3') | ~v1_funct_1(E_1620) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1618)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1616, k1_zfmisc_1(A_1618)) | v1_xboole_0(C_1616) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1618))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_12764, c_46438])).
% 27.55/17.72  tff(c_69925, plain, (![A_1750, C_1751, E_1752]: (k2_partfun1(k4_subset_1(A_1750, C_1751, '#skF_5'), '#skF_3', k1_tmap_1(A_1750, '#skF_3', C_1751, '#skF_5', E_1752, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1750, '#skF_3', C_1751, '#skF_5', E_1752, '#skF_7')) | k2_partfun1(C_1751, '#skF_3', E_1752, k9_subset_1(A_1750, C_1751, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_1750, C_1751, '#skF_5')) | ~m1_subset_1(E_1752, k1_zfmisc_1(k2_zfmisc_1(C_1751, '#skF_3'))) | ~v1_funct_2(E_1752, C_1751, '#skF_3') | ~v1_funct_1(E_1752) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1750)) | ~m1_subset_1(C_1751, k1_zfmisc_1(A_1750)) | v1_xboole_0(C_1751) | v1_xboole_0(A_1750))), inference(negUnitSimplification, [status(thm)], [c_100, c_94, c_46444])).
% 27.55/17.72  tff(c_69932, plain, (![A_1750]: (k2_partfun1(k4_subset_1(A_1750, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_1750, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1750, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1(A_1750, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_1750, '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1750)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1750)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1750))), inference(resolution, [status(thm)], [c_84, c_69925])).
% 27.55/17.72  tff(c_69942, plain, (![A_1750]: (k2_partfun1(k4_subset_1(A_1750, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_1750, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1750, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_1750, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_1750, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1750)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1750)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1750))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_12767, c_69932])).
% 27.55/17.72  tff(c_71990, plain, (![A_1759]: (k2_partfun1(k4_subset_1(A_1759, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_1759, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1759, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_1759, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_1759, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1759)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1759)) | v1_xboole_0(A_1759))), inference(negUnitSimplification, [status(thm)], [c_98, c_69942])).
% 27.55/17.72  tff(c_1191, plain, (![C_355, A_356, B_357]: (v1_relat_1(C_355) | ~m1_subset_1(C_355, k1_zfmisc_1(k2_zfmisc_1(A_356, B_357))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 27.55/17.72  tff(c_1199, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_84, c_1191])).
% 27.55/17.72  tff(c_150, plain, (![C_251, A_252, B_253]: (v1_relat_1(C_251) | ~m1_subset_1(C_251, k1_zfmisc_1(k2_zfmisc_1(A_252, B_253))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 27.55/17.72  tff(c_158, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_84, c_150])).
% 27.55/17.72  tff(c_190, plain, (![A_257]: (k1_relat_1(A_257)=k1_xboole_0 | k2_relat_1(A_257)!=k1_xboole_0 | ~v1_relat_1(A_257))), inference(cnfTransformation, [status(thm)], [f_92])).
% 27.55/17.72  tff(c_200, plain, (k1_relat_1('#skF_6')=k1_xboole_0 | k2_relat_1('#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_158, c_190])).
% 27.55/17.72  tff(c_203, plain, (k2_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_200])).
% 27.55/17.72  tff(c_231, plain, (![A_263]: (k2_relat_1(A_263)=k1_xboole_0 | k1_relat_1(A_263)!=k1_xboole_0 | ~v1_relat_1(A_263))), inference(cnfTransformation, [status(thm)], [f_92])).
% 27.55/17.72  tff(c_234, plain, (k2_relat_1('#skF_6')=k1_xboole_0 | k1_relat_1('#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_158, c_231])).
% 27.55/17.72  tff(c_243, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_203, c_234])).
% 27.55/17.72  tff(c_130, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_126])).
% 27.55/17.72  tff(c_397, plain, (![A_285, B_286]: (k7_relat_1(A_285, B_286)=k1_xboole_0 | ~r1_xboole_0(B_286, k1_relat_1(A_285)) | ~v1_relat_1(A_285))), inference(cnfTransformation, [status(thm)], [f_77])).
% 27.55/17.72  tff(c_563, plain, (![A_302]: (k7_relat_1(A_302, '#skF_1'(k1_relat_1(A_302)))=k1_xboole_0 | ~v1_relat_1(A_302) | k1_relat_1(A_302)=k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_397])).
% 27.55/17.72  tff(c_579, plain, (![A_302]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_302) | ~v1_relat_1(A_302) | k1_relat_1(A_302)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_563, c_14])).
% 27.55/17.72  tff(c_595, plain, (![A_303]: (~v1_relat_1(A_303) | ~v1_relat_1(A_303) | k1_relat_1(A_303)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_130, c_579])).
% 27.55/17.72  tff(c_597, plain, (~v1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_158, c_595])).
% 27.55/17.72  tff(c_604, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_158, c_597])).
% 27.55/17.72  tff(c_606, plain, $false, inference(negUnitSimplification, [status(thm)], [c_243, c_604])).
% 27.55/17.72  tff(c_608, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_200])).
% 27.55/17.72  tff(c_607, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_200])).
% 27.55/17.72  tff(c_667, plain, (![A_309]: (k9_relat_1(A_309, k1_relat_1(A_309))=k2_relat_1(A_309) | ~v1_relat_1(A_309))), inference(cnfTransformation, [status(thm)], [f_64])).
% 27.55/17.72  tff(c_676, plain, (k9_relat_1('#skF_6', k1_xboole_0)=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_607, c_667])).
% 27.55/17.72  tff(c_683, plain, (k9_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_158, c_608, c_676])).
% 27.55/17.72  tff(c_613, plain, (k7_relat_1('#skF_6', k1_xboole_0)='#skF_6' | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_607, c_38])).
% 27.55/17.72  tff(c_617, plain, (k7_relat_1('#skF_6', k1_xboole_0)='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_158, c_613])).
% 27.55/17.72  tff(c_974, plain, (![B_336, A_337]: (r1_xboole_0(k1_relat_1(B_336), A_337) | k9_relat_1(B_336, A_337)!=k1_xboole_0 | ~v1_relat_1(B_336))), inference(cnfTransformation, [status(thm)], [f_70])).
% 27.55/17.72  tff(c_997, plain, (![A_337]: (r1_xboole_0(k1_xboole_0, A_337) | k9_relat_1('#skF_6', A_337)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_607, c_974])).
% 27.55/17.72  tff(c_1009, plain, (![A_338]: (r1_xboole_0(k1_xboole_0, A_338) | k9_relat_1('#skF_6', A_338)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_158, c_997])).
% 27.55/17.72  tff(c_859, plain, (![A_329, B_330]: (k7_relat_1(A_329, B_330)=k1_xboole_0 | ~r1_xboole_0(B_330, k1_relat_1(A_329)) | ~v1_relat_1(A_329))), inference(cnfTransformation, [status(thm)], [f_77])).
% 27.55/17.72  tff(c_862, plain, (![B_330]: (k7_relat_1('#skF_6', B_330)=k1_xboole_0 | ~r1_xboole_0(B_330, k1_xboole_0) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_607, c_859])).
% 27.55/17.72  tff(c_875, plain, (![B_330]: (k7_relat_1('#skF_6', B_330)=k1_xboole_0 | ~r1_xboole_0(B_330, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_862])).
% 27.55/17.72  tff(c_1013, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0 | k9_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_1009, c_875])).
% 27.55/17.72  tff(c_1032, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_683, c_617, c_1013])).
% 27.55/17.72  tff(c_1064, plain, (~v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1032, c_130])).
% 27.55/17.72  tff(c_1071, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_158, c_1064])).
% 27.55/17.72  tff(c_1072, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_126])).
% 27.55/17.72  tff(c_1219, plain, (![C_358, A_359, B_360]: (v4_relat_1(C_358, A_359) | ~m1_subset_1(C_358, k1_zfmisc_1(k2_zfmisc_1(A_359, B_360))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 27.55/17.72  tff(c_1227, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_84, c_1219])).
% 27.55/17.72  tff(c_1624, plain, (![B_392, A_393]: (k1_relat_1(B_392)=A_393 | ~v1_partfun1(B_392, A_393) | ~v4_relat_1(B_392, A_393) | ~v1_relat_1(B_392))), inference(cnfTransformation, [status(thm)], [f_152])).
% 27.55/17.72  tff(c_1627, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1227, c_1624])).
% 27.55/17.72  tff(c_1633, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1199, c_1627])).
% 27.55/17.72  tff(c_1637, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_1633])).
% 27.55/17.72  tff(c_2547, plain, (![C_460, A_461, B_462]: (v1_partfun1(C_460, A_461) | ~v1_funct_2(C_460, A_461, B_462) | ~v1_funct_1(C_460) | ~m1_subset_1(C_460, k1_zfmisc_1(k2_zfmisc_1(A_461, B_462))) | v1_xboole_0(B_462))), inference(cnfTransformation, [status(thm)], [f_144])).
% 27.55/17.72  tff(c_2553, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_84, c_2547])).
% 27.55/17.72  tff(c_2560, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_2553])).
% 27.55/17.72  tff(c_2562, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_1637, c_2560])).
% 27.55/17.72  tff(c_2563, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_1633])).
% 27.55/17.72  tff(c_34, plain, (![A_26]: (k2_relat_1(A_26)=k1_xboole_0 | k1_relat_1(A_26)!=k1_xboole_0 | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_92])).
% 27.55/17.72  tff(c_1214, plain, (k2_relat_1('#skF_6')=k1_xboole_0 | k1_relat_1('#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_1199, c_34])).
% 27.55/17.72  tff(c_1218, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1214])).
% 27.55/17.72  tff(c_2567, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2563, c_1218])).
% 27.55/17.72  tff(c_2580, plain, (![B_23]: (k7_relat_1('#skF_6', B_23)=k1_xboole_0 | ~r1_xboole_0(B_23, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2563, c_24])).
% 27.55/17.72  tff(c_3186, plain, (![B_501]: (k7_relat_1('#skF_6', B_501)=k1_xboole_0 | ~r1_xboole_0(B_501, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1199, c_2580])).
% 27.55/17.72  tff(c_3206, plain, (k7_relat_1('#skF_6', '#skF_1'('#skF_4'))=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_50, c_3186])).
% 27.55/17.72  tff(c_3215, plain, (k7_relat_1('#skF_6', '#skF_1'('#skF_4'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_2567, c_3206])).
% 27.55/17.72  tff(c_3231, plain, (r1_tarski(k1_relat_1(k1_xboole_0), '#skF_1'('#skF_4')) | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3215, c_36])).
% 27.55/17.72  tff(c_3240, plain, (r1_tarski(k1_xboole_0, '#skF_1'('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1199, c_30, c_3231])).
% 27.55/17.72  tff(c_3228, plain, (![A_15]: (k7_relat_1(k1_xboole_0, A_15)=k7_relat_1('#skF_6', A_15) | ~r1_tarski(A_15, '#skF_1'('#skF_4')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3215, c_16])).
% 27.55/17.72  tff(c_4186, plain, (![A_573]: (k7_relat_1(k1_xboole_0, A_573)=k7_relat_1('#skF_6', A_573) | ~r1_tarski(A_573, '#skF_1'('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1199, c_3228])).
% 27.55/17.72  tff(c_4197, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k7_relat_1('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_3240, c_4186])).
% 27.55/17.72  tff(c_4211, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1072, c_4197])).
% 27.55/17.72  tff(c_1198, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_78, c_1191])).
% 27.55/17.72  tff(c_2571, plain, (![A_19]: (r1_xboole_0('#skF_4', A_19) | k9_relat_1('#skF_6', A_19)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2563, c_22])).
% 27.55/17.72  tff(c_2596, plain, (![A_19]: (r1_xboole_0('#skF_4', A_19) | k9_relat_1('#skF_6', A_19)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1199, c_2571])).
% 27.55/17.72  tff(c_1226, plain, (v4_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_78, c_1219])).
% 27.55/17.72  tff(c_1630, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_1226, c_1624])).
% 27.55/17.72  tff(c_1636, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1198, c_1630])).
% 27.55/17.72  tff(c_2612, plain, (~v1_partfun1('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_1636])).
% 27.55/17.72  tff(c_2997, plain, (![C_489, A_490, B_491]: (v1_partfun1(C_489, A_490) | ~v1_funct_2(C_489, A_490, B_491) | ~v1_funct_1(C_489) | ~m1_subset_1(C_489, k1_zfmisc_1(k2_zfmisc_1(A_490, B_491))) | v1_xboole_0(B_491))), inference(cnfTransformation, [status(thm)], [f_144])).
% 27.55/17.72  tff(c_3000, plain, (v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_78, c_2997])).
% 27.55/17.72  tff(c_3006, plain, (v1_partfun1('#skF_7', '#skF_5') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_3000])).
% 27.55/17.72  tff(c_3008, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_2612, c_3006])).
% 27.55/17.72  tff(c_3009, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitRight, [status(thm)], [c_1636])).
% 27.55/17.72  tff(c_3026, plain, (![B_23]: (k7_relat_1('#skF_7', B_23)=k1_xboole_0 | ~r1_xboole_0(B_23, '#skF_5') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_3009, c_24])).
% 27.55/17.72  tff(c_3318, plain, (![B_505]: (k7_relat_1('#skF_7', B_505)=k1_xboole_0 | ~r1_xboole_0(B_505, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1198, c_3026])).
% 27.55/17.72  tff(c_3347, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0 | k9_relat_1('#skF_6', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_2596, c_3318])).
% 27.55/17.72  tff(c_3696, plain, (k9_relat_1('#skF_6', '#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3347])).
% 27.55/17.72  tff(c_2574, plain, (![A_19]: (k9_relat_1('#skF_6', A_19)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_19) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2563, c_20])).
% 27.55/17.72  tff(c_3394, plain, (![A_510]: (k9_relat_1('#skF_6', A_510)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_510))), inference(demodulation, [status(thm), theory('equality')], [c_1199, c_2574])).
% 27.55/17.72  tff(c_3401, plain, (![B_31]: (k9_relat_1('#skF_6', B_31)=k1_xboole_0 | ~r1_subset_1('#skF_4', B_31) | v1_xboole_0(B_31) | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_42, c_3394])).
% 27.55/17.72  tff(c_3766, plain, (![B_549]: (k9_relat_1('#skF_6', B_549)=k1_xboole_0 | ~r1_subset_1('#skF_4', B_549) | v1_xboole_0(B_549))), inference(negUnitSimplification, [status(thm)], [c_98, c_3401])).
% 27.55/17.72  tff(c_3772, plain, (k9_relat_1('#skF_6', '#skF_5')=k1_xboole_0 | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_90, c_3766])).
% 27.55/17.72  tff(c_3777, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_3696, c_3772])).
% 27.55/17.72  tff(c_3778, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_3347])).
% 27.55/17.72  tff(c_3803, plain, (r1_tarski(k1_relat_1(k1_xboole_0), '#skF_4') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_3778, c_36])).
% 27.55/17.72  tff(c_3816, plain, (r1_tarski(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1198, c_30, c_3803])).
% 27.55/17.72  tff(c_3800, plain, (![A_15]: (k7_relat_1(k1_xboole_0, A_15)=k7_relat_1('#skF_7', A_15) | ~r1_tarski(A_15, '#skF_4') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_3778, c_16])).
% 27.55/17.72  tff(c_3932, plain, (![A_561]: (k7_relat_1(k1_xboole_0, A_561)=k7_relat_1('#skF_7', A_561) | ~r1_tarski(A_561, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1198, c_3800])).
% 27.55/17.72  tff(c_3935, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k7_relat_1('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_3816, c_3932])).
% 27.55/17.72  tff(c_3956, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1072, c_3935])).
% 27.55/17.72  tff(c_3779, plain, (k9_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_3347])).
% 27.55/17.72  tff(c_3285, plain, (![A_504]: (r1_xboole_0('#skF_4', A_504) | k9_relat_1('#skF_6', A_504)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1199, c_2571])).
% 27.55/17.72  tff(c_3317, plain, (![A_504]: (k3_xboole_0('#skF_4', A_504)=k1_xboole_0 | k9_relat_1('#skF_6', A_504)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_3285, c_2])).
% 27.55/17.72  tff(c_3838, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3779, c_3317])).
% 27.55/17.72  tff(c_3359, plain, (![A_506, B_507, C_508, D_509]: (k2_partfun1(A_506, B_507, C_508, D_509)=k7_relat_1(C_508, D_509) | ~m1_subset_1(C_508, k1_zfmisc_1(k2_zfmisc_1(A_506, B_507))) | ~v1_funct_1(C_508))), inference(cnfTransformation, [status(thm)], [f_158])).
% 27.55/17.72  tff(c_3361, plain, (![D_509]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_509)=k7_relat_1('#skF_7', D_509) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_78, c_3359])).
% 27.55/17.72  tff(c_3366, plain, (![D_509]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_509)=k7_relat_1('#skF_7', D_509))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_3361])).
% 27.55/17.72  tff(c_3363, plain, (![D_509]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_509)=k7_relat_1('#skF_6', D_509) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_84, c_3359])).
% 27.55/17.72  tff(c_3369, plain, (![D_509]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_509)=k7_relat_1('#skF_6', D_509))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_3363])).
% 27.55/17.72  tff(c_3074, plain, (![A_492, B_493, C_494]: (k9_subset_1(A_492, B_493, C_494)=k3_xboole_0(B_493, C_494) | ~m1_subset_1(C_494, k1_zfmisc_1(A_492)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 27.55/17.72  tff(c_3086, plain, (![B_493]: (k9_subset_1('#skF_2', B_493, '#skF_5')=k3_xboole_0(B_493, '#skF_5'))), inference(resolution, [status(thm)], [c_92, c_3074])).
% 27.55/17.72  tff(c_76, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')!='#skF_7' | k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')!='#skF_6' | k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_282])).
% 27.55/17.72  tff(c_129, plain, (k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_76])).
% 27.55/17.72  tff(c_3163, plain, (k2_partfun1('#skF_5', '#skF_3', '#skF_7', k3_xboole_0('#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_3086, c_3086, c_129])).
% 27.55/17.72  tff(c_7149, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4211, c_3956, c_3838, c_3838, c_3366, c_3369, c_3163])).
% 27.55/17.72  tff(c_7150, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1214])).
% 27.55/17.72  tff(c_1215, plain, (k1_relat_1('#skF_6')=k1_xboole_0 | k2_relat_1('#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_1199, c_32])).
% 27.55/17.72  tff(c_7157, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7150, c_1215])).
% 27.55/17.72  tff(c_7161, plain, (k9_relat_1('#skF_6', k1_xboole_0)=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_7157, c_18])).
% 27.55/17.72  tff(c_7168, plain, (k9_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1199, c_7150, c_7161])).
% 27.55/17.72  tff(c_7164, plain, (k7_relat_1('#skF_6', k1_xboole_0)='#skF_6' | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_7157, c_38])).
% 27.55/17.72  tff(c_7170, plain, (k7_relat_1('#skF_6', k1_xboole_0)='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1199, c_7164])).
% 27.55/17.72  tff(c_7448, plain, (![B_664, A_665]: (r1_xboole_0(k1_relat_1(B_664), A_665) | k9_relat_1(B_664, A_665)!=k1_xboole_0 | ~v1_relat_1(B_664))), inference(cnfTransformation, [status(thm)], [f_70])).
% 27.55/17.72  tff(c_7472, plain, (![A_665]: (r1_xboole_0(k1_xboole_0, A_665) | k9_relat_1('#skF_6', A_665)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_7157, c_7448])).
% 27.55/17.72  tff(c_7487, plain, (![A_666]: (r1_xboole_0(k1_xboole_0, A_666) | k9_relat_1('#skF_6', A_666)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1199, c_7472])).
% 27.55/17.72  tff(c_7305, plain, (![A_656, B_657]: (k7_relat_1(A_656, B_657)=k1_xboole_0 | ~r1_xboole_0(B_657, k1_relat_1(A_656)) | ~v1_relat_1(A_656))), inference(cnfTransformation, [status(thm)], [f_77])).
% 27.55/17.72  tff(c_7308, plain, (![B_657]: (k7_relat_1('#skF_6', B_657)=k1_xboole_0 | ~r1_xboole_0(B_657, k1_xboole_0) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_7157, c_7305])).
% 27.55/17.72  tff(c_7321, plain, (![B_657]: (k7_relat_1('#skF_6', B_657)=k1_xboole_0 | ~r1_xboole_0(B_657, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_1199, c_7308])).
% 27.55/17.72  tff(c_7495, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0 | k9_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_7487, c_7321])).
% 27.55/17.72  tff(c_7514, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_7168, c_7170, c_7495])).
% 27.55/17.72  tff(c_1073, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_126])).
% 27.55/17.72  tff(c_1171, plain, (![B_352, A_353]: (r1_tarski(k1_relat_1(k7_relat_1(B_352, A_353)), A_353) | ~v1_relat_1(B_352))), inference(cnfTransformation, [status(thm)], [f_96])).
% 27.55/17.72  tff(c_1174, plain, (r1_tarski(k1_relat_1(k1_xboole_0), k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1072, c_1171])).
% 27.55/17.72  tff(c_1179, plain, (r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1073, c_30, c_1174])).
% 27.55/17.72  tff(c_1151, plain, (![B_349, A_350]: (~r1_xboole_0(B_349, A_350) | ~r1_tarski(B_349, A_350) | v1_xboole_0(B_349))), inference(cnfTransformation, [status(thm)], [f_37])).
% 27.55/17.72  tff(c_7260, plain, (![A_653, B_654]: (~r1_tarski(A_653, B_654) | v1_xboole_0(A_653) | k3_xboole_0(A_653, B_654)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_1151])).
% 27.55/17.72  tff(c_7275, plain, (v1_xboole_0(k1_xboole_0) | k3_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_1179, c_7260])).
% 27.55/17.72  tff(c_7277, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7275])).
% 27.55/17.72  tff(c_7532, plain, (k3_xboole_0('#skF_6', '#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_7514, c_7514, c_7514, c_7277])).
% 27.55/17.72  tff(c_7537, plain, (k9_relat_1('#skF_6', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_7514, c_7514, c_7168])).
% 27.55/17.72  tff(c_7518, plain, (![A_666]: (k3_xboole_0(k1_xboole_0, A_666)=k1_xboole_0 | k9_relat_1('#skF_6', A_666)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_7487, c_2])).
% 27.55/17.72  tff(c_7898, plain, (![A_694]: (k3_xboole_0('#skF_6', A_694)='#skF_6' | k9_relat_1('#skF_6', A_694)!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_7514, c_7514, c_7514, c_7518])).
% 27.55/17.72  tff(c_7901, plain, (k3_xboole_0('#skF_6', '#skF_6')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_7537, c_7898])).
% 27.55/17.72  tff(c_7909, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7532, c_7901])).
% 27.55/17.72  tff(c_7911, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_7275])).
% 27.55/17.72  tff(c_7918, plain, (![A_695, B_696]: (k7_relat_1(A_695, B_696)=k1_xboole_0 | ~r1_xboole_0(B_696, k1_relat_1(A_695)) | ~v1_relat_1(A_695))), inference(cnfTransformation, [status(thm)], [f_77])).
% 27.55/17.72  tff(c_7921, plain, (![B_696]: (k7_relat_1('#skF_6', B_696)=k1_xboole_0 | ~r1_xboole_0(B_696, k1_xboole_0) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_7157, c_7918])).
% 27.55/17.72  tff(c_7951, plain, (![B_698]: (k7_relat_1('#skF_6', B_698)=k1_xboole_0 | ~r1_xboole_0(B_698, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_1199, c_7921])).
% 27.55/17.72  tff(c_8008, plain, (![A_700]: (k7_relat_1('#skF_6', A_700)=k1_xboole_0 | k3_xboole_0(A_700, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_7951])).
% 27.55/17.72  tff(c_8017, plain, (k1_xboole_0='#skF_6' | k3_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_8008, c_7170])).
% 27.55/17.72  tff(c_8043, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_7911, c_8017])).
% 27.55/17.72  tff(c_8084, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_8043, c_8043, c_30])).
% 27.55/17.72  tff(c_7191, plain, (![C_642, A_643, B_644]: (v4_relat_1(C_642, A_643) | ~m1_subset_1(C_642, k1_zfmisc_1(k2_zfmisc_1(A_643, B_644))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 27.55/17.72  tff(c_7199, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_84, c_7191])).
% 27.55/17.72  tff(c_8499, plain, (![B_732, A_733]: (k1_relat_1(B_732)=A_733 | ~v1_partfun1(B_732, A_733) | ~v4_relat_1(B_732, A_733) | ~v1_relat_1(B_732))), inference(cnfTransformation, [status(thm)], [f_152])).
% 27.55/17.72  tff(c_8502, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_7199, c_8499])).
% 27.55/17.72  tff(c_8508, plain, ('#skF_6'='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1199, c_8084, c_8502])).
% 27.55/17.72  tff(c_8512, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_8508])).
% 27.55/17.72  tff(c_9179, plain, (![C_786, A_787, B_788]: (v1_partfun1(C_786, A_787) | ~v1_funct_2(C_786, A_787, B_788) | ~v1_funct_1(C_786) | ~m1_subset_1(C_786, k1_zfmisc_1(k2_zfmisc_1(A_787, B_788))) | v1_xboole_0(B_788))), inference(cnfTransformation, [status(thm)], [f_144])).
% 27.55/17.72  tff(c_9185, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_84, c_9179])).
% 27.55/17.72  tff(c_9192, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_9185])).
% 27.55/17.72  tff(c_9194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_8512, c_9192])).
% 27.55/17.72  tff(c_9195, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_8508])).
% 27.55/17.72  tff(c_7910, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_7275])).
% 27.55/17.72  tff(c_8063, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_8043, c_7910])).
% 27.55/17.72  tff(c_9226, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9195, c_8063])).
% 27.55/17.72  tff(c_9236, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_9226])).
% 27.55/17.72  tff(c_9237, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_76])).
% 27.55/17.72  tff(c_10578, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')!='#skF_7'), inference(splitLeft, [status(thm)], [c_9237])).
% 27.55/17.72  tff(c_72001, plain, (~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_71990, c_10578])).
% 27.55/17.72  tff(c_72015, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_92, c_13691, c_13459, c_13202, c_13202, c_12515, c_12515, c_13764, c_72001])).
% 27.55/17.72  tff(c_72017, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_72015])).
% 27.55/17.72  tff(c_72019, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_10629])).
% 27.55/17.72  tff(c_72018, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_10629])).
% 27.55/17.72  tff(c_72023, plain, (k9_relat_1('#skF_6', k1_xboole_0)=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_72018, c_18])).
% 27.55/17.72  tff(c_72030, plain, (k9_relat_1('#skF_6', k1_xboole_0)=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10607, c_72023])).
% 27.55/17.72  tff(c_72052, plain, (k9_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_72019, c_72030])).
% 27.55/17.72  tff(c_72026, plain, (k7_relat_1('#skF_6', k1_xboole_0)='#skF_6' | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_72018, c_38])).
% 27.55/17.72  tff(c_72032, plain, (k7_relat_1('#skF_6', k1_xboole_0)='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_10607, c_72026])).
% 27.55/17.72  tff(c_72134, plain, (![B_1771, A_1772]: (r1_xboole_0(k1_relat_1(B_1771), A_1772) | k9_relat_1(B_1771, A_1772)!=k1_xboole_0 | ~v1_relat_1(B_1771))), inference(cnfTransformation, [status(thm)], [f_70])).
% 27.55/17.72  tff(c_72143, plain, (![A_1772]: (r1_xboole_0(k1_xboole_0, A_1772) | k9_relat_1('#skF_6', A_1772)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_72018, c_72134])).
% 27.55/17.72  tff(c_72150, plain, (![A_1772]: (r1_xboole_0(k1_xboole_0, A_1772) | k9_relat_1('#skF_6', A_1772)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10607, c_72143])).
% 27.55/17.72  tff(c_72201, plain, (![A_1776, B_1777]: (k7_relat_1(A_1776, B_1777)=k1_xboole_0 | ~r1_xboole_0(B_1777, k1_relat_1(A_1776)) | ~v1_relat_1(A_1776))), inference(cnfTransformation, [status(thm)], [f_77])).
% 27.55/17.72  tff(c_72216, plain, (![B_1777]: (k7_relat_1('#skF_6', B_1777)=k1_xboole_0 | ~r1_xboole_0(B_1777, k1_xboole_0) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_72018, c_72201])).
% 27.55/17.72  tff(c_72268, plain, (![B_1779]: (k7_relat_1('#skF_6', B_1779)=k1_xboole_0 | ~r1_xboole_0(B_1779, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10607, c_72216])).
% 27.55/17.72  tff(c_72272, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0 | k9_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_72150, c_72268])).
% 27.55/17.72  tff(c_72291, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_72052, c_72032, c_72272])).
% 27.55/17.72  tff(c_72325, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_72291, c_72291, c_30])).
% 27.55/17.72  tff(c_72089, plain, (![C_1763, A_1764, B_1765]: (v4_relat_1(C_1763, A_1764) | ~m1_subset_1(C_1763, k1_zfmisc_1(k2_zfmisc_1(A_1764, B_1765))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 27.55/17.72  tff(c_72097, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_84, c_72089])).
% 27.55/17.72  tff(c_72759, plain, (![B_1815, A_1816]: (k1_relat_1(B_1815)=A_1816 | ~v1_partfun1(B_1815, A_1816) | ~v4_relat_1(B_1815, A_1816) | ~v1_relat_1(B_1815))), inference(cnfTransformation, [status(thm)], [f_152])).
% 27.55/17.72  tff(c_72762, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_72097, c_72759])).
% 27.55/17.72  tff(c_72768, plain, ('#skF_6'='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10607, c_72325, c_72762])).
% 27.55/17.72  tff(c_72772, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_72768])).
% 27.55/17.72  tff(c_73539, plain, (![C_1862, A_1863, B_1864]: (v1_partfun1(C_1862, A_1863) | ~v1_funct_2(C_1862, A_1863, B_1864) | ~v1_funct_1(C_1862) | ~m1_subset_1(C_1862, k1_zfmisc_1(k2_zfmisc_1(A_1863, B_1864))) | v1_xboole_0(B_1864))), inference(cnfTransformation, [status(thm)], [f_144])).
% 27.55/17.72  tff(c_73545, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_84, c_73539])).
% 27.55/17.72  tff(c_73552, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_73545])).
% 27.55/17.72  tff(c_73554, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_72772, c_73552])).
% 27.55/17.72  tff(c_73555, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_72768])).
% 27.55/17.72  tff(c_72310, plain, (k9_relat_1('#skF_6', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_72291, c_72291, c_72052])).
% 27.55/17.72  tff(c_10579, plain, (![B_923, A_924]: (r1_tarski(k1_relat_1(k7_relat_1(B_923, A_924)), A_924) | ~v1_relat_1(B_923))), inference(cnfTransformation, [status(thm)], [f_96])).
% 27.55/17.72  tff(c_10582, plain, (r1_tarski(k1_relat_1(k1_xboole_0), k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10513, c_10579])).
% 27.55/17.72  tff(c_10587, plain, (r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10514, c_30, c_10582])).
% 27.55/17.72  tff(c_72317, plain, (r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_72291, c_72291, c_10587])).
% 27.55/17.72  tff(c_72176, plain, (![A_1774]: (r1_xboole_0(k1_xboole_0, A_1774) | k9_relat_1('#skF_6', A_1774)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10607, c_72143])).
% 27.55/17.72  tff(c_6, plain, (![B_4, A_3]: (~r1_xboole_0(B_4, A_3) | ~r1_tarski(B_4, A_3) | v1_xboole_0(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 27.55/17.72  tff(c_72183, plain, (![A_1774]: (~r1_tarski(k1_xboole_0, A_1774) | v1_xboole_0(k1_xboole_0) | k9_relat_1('#skF_6', A_1774)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_72176, c_6])).
% 27.55/17.72  tff(c_72608, plain, (![A_1774]: (~r1_tarski('#skF_6', A_1774) | v1_xboole_0('#skF_6') | k9_relat_1('#skF_6', A_1774)!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_72291, c_72291, c_72291, c_72183])).
% 27.55/17.72  tff(c_72610, plain, (![A_1802]: (~r1_tarski('#skF_6', A_1802) | k9_relat_1('#skF_6', A_1802)!='#skF_6')), inference(splitLeft, [status(thm)], [c_72608])).
% 27.55/17.72  tff(c_72619, plain, (k9_relat_1('#skF_6', '#skF_6')!='#skF_6'), inference(resolution, [status(thm)], [c_72317, c_72610])).
% 27.55/17.72  tff(c_72625, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72310, c_72619])).
% 27.55/17.72  tff(c_72626, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_72608])).
% 27.55/17.72  tff(c_73562, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_73555, c_72626])).
% 27.55/17.72  tff(c_73597, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_73562])).
% 27.55/17.72  tff(c_73598, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_9237])).
% 27.55/17.72  tff(c_73691, plain, (![C_1875, A_1876, B_1877]: (v4_relat_1(C_1875, A_1876) | ~m1_subset_1(C_1875, k1_zfmisc_1(k2_zfmisc_1(A_1876, B_1877))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 27.55/17.72  tff(c_73699, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_84, c_73691])).
% 27.55/17.72  tff(c_74272, plain, (![B_1924, A_1925]: (k1_relat_1(B_1924)=A_1925 | ~v1_partfun1(B_1924, A_1925) | ~v4_relat_1(B_1924, A_1925) | ~v1_relat_1(B_1924))), inference(cnfTransformation, [status(thm)], [f_152])).
% 27.55/17.72  tff(c_74275, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_73699, c_74272])).
% 27.55/17.72  tff(c_74281, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_73641, c_74275])).
% 27.55/17.72  tff(c_74285, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_74281])).
% 27.55/17.72  tff(c_74843, plain, (![C_1960, A_1961, B_1962]: (v1_partfun1(C_1960, A_1961) | ~v1_funct_2(C_1960, A_1961, B_1962) | ~v1_funct_1(C_1960) | ~m1_subset_1(C_1960, k1_zfmisc_1(k2_zfmisc_1(A_1961, B_1962))) | v1_xboole_0(B_1962))), inference(cnfTransformation, [status(thm)], [f_144])).
% 27.55/17.72  tff(c_74849, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_84, c_74843])).
% 27.55/17.72  tff(c_74856, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_74849])).
% 27.55/17.72  tff(c_74858, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_74285, c_74856])).
% 27.55/17.72  tff(c_74859, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_74281])).
% 27.55/17.72  tff(c_73668, plain, (k1_relat_1('#skF_6')=k1_xboole_0 | k2_relat_1('#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_73641, c_32])).
% 27.55/17.72  tff(c_73671, plain, (k2_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_73668])).
% 27.55/17.72  tff(c_73667, plain, (k2_relat_1('#skF_6')=k1_xboole_0 | k1_relat_1('#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_73641, c_34])).
% 27.55/17.72  tff(c_73672, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_73671, c_73667])).
% 27.55/17.72  tff(c_74864, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_74859, c_73672])).
% 27.55/17.72  tff(c_74868, plain, (![B_23]: (k7_relat_1('#skF_6', B_23)=k1_xboole_0 | ~r1_xboole_0(B_23, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_74859, c_24])).
% 27.55/17.72  tff(c_75470, plain, (![B_1995]: (k7_relat_1('#skF_6', B_1995)=k1_xboole_0 | ~r1_xboole_0(B_1995, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_73641, c_74868])).
% 27.55/17.72  tff(c_75498, plain, (k7_relat_1('#skF_6', '#skF_1'('#skF_4'))=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_50, c_75470])).
% 27.55/17.72  tff(c_75510, plain, (k7_relat_1('#skF_6', '#skF_1'('#skF_4'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_74864, c_75498])).
% 27.55/17.72  tff(c_75517, plain, (r1_tarski(k1_relat_1(k1_xboole_0), '#skF_1'('#skF_4')) | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_75510, c_36])).
% 27.55/17.72  tff(c_75526, plain, (r1_tarski(k1_xboole_0, '#skF_1'('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_73641, c_30, c_75517])).
% 27.55/17.72  tff(c_75514, plain, (![A_15]: (k7_relat_1(k1_xboole_0, A_15)=k7_relat_1('#skF_6', A_15) | ~r1_tarski(A_15, '#skF_1'('#skF_4')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_75510, c_16])).
% 27.55/17.72  tff(c_76547, plain, (![A_2082]: (k7_relat_1(k1_xboole_0, A_2082)=k7_relat_1('#skF_6', A_2082) | ~r1_tarski(A_2082, '#skF_1'('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_73641, c_75514])).
% 27.55/17.72  tff(c_76558, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k7_relat_1('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_75526, c_76547])).
% 27.55/17.72  tff(c_76572, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10513, c_76558])).
% 27.55/17.72  tff(c_74871, plain, (![A_19]: (r1_xboole_0('#skF_4', A_19) | k9_relat_1('#skF_6', A_19)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_74859, c_22])).
% 27.55/17.72  tff(c_75438, plain, (![A_1994]: (r1_xboole_0('#skF_4', A_1994) | k9_relat_1('#skF_6', A_1994)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_73641, c_74871])).
% 27.55/17.72  tff(c_73640, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_78, c_73633])).
% 27.55/17.72  tff(c_73698, plain, (v4_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_78, c_73691])).
% 27.55/17.72  tff(c_74278, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_73698, c_74272])).
% 27.55/17.72  tff(c_74284, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_73640, c_74278])).
% 27.55/17.72  tff(c_74985, plain, (~v1_partfun1('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_74284])).
% 27.55/17.72  tff(c_75209, plain, (![C_1980, A_1981, B_1982]: (v1_partfun1(C_1980, A_1981) | ~v1_funct_2(C_1980, A_1981, B_1982) | ~v1_funct_1(C_1980) | ~m1_subset_1(C_1980, k1_zfmisc_1(k2_zfmisc_1(A_1981, B_1982))) | v1_xboole_0(B_1982))), inference(cnfTransformation, [status(thm)], [f_144])).
% 27.55/17.72  tff(c_75212, plain, (v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_78, c_75209])).
% 27.55/17.72  tff(c_75218, plain, (v1_partfun1('#skF_7', '#skF_5') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_75212])).
% 27.55/17.72  tff(c_75220, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_74985, c_75218])).
% 27.55/17.72  tff(c_75221, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitRight, [status(thm)], [c_74284])).
% 27.55/17.72  tff(c_75230, plain, (![B_23]: (k7_relat_1('#skF_7', B_23)=k1_xboole_0 | ~r1_xboole_0(B_23, '#skF_5') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_75221, c_24])).
% 27.55/17.72  tff(c_75255, plain, (![B_23]: (k7_relat_1('#skF_7', B_23)=k1_xboole_0 | ~r1_xboole_0(B_23, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_73640, c_75230])).
% 27.55/17.72  tff(c_75460, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0 | k9_relat_1('#skF_6', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_75438, c_75255])).
% 27.55/17.72  tff(c_75596, plain, (k9_relat_1('#skF_6', '#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_75460])).
% 27.55/17.72  tff(c_74883, plain, (![A_19]: (k9_relat_1('#skF_6', A_19)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_19) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_74859, c_20])).
% 27.55/17.72  tff(c_75546, plain, (![A_1997]: (k9_relat_1('#skF_6', A_1997)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_1997))), inference(demodulation, [status(thm), theory('equality')], [c_73641, c_74883])).
% 27.55/17.72  tff(c_75553, plain, (![B_31]: (k9_relat_1('#skF_6', B_31)=k1_xboole_0 | ~r1_subset_1('#skF_4', B_31) | v1_xboole_0(B_31) | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_42, c_75546])).
% 27.55/17.72  tff(c_75963, plain, (![B_2037]: (k9_relat_1('#skF_6', B_2037)=k1_xboole_0 | ~r1_subset_1('#skF_4', B_2037) | v1_xboole_0(B_2037))), inference(negUnitSimplification, [status(thm)], [c_98, c_75553])).
% 27.55/17.72  tff(c_75969, plain, (k9_relat_1('#skF_6', '#skF_5')=k1_xboole_0 | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_90, c_75963])).
% 27.55/17.72  tff(c_75974, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_75596, c_75969])).
% 27.55/17.72  tff(c_75976, plain, (k9_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_75460])).
% 27.55/17.72  tff(c_76291, plain, (![A_2066]: (k3_xboole_0('#skF_4', A_2066)=k1_xboole_0 | k9_relat_1('#skF_6', A_2066)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_75438, c_2])).
% 27.55/17.72  tff(c_76306, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_75976, c_76291])).
% 27.55/17.72  tff(c_74189, plain, (![A_1915, B_1916, C_1917]: (k9_subset_1(A_1915, B_1916, C_1917)=k3_xboole_0(B_1916, C_1917) | ~m1_subset_1(C_1917, k1_zfmisc_1(A_1915)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 27.55/17.72  tff(c_74201, plain, (![B_1916]: (k9_subset_1('#skF_2', B_1916, '#skF_5')=k3_xboole_0(B_1916, '#skF_5'))), inference(resolution, [status(thm)], [c_92, c_74189])).
% 27.55/17.72  tff(c_75327, plain, (![B_1989]: (k7_relat_1('#skF_7', B_1989)=k1_xboole_0 | ~r1_xboole_0(B_1989, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_73640, c_75230])).
% 27.55/17.72  tff(c_76147, plain, (![A_2055]: (k7_relat_1('#skF_7', A_2055)=k1_xboole_0 | k3_xboole_0(A_2055, '#skF_5')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_75327])).
% 27.55/17.72  tff(c_76165, plain, (![A_2055]: (r1_tarski(k1_relat_1(k1_xboole_0), A_2055) | ~v1_relat_1('#skF_7') | k3_xboole_0(A_2055, '#skF_5')!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_76147, c_36])).
% 27.55/17.72  tff(c_76195, plain, (![A_2055]: (r1_tarski(k1_xboole_0, A_2055) | k3_xboole_0(A_2055, '#skF_5')!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_73640, c_30, c_76165])).
% 27.55/17.72  tff(c_75975, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_75460])).
% 27.55/17.72  tff(c_75980, plain, (![A_15]: (k7_relat_1(k1_xboole_0, A_15)=k7_relat_1('#skF_7', A_15) | ~r1_tarski(A_15, '#skF_4') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_75975, c_16])).
% 27.55/17.72  tff(c_76376, plain, (![A_2076]: (k7_relat_1(k1_xboole_0, A_2076)=k7_relat_1('#skF_7', A_2076) | ~r1_tarski(A_2076, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_73640, c_75980])).
% 27.55/17.72  tff(c_76380, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k7_relat_1('#skF_7', k1_xboole_0) | k3_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_76195, c_76376])).
% 27.55/17.72  tff(c_76401, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_76306, c_10513, c_76380])).
% 27.55/17.72  tff(c_75285, plain, (![A_1983, B_1984, C_1985, D_1986]: (k2_partfun1(A_1983, B_1984, C_1985, D_1986)=k7_relat_1(C_1985, D_1986) | ~m1_subset_1(C_1985, k1_zfmisc_1(k2_zfmisc_1(A_1983, B_1984))) | ~v1_funct_1(C_1985))), inference(cnfTransformation, [status(thm)], [f_158])).
% 27.55/17.72  tff(c_75287, plain, (![D_1986]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_1986)=k7_relat_1('#skF_7', D_1986) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_78, c_75285])).
% 27.55/17.72  tff(c_75292, plain, (![D_1986]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_1986)=k7_relat_1('#skF_7', D_1986))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_75287])).
% 27.55/17.72  tff(c_75289, plain, (![D_1986]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_1986)=k7_relat_1('#skF_6', D_1986) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_84, c_75285])).
% 27.55/17.72  tff(c_75295, plain, (![D_1986]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_1986)=k7_relat_1('#skF_6', D_1986))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_75289])).
% 27.55/17.72  tff(c_75579, plain, (![E_2005, B_2004, D_2000, C_2001, F_2002, A_2003]: (v1_funct_1(k1_tmap_1(A_2003, B_2004, C_2001, D_2000, E_2005, F_2002)) | ~m1_subset_1(F_2002, k1_zfmisc_1(k2_zfmisc_1(D_2000, B_2004))) | ~v1_funct_2(F_2002, D_2000, B_2004) | ~v1_funct_1(F_2002) | ~m1_subset_1(E_2005, k1_zfmisc_1(k2_zfmisc_1(C_2001, B_2004))) | ~v1_funct_2(E_2005, C_2001, B_2004) | ~v1_funct_1(E_2005) | ~m1_subset_1(D_2000, k1_zfmisc_1(A_2003)) | v1_xboole_0(D_2000) | ~m1_subset_1(C_2001, k1_zfmisc_1(A_2003)) | v1_xboole_0(C_2001) | v1_xboole_0(B_2004) | v1_xboole_0(A_2003))), inference(cnfTransformation, [status(thm)], [f_240])).
% 27.55/17.72  tff(c_75581, plain, (![A_2003, C_2001, E_2005]: (v1_funct_1(k1_tmap_1(A_2003, '#skF_3', C_2001, '#skF_5', E_2005, '#skF_7')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_2005, k1_zfmisc_1(k2_zfmisc_1(C_2001, '#skF_3'))) | ~v1_funct_2(E_2005, C_2001, '#skF_3') | ~v1_funct_1(E_2005) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2003)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_2001, k1_zfmisc_1(A_2003)) | v1_xboole_0(C_2001) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2003))), inference(resolution, [status(thm)], [c_78, c_75579])).
% 27.55/17.72  tff(c_75586, plain, (![A_2003, C_2001, E_2005]: (v1_funct_1(k1_tmap_1(A_2003, '#skF_3', C_2001, '#skF_5', E_2005, '#skF_7')) | ~m1_subset_1(E_2005, k1_zfmisc_1(k2_zfmisc_1(C_2001, '#skF_3'))) | ~v1_funct_2(E_2005, C_2001, '#skF_3') | ~v1_funct_1(E_2005) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2003)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_2001, k1_zfmisc_1(A_2003)) | v1_xboole_0(C_2001) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2003))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_75581])).
% 27.55/17.72  tff(c_76436, plain, (![A_2077, C_2078, E_2079]: (v1_funct_1(k1_tmap_1(A_2077, '#skF_3', C_2078, '#skF_5', E_2079, '#skF_7')) | ~m1_subset_1(E_2079, k1_zfmisc_1(k2_zfmisc_1(C_2078, '#skF_3'))) | ~v1_funct_2(E_2079, C_2078, '#skF_3') | ~v1_funct_1(E_2079) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2077)) | ~m1_subset_1(C_2078, k1_zfmisc_1(A_2077)) | v1_xboole_0(C_2078) | v1_xboole_0(A_2077))), inference(negUnitSimplification, [status(thm)], [c_100, c_94, c_75586])).
% 27.55/17.72  tff(c_76443, plain, (![A_2077]: (v1_funct_1(k1_tmap_1(A_2077, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2077)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2077)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_2077))), inference(resolution, [status(thm)], [c_84, c_76436])).
% 27.55/17.72  tff(c_76453, plain, (![A_2077]: (v1_funct_1(k1_tmap_1(A_2077, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2077)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2077)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_2077))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_76443])).
% 27.55/17.72  tff(c_76865, plain, (![A_2099]: (v1_funct_1(k1_tmap_1(A_2099, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2099)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2099)) | v1_xboole_0(A_2099))), inference(negUnitSimplification, [status(thm)], [c_98, c_76453])).
% 27.55/17.72  tff(c_76868, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_92, c_76865])).
% 27.55/17.72  tff(c_76871, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_76868])).
% 27.55/17.72  tff(c_76872, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_102, c_76871])).
% 27.55/17.72  tff(c_76350, plain, (![B_2069, A_2070, E_2074, D_2073, F_2072, C_2071]: (k2_partfun1(k4_subset_1(A_2070, C_2071, D_2073), B_2069, k1_tmap_1(A_2070, B_2069, C_2071, D_2073, E_2074, F_2072), C_2071)=E_2074 | ~m1_subset_1(k1_tmap_1(A_2070, B_2069, C_2071, D_2073, E_2074, F_2072), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_2070, C_2071, D_2073), B_2069))) | ~v1_funct_2(k1_tmap_1(A_2070, B_2069, C_2071, D_2073, E_2074, F_2072), k4_subset_1(A_2070, C_2071, D_2073), B_2069) | ~v1_funct_1(k1_tmap_1(A_2070, B_2069, C_2071, D_2073, E_2074, F_2072)) | k2_partfun1(D_2073, B_2069, F_2072, k9_subset_1(A_2070, C_2071, D_2073))!=k2_partfun1(C_2071, B_2069, E_2074, k9_subset_1(A_2070, C_2071, D_2073)) | ~m1_subset_1(F_2072, k1_zfmisc_1(k2_zfmisc_1(D_2073, B_2069))) | ~v1_funct_2(F_2072, D_2073, B_2069) | ~v1_funct_1(F_2072) | ~m1_subset_1(E_2074, k1_zfmisc_1(k2_zfmisc_1(C_2071, B_2069))) | ~v1_funct_2(E_2074, C_2071, B_2069) | ~v1_funct_1(E_2074) | ~m1_subset_1(D_2073, k1_zfmisc_1(A_2070)) | v1_xboole_0(D_2073) | ~m1_subset_1(C_2071, k1_zfmisc_1(A_2070)) | v1_xboole_0(C_2071) | v1_xboole_0(B_2069) | v1_xboole_0(A_2070))), inference(cnfTransformation, [status(thm)], [f_206])).
% 27.55/17.72  tff(c_87574, plain, (![D_2325, B_2329, C_2326, E_2330, F_2327, A_2328]: (k2_partfun1(k4_subset_1(A_2328, C_2326, D_2325), B_2329, k1_tmap_1(A_2328, B_2329, C_2326, D_2325, E_2330, F_2327), C_2326)=E_2330 | ~v1_funct_2(k1_tmap_1(A_2328, B_2329, C_2326, D_2325, E_2330, F_2327), k4_subset_1(A_2328, C_2326, D_2325), B_2329) | ~v1_funct_1(k1_tmap_1(A_2328, B_2329, C_2326, D_2325, E_2330, F_2327)) | k2_partfun1(D_2325, B_2329, F_2327, k9_subset_1(A_2328, C_2326, D_2325))!=k2_partfun1(C_2326, B_2329, E_2330, k9_subset_1(A_2328, C_2326, D_2325)) | ~m1_subset_1(F_2327, k1_zfmisc_1(k2_zfmisc_1(D_2325, B_2329))) | ~v1_funct_2(F_2327, D_2325, B_2329) | ~v1_funct_1(F_2327) | ~m1_subset_1(E_2330, k1_zfmisc_1(k2_zfmisc_1(C_2326, B_2329))) | ~v1_funct_2(E_2330, C_2326, B_2329) | ~v1_funct_1(E_2330) | ~m1_subset_1(D_2325, k1_zfmisc_1(A_2328)) | v1_xboole_0(D_2325) | ~m1_subset_1(C_2326, k1_zfmisc_1(A_2328)) | v1_xboole_0(C_2326) | v1_xboole_0(B_2329) | v1_xboole_0(A_2328))), inference(resolution, [status(thm)], [c_70, c_76350])).
% 27.55/17.72  tff(c_107524, plain, (![F_2541, A_2542, C_2540, B_2543, D_2539, E_2544]: (k2_partfun1(k4_subset_1(A_2542, C_2540, D_2539), B_2543, k1_tmap_1(A_2542, B_2543, C_2540, D_2539, E_2544, F_2541), C_2540)=E_2544 | ~v1_funct_1(k1_tmap_1(A_2542, B_2543, C_2540, D_2539, E_2544, F_2541)) | k2_partfun1(D_2539, B_2543, F_2541, k9_subset_1(A_2542, C_2540, D_2539))!=k2_partfun1(C_2540, B_2543, E_2544, k9_subset_1(A_2542, C_2540, D_2539)) | ~m1_subset_1(F_2541, k1_zfmisc_1(k2_zfmisc_1(D_2539, B_2543))) | ~v1_funct_2(F_2541, D_2539, B_2543) | ~v1_funct_1(F_2541) | ~m1_subset_1(E_2544, k1_zfmisc_1(k2_zfmisc_1(C_2540, B_2543))) | ~v1_funct_2(E_2544, C_2540, B_2543) | ~v1_funct_1(E_2544) | ~m1_subset_1(D_2539, k1_zfmisc_1(A_2542)) | v1_xboole_0(D_2539) | ~m1_subset_1(C_2540, k1_zfmisc_1(A_2542)) | v1_xboole_0(C_2540) | v1_xboole_0(B_2543) | v1_xboole_0(A_2542))), inference(resolution, [status(thm)], [c_72, c_87574])).
% 27.55/17.72  tff(c_107528, plain, (![A_2542, C_2540, E_2544]: (k2_partfun1(k4_subset_1(A_2542, C_2540, '#skF_5'), '#skF_3', k1_tmap_1(A_2542, '#skF_3', C_2540, '#skF_5', E_2544, '#skF_7'), C_2540)=E_2544 | ~v1_funct_1(k1_tmap_1(A_2542, '#skF_3', C_2540, '#skF_5', E_2544, '#skF_7')) | k2_partfun1(C_2540, '#skF_3', E_2544, k9_subset_1(A_2542, C_2540, '#skF_5'))!=k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1(A_2542, C_2540, '#skF_5')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_2544, k1_zfmisc_1(k2_zfmisc_1(C_2540, '#skF_3'))) | ~v1_funct_2(E_2544, C_2540, '#skF_3') | ~v1_funct_1(E_2544) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2542)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_2540, k1_zfmisc_1(A_2542)) | v1_xboole_0(C_2540) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2542))), inference(resolution, [status(thm)], [c_78, c_107524])).
% 27.55/17.72  tff(c_107534, plain, (![A_2542, C_2540, E_2544]: (k2_partfun1(k4_subset_1(A_2542, C_2540, '#skF_5'), '#skF_3', k1_tmap_1(A_2542, '#skF_3', C_2540, '#skF_5', E_2544, '#skF_7'), C_2540)=E_2544 | ~v1_funct_1(k1_tmap_1(A_2542, '#skF_3', C_2540, '#skF_5', E_2544, '#skF_7')) | k2_partfun1(C_2540, '#skF_3', E_2544, k9_subset_1(A_2542, C_2540, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_2542, C_2540, '#skF_5')) | ~m1_subset_1(E_2544, k1_zfmisc_1(k2_zfmisc_1(C_2540, '#skF_3'))) | ~v1_funct_2(E_2544, C_2540, '#skF_3') | ~v1_funct_1(E_2544) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2542)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_2540, k1_zfmisc_1(A_2542)) | v1_xboole_0(C_2540) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2542))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_75292, c_107528])).
% 27.55/17.72  tff(c_119693, plain, (![A_2647, C_2648, E_2649]: (k2_partfun1(k4_subset_1(A_2647, C_2648, '#skF_5'), '#skF_3', k1_tmap_1(A_2647, '#skF_3', C_2648, '#skF_5', E_2649, '#skF_7'), C_2648)=E_2649 | ~v1_funct_1(k1_tmap_1(A_2647, '#skF_3', C_2648, '#skF_5', E_2649, '#skF_7')) | k2_partfun1(C_2648, '#skF_3', E_2649, k9_subset_1(A_2647, C_2648, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_2647, C_2648, '#skF_5')) | ~m1_subset_1(E_2649, k1_zfmisc_1(k2_zfmisc_1(C_2648, '#skF_3'))) | ~v1_funct_2(E_2649, C_2648, '#skF_3') | ~v1_funct_1(E_2649) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2647)) | ~m1_subset_1(C_2648, k1_zfmisc_1(A_2647)) | v1_xboole_0(C_2648) | v1_xboole_0(A_2647))), inference(negUnitSimplification, [status(thm)], [c_100, c_94, c_107534])).
% 27.55/17.72  tff(c_119700, plain, (![A_2647]: (k2_partfun1(k4_subset_1(A_2647, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_2647, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_2647, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1(A_2647, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_2647, '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2647)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2647)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_2647))), inference(resolution, [status(thm)], [c_84, c_119693])).
% 27.55/17.72  tff(c_119710, plain, (![A_2647]: (k2_partfun1(k4_subset_1(A_2647, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_2647, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_2647, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_2647, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_2647, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2647)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2647)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_2647))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_75295, c_119700])).
% 27.55/17.72  tff(c_124663, plain, (![A_2666]: (k2_partfun1(k4_subset_1(A_2666, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_2666, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_2666, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_2666, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_2666, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2666)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2666)) | v1_xboole_0(A_2666))), inference(negUnitSimplification, [status(thm)], [c_98, c_119710])).
% 27.55/17.72  tff(c_73599, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')='#skF_7'), inference(splitRight, [status(thm)], [c_9237])).
% 27.55/17.72  tff(c_76576, plain, (![A_2084, D_2086, B_2083, G_2087, C_2085]: (k1_tmap_1(A_2084, B_2083, C_2085, D_2086, k2_partfun1(k4_subset_1(A_2084, C_2085, D_2086), B_2083, G_2087, C_2085), k2_partfun1(k4_subset_1(A_2084, C_2085, D_2086), B_2083, G_2087, D_2086))=G_2087 | ~m1_subset_1(G_2087, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_2084, C_2085, D_2086), B_2083))) | ~v1_funct_2(G_2087, k4_subset_1(A_2084, C_2085, D_2086), B_2083) | ~v1_funct_1(G_2087) | k2_partfun1(D_2086, B_2083, k2_partfun1(k4_subset_1(A_2084, C_2085, D_2086), B_2083, G_2087, D_2086), k9_subset_1(A_2084, C_2085, D_2086))!=k2_partfun1(C_2085, B_2083, k2_partfun1(k4_subset_1(A_2084, C_2085, D_2086), B_2083, G_2087, C_2085), k9_subset_1(A_2084, C_2085, D_2086)) | ~m1_subset_1(k2_partfun1(k4_subset_1(A_2084, C_2085, D_2086), B_2083, G_2087, D_2086), k1_zfmisc_1(k2_zfmisc_1(D_2086, B_2083))) | ~v1_funct_2(k2_partfun1(k4_subset_1(A_2084, C_2085, D_2086), B_2083, G_2087, D_2086), D_2086, B_2083) | ~v1_funct_1(k2_partfun1(k4_subset_1(A_2084, C_2085, D_2086), B_2083, G_2087, D_2086)) | ~m1_subset_1(k2_partfun1(k4_subset_1(A_2084, C_2085, D_2086), B_2083, G_2087, C_2085), k1_zfmisc_1(k2_zfmisc_1(C_2085, B_2083))) | ~v1_funct_2(k2_partfun1(k4_subset_1(A_2084, C_2085, D_2086), B_2083, G_2087, C_2085), C_2085, B_2083) | ~v1_funct_1(k2_partfun1(k4_subset_1(A_2084, C_2085, D_2086), B_2083, G_2087, C_2085)) | ~m1_subset_1(D_2086, k1_zfmisc_1(A_2084)) | v1_xboole_0(D_2086) | ~m1_subset_1(C_2085, k1_zfmisc_1(A_2084)) | v1_xboole_0(C_2085) | v1_xboole_0(B_2083) | v1_xboole_0(A_2084))), inference(cnfTransformation, [status(thm)], [f_206])).
% 27.55/17.72  tff(c_76578, plain, (k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5'))=k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7') | ~m1_subset_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3'))) | ~v1_funct_2(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3') | ~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k2_partfun1('#skF_5', '#skF_3', k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5'), k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), k9_subset_1('#skF_2', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3'))) | ~v1_funct_2(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5'), '#skF_5', '#skF_3') | ~v1_funct_1(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')) | ~m1_subset_1(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_73599, c_76576])).
% 27.55/17.72  tff(c_76580, plain, (k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), '#skF_7')=k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7') | ~m1_subset_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3'))) | ~v1_funct_2(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3') | ~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k2_partfun1('#skF_4', '#skF_3', k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), k1_xboole_0)!=k1_xboole_0 | ~m1_subset_1(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')) | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_92, c_82, c_73599, c_80, c_73599, c_78, c_76401, c_76306, c_76306, c_75292, c_73599, c_74201, c_74201, c_73599, c_76578])).
% 27.55/17.72  tff(c_76581, plain, (k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), '#skF_7')=k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7') | ~m1_subset_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3'))) | ~v1_funct_2(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3') | ~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k2_partfun1('#skF_4', '#skF_3', k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), k1_xboole_0)!=k1_xboole_0 | ~m1_subset_1(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_102, c_100, c_98, c_94, c_76580])).
% 27.55/17.72  tff(c_80703, plain, (k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), '#skF_7')=k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7') | ~m1_subset_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3'))) | ~v1_funct_2(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3') | k2_partfun1('#skF_4', '#skF_3', k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), k1_xboole_0)!=k1_xboole_0 | ~m1_subset_1(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_76872, c_76581])).
% 27.55/17.72  tff(c_80704, plain, (~v1_funct_1(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'))), inference(splitLeft, [status(thm)], [c_80703])).
% 27.55/17.72  tff(c_124672, plain, (~v1_funct_1('#skF_6') | ~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_124663, c_80704])).
% 27.55/17.72  tff(c_124685, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_92, c_76572, c_76401, c_76306, c_76306, c_74201, c_74201, c_76872, c_88, c_124672])).
% 27.55/17.72  tff(c_124687, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_124685])).
% 27.55/17.72  tff(c_124688, plain, (~v1_funct_2(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), '#skF_4', '#skF_3') | ~m1_subset_1(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | k2_partfun1('#skF_4', '#skF_3', k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), k1_xboole_0)!=k1_xboole_0 | ~v1_funct_2(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3') | ~m1_subset_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3'))) | k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), '#skF_7')=k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_80703])).
% 27.55/17.72  tff(c_126446, plain, (~m1_subset_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3')))), inference(splitLeft, [status(thm)], [c_124688])).
% 27.55/17.72  tff(c_127144, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3'))) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_70, c_126446])).
% 27.55/17.72  tff(c_127147, plain, (v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_92, c_88, c_86, c_84, c_82, c_80, c_78, c_127144])).
% 27.55/17.72  tff(c_127149, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_100, c_98, c_94, c_127147])).
% 27.55/17.72  tff(c_127151, plain, (m1_subset_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3')))), inference(splitRight, [status(thm)], [c_124688])).
% 27.55/17.72  tff(c_68, plain, (![A_50, D_162, F_174, B_114, E_170, C_146]: (k2_partfun1(k4_subset_1(A_50, C_146, D_162), B_114, k1_tmap_1(A_50, B_114, C_146, D_162, E_170, F_174), C_146)=E_170 | ~m1_subset_1(k1_tmap_1(A_50, B_114, C_146, D_162, E_170, F_174), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_50, C_146, D_162), B_114))) | ~v1_funct_2(k1_tmap_1(A_50, B_114, C_146, D_162, E_170, F_174), k4_subset_1(A_50, C_146, D_162), B_114) | ~v1_funct_1(k1_tmap_1(A_50, B_114, C_146, D_162, E_170, F_174)) | k2_partfun1(D_162, B_114, F_174, k9_subset_1(A_50, C_146, D_162))!=k2_partfun1(C_146, B_114, E_170, k9_subset_1(A_50, C_146, D_162)) | ~m1_subset_1(F_174, k1_zfmisc_1(k2_zfmisc_1(D_162, B_114))) | ~v1_funct_2(F_174, D_162, B_114) | ~v1_funct_1(F_174) | ~m1_subset_1(E_170, k1_zfmisc_1(k2_zfmisc_1(C_146, B_114))) | ~v1_funct_2(E_170, C_146, B_114) | ~v1_funct_1(E_170) | ~m1_subset_1(D_162, k1_zfmisc_1(A_50)) | v1_xboole_0(D_162) | ~m1_subset_1(C_146, k1_zfmisc_1(A_50)) | v1_xboole_0(C_146) | v1_xboole_0(B_114) | v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_206])).
% 27.55/17.72  tff(c_127852, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | ~v1_funct_2(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3') | ~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3'))) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_127151, c_68])).
% 27.55/17.72  tff(c_127884, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | ~v1_funct_2(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3') | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_92, c_88, c_86, c_84, c_82, c_80, c_78, c_76572, c_76306, c_74201, c_76401, c_76306, c_74201, c_75292, c_75295, c_76872, c_127852])).
% 27.55/17.72  tff(c_127885, plain, (~v1_funct_2(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_102, c_100, c_98, c_94, c_73598, c_127884])).
% 27.55/17.72  tff(c_127987, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3'))) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_72, c_127885])).
% 27.55/17.72  tff(c_127990, plain, (v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_92, c_88, c_86, c_84, c_82, c_80, c_78, c_127987])).
% 27.55/17.72  tff(c_127992, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_100, c_98, c_94, c_127990])).
% 27.55/17.72  tff(c_127993, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_73668])).
% 27.55/17.72  tff(c_128015, plain, (k7_relat_1('#skF_6', k1_xboole_0)='#skF_6' | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_127993, c_38])).
% 27.55/17.72  tff(c_128021, plain, (k7_relat_1('#skF_6', k1_xboole_0)='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_73641, c_128015])).
% 27.55/17.72  tff(c_128166, plain, (![B_2714, A_2715]: (r1_xboole_0(k1_relat_1(B_2714), A_2715) | k9_relat_1(B_2714, A_2715)!=k1_xboole_0 | ~v1_relat_1(B_2714))), inference(cnfTransformation, [status(thm)], [f_70])).
% 27.55/17.72  tff(c_128178, plain, (![A_2715]: (r1_xboole_0(k1_xboole_0, A_2715) | k9_relat_1(k1_xboole_0, A_2715)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_128166])).
% 27.55/17.72  tff(c_128184, plain, (![A_2715]: (r1_xboole_0(k1_xboole_0, A_2715) | k9_relat_1(k1_xboole_0, A_2715)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10514, c_128178])).
% 27.55/17.72  tff(c_128185, plain, (![A_2716, B_2717]: (k7_relat_1(A_2716, B_2717)=k1_xboole_0 | ~r1_xboole_0(B_2717, k1_relat_1(A_2716)) | ~v1_relat_1(A_2716))), inference(cnfTransformation, [status(thm)], [f_77])).
% 27.55/17.72  tff(c_128196, plain, (![B_2717]: (k7_relat_1('#skF_6', B_2717)=k1_xboole_0 | ~r1_xboole_0(B_2717, k1_xboole_0) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_127993, c_128185])).
% 27.55/17.72  tff(c_128259, plain, (![B_2720]: (k7_relat_1('#skF_6', B_2720)=k1_xboole_0 | ~r1_xboole_0(B_2720, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_73641, c_128196])).
% 27.55/17.72  tff(c_128263, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0 | k9_relat_1(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_128184, c_128259])).
% 27.55/17.72  tff(c_128282, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_128008, c_128021, c_128263])).
% 27.55/17.72  tff(c_73600, plain, (![B_1865, A_1866]: (r1_tarski(k1_relat_1(k7_relat_1(B_1865, A_1866)), A_1866) | ~v1_relat_1(B_1865))), inference(cnfTransformation, [status(thm)], [f_96])).
% 27.55/17.72  tff(c_73603, plain, (r1_tarski(k1_relat_1(k1_xboole_0), k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10513, c_73600])).
% 27.55/17.72  tff(c_73608, plain, (r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10514, c_30, c_73603])).
% 27.55/17.72  tff(c_73624, plain, (![B_1868, A_1869]: (~r1_xboole_0(B_1868, A_1869) | ~r1_tarski(B_1868, A_1869) | v1_xboole_0(B_1868))), inference(cnfTransformation, [status(thm)], [f_37])).
% 27.55/17.72  tff(c_128142, plain, (![A_2712, B_2713]: (~r1_tarski(A_2712, B_2713) | v1_xboole_0(A_2712) | k3_xboole_0(A_2712, B_2713)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_73624])).
% 27.55/17.72  tff(c_128161, plain, (v1_xboole_0(k1_xboole_0) | k3_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_73608, c_128142])).
% 27.55/17.72  tff(c_128163, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_128161])).
% 27.55/17.72  tff(c_128324, plain, (k3_xboole_0('#skF_6', '#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_128282, c_128282, c_128282, c_128163])).
% 27.55/17.72  tff(c_127994, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_73668])).
% 27.55/17.72  tff(c_128012, plain, (k9_relat_1('#skF_6', k1_xboole_0)=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_127993, c_18])).
% 27.55/17.72  tff(c_128019, plain, (k9_relat_1('#skF_6', k1_xboole_0)=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_73641, c_128012])).
% 27.55/17.72  tff(c_128047, plain, (k9_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_127994, c_128019])).
% 27.55/17.72  tff(c_128328, plain, (k9_relat_1('#skF_6', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_128282, c_128282, c_128047])).
% 27.55/17.72  tff(c_128216, plain, (![A_2718]: (r1_xboole_0(k1_xboole_0, A_2718) | k9_relat_1(k1_xboole_0, A_2718)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10514, c_128178])).
% 27.55/17.72  tff(c_128229, plain, (![A_2718]: (k3_xboole_0(k1_xboole_0, A_2718)=k1_xboole_0 | k9_relat_1(k1_xboole_0, A_2718)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_128216, c_2])).
% 27.55/17.72  tff(c_128572, plain, (![A_2743]: (k3_xboole_0('#skF_6', A_2743)='#skF_6' | k9_relat_1('#skF_6', A_2743)!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_128282, c_128282, c_128282, c_128282, c_128229])).
% 27.55/17.72  tff(c_128575, plain, (k3_xboole_0('#skF_6', '#skF_6')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_128328, c_128572])).
% 27.55/17.72  tff(c_128583, plain, $false, inference(negUnitSimplification, [status(thm)], [c_128324, c_128575])).
% 27.55/17.72  tff(c_128585, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_128161])).
% 27.55/17.72  tff(c_128605, plain, (![A_2746, B_2747]: (k7_relat_1(A_2746, B_2747)=k1_xboole_0 | ~r1_xboole_0(B_2747, k1_relat_1(A_2746)) | ~v1_relat_1(A_2746))), inference(cnfTransformation, [status(thm)], [f_77])).
% 27.55/17.72  tff(c_128612, plain, (![B_2747]: (k7_relat_1('#skF_6', B_2747)=k1_xboole_0 | ~r1_xboole_0(B_2747, k1_xboole_0) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_127993, c_128605])).
% 27.55/17.72  tff(c_128649, plain, (![B_2749]: (k7_relat_1('#skF_6', B_2749)=k1_xboole_0 | ~r1_xboole_0(B_2749, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_73641, c_128612])).
% 27.55/17.72  tff(c_128718, plain, (![A_2752]: (k7_relat_1('#skF_6', A_2752)=k1_xboole_0 | k3_xboole_0(A_2752, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_128649])).
% 27.55/17.72  tff(c_128727, plain, (k1_xboole_0='#skF_6' | k3_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_128718, c_128021])).
% 27.55/17.72  tff(c_128753, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_128585, c_128727])).
% 27.55/17.72  tff(c_128781, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_128753, c_127993])).
% 27.55/17.72  tff(c_128052, plain, (![C_2700, A_2701, B_2702]: (v4_relat_1(C_2700, A_2701) | ~m1_subset_1(C_2700, k1_zfmisc_1(k2_zfmisc_1(A_2701, B_2702))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 27.55/17.72  tff(c_128060, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_84, c_128052])).
% 27.55/17.72  tff(c_129018, plain, (![B_2773, A_2774]: (k1_relat_1(B_2773)=A_2774 | ~v1_partfun1(B_2773, A_2774) | ~v4_relat_1(B_2773, A_2774) | ~v1_relat_1(B_2773))), inference(cnfTransformation, [status(thm)], [f_152])).
% 27.55/17.72  tff(c_129021, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_128060, c_129018])).
% 27.55/17.72  tff(c_129027, plain, ('#skF_6'='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_73641, c_128781, c_129021])).
% 27.55/17.72  tff(c_129031, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_129027])).
% 27.55/17.72  tff(c_129734, plain, (![C_2819, A_2820, B_2821]: (v1_partfun1(C_2819, A_2820) | ~v1_funct_2(C_2819, A_2820, B_2821) | ~v1_funct_1(C_2819) | ~m1_subset_1(C_2819, k1_zfmisc_1(k2_zfmisc_1(A_2820, B_2821))) | v1_xboole_0(B_2821))), inference(cnfTransformation, [status(thm)], [f_144])).
% 27.55/17.72  tff(c_129740, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_84, c_129734])).
% 27.55/17.72  tff(c_129747, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_129740])).
% 27.55/17.72  tff(c_129749, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_129031, c_129747])).
% 27.55/17.72  tff(c_129750, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_129027])).
% 27.55/17.72  tff(c_128584, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_128161])).
% 27.55/17.72  tff(c_128773, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_128753, c_128584])).
% 27.55/17.72  tff(c_129771, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_129750, c_128773])).
% 27.55/17.72  tff(c_129784, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_129771])).
% 27.55/17.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.55/17.72  
% 27.55/17.72  Inference rules
% 27.55/17.72  ----------------------
% 27.55/17.72  #Ref     : 0
% 27.55/17.72  #Sup     : 28262
% 27.55/17.72  #Fact    : 0
% 27.55/17.72  #Define  : 0
% 27.55/17.72  #Split   : 169
% 27.55/17.72  #Chain   : 0
% 27.55/17.72  #Close   : 0
% 27.55/17.72  
% 27.55/17.72  Ordering : KBO
% 27.55/17.72  
% 27.55/17.72  Simplification rules
% 27.55/17.72  ----------------------
% 27.55/17.72  #Subsume      : 7088
% 27.55/17.72  #Demod        : 52467
% 27.55/17.72  #Tautology    : 11553
% 27.55/17.72  #SimpNegUnit  : 1439
% 27.55/17.72  #BackRed      : 400
% 27.55/17.72  
% 27.55/17.72  #Partial instantiations: 0
% 27.55/17.72  #Strategies tried      : 1
% 27.55/17.72  
% 27.55/17.72  Timing (in seconds)
% 27.55/17.72  ----------------------
% 27.55/17.72  Preprocessing        : 0.48
% 27.55/17.72  Parsing              : 0.21
% 27.55/17.72  CNF conversion       : 0.06
% 27.55/17.72  Main loop            : 16.29
% 27.55/17.72  Inferencing          : 3.00
% 27.55/17.72  Reduction            : 6.55
% 27.55/17.72  Demodulation         : 4.97
% 27.55/17.72  BG Simplification    : 0.33
% 27.55/17.72  Subsumption          : 5.68
% 27.55/17.72  Abstraction          : 0.46
% 27.55/17.72  MUC search           : 0.00
% 27.55/17.72  Cooper               : 0.00
% 27.55/17.72  Total                : 16.97
% 27.55/17.72  Index Insertion      : 0.00
% 27.55/17.72  Index Deletion       : 0.00
% 27.55/17.72  Index Matching       : 0.00
% 27.55/17.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
