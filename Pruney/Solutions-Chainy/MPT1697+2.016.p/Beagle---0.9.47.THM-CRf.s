%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:11 EST 2020

% Result     : Theorem 16.37s
% Output     : CNFRefutation 16.97s
% Verified   : 
% Statistics : Number of formulae       :  557 (5591 expanded)
%              Number of leaves         :   53 (1861 expanded)
%              Depth                    :   19
%              Number of atoms          : 1505 (22859 expanded)
%              Number of equality atoms :  466 (4977 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_255,negated_conjecture,(
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

tff(f_213,axiom,(
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

tff(f_93,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_73,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_125,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_117,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_131,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_179,axiom,(
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
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_90,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_88,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_84,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_86,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_82,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_78,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_76,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_74,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_72,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_70,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_68,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_62,plain,(
    ! [E_177,F_178,B_174,D_176,C_175,A_173] :
      ( v1_funct_2(k1_tmap_1(A_173,B_174,C_175,D_176,E_177,F_178),k4_subset_1(A_173,C_175,D_176),B_174)
      | ~ m1_subset_1(F_178,k1_zfmisc_1(k2_zfmisc_1(D_176,B_174)))
      | ~ v1_funct_2(F_178,D_176,B_174)
      | ~ v1_funct_1(F_178)
      | ~ m1_subset_1(E_177,k1_zfmisc_1(k2_zfmisc_1(C_175,B_174)))
      | ~ v1_funct_2(E_177,C_175,B_174)
      | ~ v1_funct_1(E_177)
      | ~ m1_subset_1(D_176,k1_zfmisc_1(A_173))
      | v1_xboole_0(D_176)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(A_173))
      | v1_xboole_0(C_175)
      | v1_xboole_0(B_174)
      | v1_xboole_0(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_80,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_36,plain,(
    ! [A_28,B_29] :
      ( r1_xboole_0(A_28,B_29)
      | ~ r1_subset_1(A_28,B_29)
      | v1_xboole_0(B_29)
      | v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_24,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_7125,plain,(
    ! [A_788] :
      ( k9_relat_1(A_788,k1_relat_1(A_788)) = k2_relat_1(A_788)
      | ~ v1_relat_1(A_788) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_7134,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_7125])).

tff(c_7137,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_7134])).

tff(c_7138,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_7137])).

tff(c_7115,plain,(
    ! [C_783,A_784,B_785] :
      ( v1_relat_1(C_783)
      | ~ m1_subset_1(C_783,k1_zfmisc_1(k2_zfmisc_1(A_784,B_785))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_7122,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_7115])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_7139,plain,(
    ! [C_789,A_790,B_791] :
      ( v4_relat_1(C_789,A_790)
      | ~ m1_subset_1(C_789,k1_zfmisc_1(k2_zfmisc_1(A_790,B_791))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_7146,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_7139])).

tff(c_7303,plain,(
    ! [B_813,A_814] :
      ( k1_relat_1(B_813) = A_814
      | ~ v1_partfun1(B_813,A_814)
      | ~ v4_relat_1(B_813,A_814)
      | ~ v1_relat_1(B_813) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_7309,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_7146,c_7303])).

tff(c_7315,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7122,c_7309])).

tff(c_7317,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_7315])).

tff(c_7624,plain,(
    ! [C_850,A_851,B_852] :
      ( v1_partfun1(C_850,A_851)
      | ~ v1_funct_2(C_850,A_851,B_852)
      | ~ v1_funct_1(C_850)
      | ~ m1_subset_1(C_850,k1_zfmisc_1(k2_zfmisc_1(A_851,B_852)))
      | v1_xboole_0(B_852) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_7627,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_7624])).

tff(c_7633,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_7627])).

tff(c_7635,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_7317,c_7633])).

tff(c_7636,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_7315])).

tff(c_30,plain,(
    ! [B_27,A_26] :
      ( k7_relat_1(B_27,A_26) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_27),A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_7650,plain,(
    ! [A_26] :
      ( k7_relat_1('#skF_5',A_26) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_26)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7636,c_30])).

tff(c_7716,plain,(
    ! [A_855] :
      ( k7_relat_1('#skF_5',A_855) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_855) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7122,c_7650])).

tff(c_7932,plain,(
    ! [B_872] :
      ( k7_relat_1('#skF_5',B_872) = k1_xboole_0
      | k3_xboole_0('#skF_3',B_872) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_7716])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( v1_relat_1(k7_relat_1(A_11,B_12))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_7950,plain,(
    ! [B_872] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1('#skF_5')
      | k3_xboole_0('#skF_3',B_872) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7932,c_12])).

tff(c_7962,plain,(
    ! [B_872] :
      ( v1_relat_1(k1_xboole_0)
      | k3_xboole_0('#skF_3',B_872) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7122,c_7950])).

tff(c_7963,plain,(
    ! [B_872] : k3_xboole_0('#skF_3',B_872) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_7138,c_7962])).

tff(c_32,plain,(
    ! [B_27,A_26] :
      ( r1_xboole_0(k1_relat_1(B_27),A_26)
      | k7_relat_1(B_27,A_26) != k1_xboole_0
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_7647,plain,(
    ! [A_26] :
      ( r1_xboole_0('#skF_3',A_26)
      | k7_relat_1('#skF_5',A_26) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7636,c_32])).

tff(c_7733,plain,(
    ! [A_856] :
      ( r1_xboole_0('#skF_3',A_856)
      | k7_relat_1('#skF_5',A_856) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7122,c_7647])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_7756,plain,(
    ! [A_856] :
      ( k3_xboole_0('#skF_3',A_856) = k1_xboole_0
      | k7_relat_1('#skF_5',A_856) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_7733,c_2])).

tff(c_7965,plain,(
    ! [A_856] : k7_relat_1('#skF_5',A_856) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_7963,c_7756])).

tff(c_7669,plain,(
    ! [A_26] :
      ( k7_relat_1('#skF_5',A_26) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7122,c_7650])).

tff(c_8000,plain,(
    ! [A_876] : ~ r1_xboole_0('#skF_3',A_876) ),
    inference(negUnitSimplification,[status(thm)],[c_7965,c_7669])).

tff(c_8004,plain,(
    ! [B_29] :
      ( ~ r1_subset_1('#skF_3',B_29)
      | v1_xboole_0(B_29)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36,c_8000])).

tff(c_8034,plain,(
    ! [B_883] :
      ( ~ r1_subset_1('#skF_3',B_883)
      | v1_xboole_0(B_883) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_8004])).

tff(c_8037,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_8034])).

tff(c_8041,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_8037])).

tff(c_8043,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_7137])).

tff(c_8070,plain,(
    ! [B_890,A_891] :
      ( r1_xboole_0(k1_relat_1(B_890),A_891)
      | k7_relat_1(B_890,A_891) != k1_xboole_0
      | ~ v1_relat_1(B_890) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_8076,plain,(
    ! [A_891] :
      ( r1_xboole_0(k1_xboole_0,A_891)
      | k7_relat_1(k1_xboole_0,A_891) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_8070])).

tff(c_8079,plain,(
    ! [A_891] :
      ( r1_xboole_0(k1_xboole_0,A_891)
      | k7_relat_1(k1_xboole_0,A_891) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8043,c_8076])).

tff(c_8286,plain,(
    ! [B_909,A_910] :
      ( k9_relat_1(B_909,A_910) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_909),A_910)
      | ~ v1_relat_1(B_909) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8303,plain,(
    ! [A_910] :
      ( k9_relat_1(k1_xboole_0,A_910) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_910)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_8286])).

tff(c_8310,plain,(
    ! [A_911] :
      ( k9_relat_1(k1_xboole_0,A_911) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_911) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8043,c_8303])).

tff(c_8327,plain,(
    ! [A_891] :
      ( k9_relat_1(k1_xboole_0,A_891) = k1_xboole_0
      | k7_relat_1(k1_xboole_0,A_891) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8079,c_8310])).

tff(c_8109,plain,(
    ! [B_898,A_899] :
      ( r1_xboole_0(k1_relat_1(B_898),A_899)
      | k9_relat_1(B_898,A_899) != k1_xboole_0
      | ~ v1_relat_1(B_898) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8118,plain,(
    ! [A_899] :
      ( r1_xboole_0(k1_xboole_0,A_899)
      | k9_relat_1(k1_xboole_0,A_899) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_8109])).

tff(c_8122,plain,(
    ! [A_899] :
      ( r1_xboole_0(k1_xboole_0,A_899)
      | k9_relat_1(k1_xboole_0,A_899) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8043,c_8118])).

tff(c_8052,plain,(
    ! [C_884,A_885,B_886] :
      ( v4_relat_1(C_884,A_885)
      | ~ m1_subset_1(C_884,k1_zfmisc_1(k2_zfmisc_1(A_885,B_886))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_8059,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_8052])).

tff(c_8409,plain,(
    ! [B_916,A_917] :
      ( k1_relat_1(B_916) = A_917
      | ~ v1_partfun1(B_916,A_917)
      | ~ v4_relat_1(B_916,A_917)
      | ~ v1_relat_1(B_916) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_8415,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_8059,c_8409])).

tff(c_8421,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7122,c_8415])).

tff(c_9475,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_8421])).

tff(c_9929,plain,(
    ! [C_1026,A_1027,B_1028] :
      ( v1_partfun1(C_1026,A_1027)
      | ~ v1_funct_2(C_1026,A_1027,B_1028)
      | ~ v1_funct_1(C_1026)
      | ~ m1_subset_1(C_1026,k1_zfmisc_1(k2_zfmisc_1(A_1027,B_1028)))
      | v1_xboole_0(B_1028) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_9932,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_9929])).

tff(c_9938,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_9932])).

tff(c_9940,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_9475,c_9938])).

tff(c_9941,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_8421])).

tff(c_22,plain,(
    ! [A_21,B_23] :
      ( k7_relat_1(A_21,B_23) = k1_xboole_0
      | ~ r1_xboole_0(B_23,k1_relat_1(A_21))
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_9949,plain,(
    ! [B_23] :
      ( k7_relat_1('#skF_5',B_23) = k1_xboole_0
      | ~ r1_xboole_0(B_23,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9941,c_22])).

tff(c_9991,plain,(
    ! [B_1029] :
      ( k7_relat_1('#skF_5',B_1029) = k1_xboole_0
      | ~ r1_xboole_0(B_1029,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7122,c_9949])).

tff(c_10016,plain,
    ( k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0
    | k9_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8122,c_9991])).

tff(c_11783,plain,(
    k9_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_10016])).

tff(c_11790,plain,(
    k7_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8327,c_11783])).

tff(c_18,plain,(
    ! [B_15,A_14] :
      ( r1_xboole_0(k1_relat_1(B_15),A_14)
      | k9_relat_1(B_15,A_14) != k1_xboole_0
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_9958,plain,(
    ! [A_14] :
      ( r1_xboole_0('#skF_3',A_14)
      | k9_relat_1('#skF_5',A_14) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9941,c_18])).

tff(c_10024,plain,(
    ! [A_1030] :
      ( r1_xboole_0('#skF_3',A_1030)
      | k9_relat_1('#skF_5',A_1030) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7122,c_9958])).

tff(c_8198,plain,(
    ! [A_906,B_907] :
      ( k7_relat_1(A_906,B_907) = k1_xboole_0
      | ~ r1_xboole_0(B_907,k1_relat_1(A_906))
      | ~ v1_relat_1(A_906) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8225,plain,(
    ! [B_907] :
      ( k7_relat_1(k1_xboole_0,B_907) = k1_xboole_0
      | ~ r1_xboole_0(B_907,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_8198])).

tff(c_8233,plain,(
    ! [B_907] :
      ( k7_relat_1(k1_xboole_0,B_907) = k1_xboole_0
      | ~ r1_xboole_0(B_907,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8043,c_8225])).

tff(c_10045,plain,
    ( k7_relat_1(k1_xboole_0,'#skF_3') = k1_xboole_0
    | k9_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10024,c_8233])).

tff(c_12021,plain,(
    k9_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_11790,c_10045])).

tff(c_9961,plain,(
    ! [A_26] :
      ( r1_xboole_0('#skF_3',A_26)
      | k7_relat_1('#skF_5',A_26) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9941,c_32])).

tff(c_9978,plain,(
    ! [A_26] :
      ( r1_xboole_0('#skF_3',A_26)
      | k7_relat_1('#skF_5',A_26) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7122,c_9961])).

tff(c_7123,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_7115])).

tff(c_8060,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_8052])).

tff(c_8412,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_8060,c_8409])).

tff(c_8418,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7123,c_8412])).

tff(c_8422,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_8418])).

tff(c_9417,plain,(
    ! [C_995,A_996,B_997] :
      ( v1_partfun1(C_995,A_996)
      | ~ v1_funct_2(C_995,A_996,B_997)
      | ~ v1_funct_1(C_995)
      | ~ m1_subset_1(C_995,k1_zfmisc_1(k2_zfmisc_1(A_996,B_997)))
      | v1_xboole_0(B_997) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_9423,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_9417])).

tff(c_9430,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_9423])).

tff(c_9432,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_8422,c_9430])).

tff(c_9433,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_8418])).

tff(c_9441,plain,(
    ! [B_23] :
      ( k7_relat_1('#skF_6',B_23) = k1_xboole_0
      | ~ r1_xboole_0(B_23,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9433,c_22])).

tff(c_10254,plain,(
    ! [B_1044] :
      ( k7_relat_1('#skF_6',B_1044) = k1_xboole_0
      | ~ r1_xboole_0(B_1044,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7123,c_9441])).

tff(c_10295,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | k7_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9978,c_10254])).

tff(c_11597,plain,(
    k7_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_10295])).

tff(c_10282,plain,(
    ! [A_28] :
      ( k7_relat_1('#skF_6',A_28) = k1_xboole_0
      | ~ r1_subset_1(A_28,'#skF_4')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_28) ) ),
    inference(resolution,[status(thm)],[c_36,c_10254])).

tff(c_11598,plain,(
    ! [A_1160] :
      ( k7_relat_1('#skF_6',A_1160) = k1_xboole_0
      | ~ r1_subset_1(A_1160,'#skF_4')
      | v1_xboole_0(A_1160) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_10282])).

tff(c_11605,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_11598])).

tff(c_11611,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_11605])).

tff(c_9453,plain,(
    ! [A_26] :
      ( r1_xboole_0('#skF_4',A_26)
      | k7_relat_1('#skF_6',A_26) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9433,c_32])).

tff(c_10186,plain,(
    ! [A_1042] :
      ( r1_xboole_0('#skF_4',A_1042)
      | k7_relat_1('#skF_6',A_1042) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7123,c_9453])).

tff(c_9970,plain,(
    ! [B_23] :
      ( k7_relat_1('#skF_5',B_23) = k1_xboole_0
      | ~ r1_xboole_0(B_23,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7122,c_9949])).

tff(c_10213,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | k7_relat_1('#skF_6','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10186,c_9970])).

tff(c_11632,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_11611,c_10213])).

tff(c_11633,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11597,c_11632])).

tff(c_11634,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_10295])).

tff(c_11713,plain,(
    ! [A_1168] :
      ( k3_xboole_0('#skF_4',A_1168) = k1_xboole_0
      | k7_relat_1('#skF_6',A_1168) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10186,c_2])).

tff(c_11720,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_11634,c_11713])).

tff(c_8042,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_7137])).

tff(c_11944,plain,(
    ! [A_1194] :
      ( k7_relat_1('#skF_5',A_1194) = k1_xboole_0
      | k3_xboole_0(A_1194,'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_9991])).

tff(c_28,plain,(
    ! [B_25,A_24] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_25,A_24)),A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_11965,plain,(
    ! [A_1194] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),A_1194)
      | ~ v1_relat_1('#skF_5')
      | k3_xboole_0(A_1194,'#skF_3') != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11944,c_28])).

tff(c_11988,plain,(
    ! [A_1194] :
      ( r1_tarski(k1_xboole_0,A_1194)
      | k3_xboole_0(A_1194,'#skF_3') != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7122,c_26,c_11965])).

tff(c_11635,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_10295])).

tff(c_20,plain,(
    ! [A_16,C_20,B_19] :
      ( k9_relat_1(k7_relat_1(A_16,C_20),B_19) = k9_relat_1(A_16,B_19)
      | ~ r1_tarski(B_19,C_20)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_11691,plain,(
    ! [B_19] :
      ( k9_relat_1(k1_xboole_0,B_19) = k9_relat_1('#skF_5',B_19)
      | ~ r1_tarski(B_19,'#skF_4')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11635,c_20])).

tff(c_12561,plain,(
    ! [B_1221] :
      ( k9_relat_1(k1_xboole_0,B_1221) = k9_relat_1('#skF_5',B_1221)
      | ~ r1_tarski(B_1221,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7122,c_11691])).

tff(c_12573,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1('#skF_5',k1_xboole_0)
    | k3_xboole_0('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_11988,c_12561])).

tff(c_12601,plain,(
    k9_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_11720,c_8042,c_12573])).

tff(c_12603,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12021,c_12601])).

tff(c_12604,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_10016])).

tff(c_10300,plain,
    ( k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0
    | k9_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8122,c_10254])).

tff(c_10538,plain,(
    k9_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_10300])).

tff(c_10545,plain,(
    k7_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8327,c_10538])).

tff(c_9450,plain,(
    ! [A_14] :
      ( r1_xboole_0('#skF_4',A_14)
      | k9_relat_1('#skF_6',A_14) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9433,c_18])).

tff(c_10117,plain,(
    ! [A_1038] :
      ( r1_xboole_0('#skF_4',A_1038)
      | k9_relat_1('#skF_6',A_1038) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7123,c_9450])).

tff(c_10137,plain,
    ( k7_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0
    | k9_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10117,c_8233])).

tff(c_11247,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_10545,c_10137])).

tff(c_34,plain,(
    ! [A_28,B_29] :
      ( r1_subset_1(A_28,B_29)
      | ~ r1_xboole_0(A_28,B_29)
      | v1_xboole_0(B_29)
      | v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_10207,plain,(
    ! [A_1042] :
      ( r1_subset_1('#skF_4',A_1042)
      | v1_xboole_0(A_1042)
      | v1_xboole_0('#skF_4')
      | k7_relat_1('#skF_6',A_1042) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10186,c_34])).

tff(c_10555,plain,(
    ! [A_1065] :
      ( r1_subset_1('#skF_4',A_1065)
      | v1_xboole_0(A_1065)
      | k7_relat_1('#skF_6',A_1065) != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_10207])).

tff(c_10003,plain,(
    ! [A_28] :
      ( k7_relat_1('#skF_5',A_28) = k1_xboole_0
      | ~ r1_subset_1(A_28,'#skF_3')
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_28) ) ),
    inference(resolution,[status(thm)],[c_36,c_9991])).

tff(c_10020,plain,(
    ! [A_28] :
      ( k7_relat_1('#skF_5',A_28) = k1_xboole_0
      | ~ r1_subset_1(A_28,'#skF_3')
      | v1_xboole_0(A_28) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_10003])).

tff(c_10559,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | k7_relat_1('#skF_6','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10555,c_10020])).

tff(c_10562,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | k7_relat_1('#skF_6','#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_84,c_10559])).

tff(c_10640,plain,(
    k7_relat_1('#skF_6','#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_10562])).

tff(c_10749,plain,(
    ! [A_1090] :
      ( k7_relat_1('#skF_6',A_1090) = k1_xboole_0
      | ~ r1_subset_1(A_1090,'#skF_4')
      | v1_xboole_0(A_1090) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_10282])).

tff(c_10756,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_10749])).

tff(c_10762,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_10640,c_10756])).

tff(c_10763,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_10562])).

tff(c_10220,plain,(
    ! [A_1043] :
      ( r1_xboole_0('#skF_3',A_1043)
      | k7_relat_1('#skF_5',A_1043) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7122,c_9961])).

tff(c_10253,plain,(
    ! [A_1043] :
      ( k3_xboole_0('#skF_3',A_1043) = k1_xboole_0
      | k7_relat_1('#skF_5',A_1043) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10220,c_2])).

tff(c_10780,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10763,c_10253])).

tff(c_11258,plain,(
    ! [A_1136] :
      ( k7_relat_1('#skF_6',A_1136) = k1_xboole_0
      | k3_xboole_0(A_1136,'#skF_4') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_10254])).

tff(c_11282,plain,(
    ! [A_1136] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),A_1136)
      | ~ v1_relat_1('#skF_6')
      | k3_xboole_0(A_1136,'#skF_4') != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11258,c_28])).

tff(c_11306,plain,(
    ! [A_1136] :
      ( r1_tarski(k1_xboole_0,A_1136)
      | k3_xboole_0(A_1136,'#skF_4') != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7123,c_26,c_11282])).

tff(c_10764,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_10562])).

tff(c_10794,plain,(
    ! [B_19] :
      ( k9_relat_1(k1_xboole_0,B_19) = k9_relat_1('#skF_6',B_19)
      | ~ r1_tarski(B_19,'#skF_3')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10764,c_20])).

tff(c_11405,plain,(
    ! [B_1145] :
      ( k9_relat_1(k1_xboole_0,B_1145) = k9_relat_1('#skF_6',B_1145)
      | ~ r1_tarski(B_1145,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7123,c_10794])).

tff(c_11409,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1('#skF_6',k1_xboole_0)
    | k3_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_11306,c_11405])).

tff(c_11439,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10780,c_8042,c_11409])).

tff(c_11441,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11247,c_11439])).

tff(c_11442,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_10300])).

tff(c_11700,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_11635,c_10253])).

tff(c_10085,plain,(
    ! [A_1033,B_1034,C_1035] :
      ( k9_subset_1(A_1033,B_1034,C_1035) = k3_xboole_0(B_1034,C_1035)
      | ~ m1_subset_1(C_1035,k1_zfmisc_1(A_1033)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10097,plain,(
    ! [B_1034] : k9_subset_1('#skF_1',B_1034,'#skF_4') = k3_xboole_0(B_1034,'#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_10085])).

tff(c_11463,plain,(
    ! [E_1148,D_1150,C_1146,A_1147,F_1151,B_1149] :
      ( v1_funct_1(k1_tmap_1(A_1147,B_1149,C_1146,D_1150,E_1148,F_1151))
      | ~ m1_subset_1(F_1151,k1_zfmisc_1(k2_zfmisc_1(D_1150,B_1149)))
      | ~ v1_funct_2(F_1151,D_1150,B_1149)
      | ~ v1_funct_1(F_1151)
      | ~ m1_subset_1(E_1148,k1_zfmisc_1(k2_zfmisc_1(C_1146,B_1149)))
      | ~ v1_funct_2(E_1148,C_1146,B_1149)
      | ~ v1_funct_1(E_1148)
      | ~ m1_subset_1(D_1150,k1_zfmisc_1(A_1147))
      | v1_xboole_0(D_1150)
      | ~ m1_subset_1(C_1146,k1_zfmisc_1(A_1147))
      | v1_xboole_0(C_1146)
      | v1_xboole_0(B_1149)
      | v1_xboole_0(A_1147) ) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_11467,plain,(
    ! [A_1147,C_1146,E_1148] :
      ( v1_funct_1(k1_tmap_1(A_1147,'#skF_2',C_1146,'#skF_4',E_1148,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1148,k1_zfmisc_1(k2_zfmisc_1(C_1146,'#skF_2')))
      | ~ v1_funct_2(E_1148,C_1146,'#skF_2')
      | ~ v1_funct_1(E_1148)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1147))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1146,k1_zfmisc_1(A_1147))
      | v1_xboole_0(C_1146)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1147) ) ),
    inference(resolution,[status(thm)],[c_68,c_11463])).

tff(c_11474,plain,(
    ! [A_1147,C_1146,E_1148] :
      ( v1_funct_1(k1_tmap_1(A_1147,'#skF_2',C_1146,'#skF_4',E_1148,'#skF_6'))
      | ~ m1_subset_1(E_1148,k1_zfmisc_1(k2_zfmisc_1(C_1146,'#skF_2')))
      | ~ v1_funct_2(E_1148,C_1146,'#skF_2')
      | ~ v1_funct_1(E_1148)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1147))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1146,k1_zfmisc_1(A_1147))
      | v1_xboole_0(C_1146)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_11467])).

tff(c_14003,plain,(
    ! [A_1284,C_1285,E_1286] :
      ( v1_funct_1(k1_tmap_1(A_1284,'#skF_2',C_1285,'#skF_4',E_1286,'#skF_6'))
      | ~ m1_subset_1(E_1286,k1_zfmisc_1(k2_zfmisc_1(C_1285,'#skF_2')))
      | ~ v1_funct_2(E_1286,C_1285,'#skF_2')
      | ~ v1_funct_1(E_1286)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1284))
      | ~ m1_subset_1(C_1285,k1_zfmisc_1(A_1284))
      | v1_xboole_0(C_1285)
      | v1_xboole_0(A_1284) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_11474])).

tff(c_14008,plain,(
    ! [A_1284] :
      ( v1_funct_1(k1_tmap_1(A_1284,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1284))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1284))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1284) ) ),
    inference(resolution,[status(thm)],[c_74,c_14003])).

tff(c_14016,plain,(
    ! [A_1284] :
      ( v1_funct_1(k1_tmap_1(A_1284,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1284))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1284))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1284) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_14008])).

tff(c_14445,plain,(
    ! [A_1300] :
      ( v1_funct_1(k1_tmap_1(A_1300,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1300))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1300))
      | v1_xboole_0(A_1300) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_14016])).

tff(c_14448,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_86,c_14445])).

tff(c_14451,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_14448])).

tff(c_14452,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_14451])).

tff(c_10461,plain,(
    ! [A_1053,B_1054,C_1055,D_1056] :
      ( k2_partfun1(A_1053,B_1054,C_1055,D_1056) = k7_relat_1(C_1055,D_1056)
      | ~ m1_subset_1(C_1055,k1_zfmisc_1(k2_zfmisc_1(A_1053,B_1054)))
      | ~ v1_funct_1(C_1055) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_10463,plain,(
    ! [D_1056] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_1056) = k7_relat_1('#skF_5',D_1056)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_74,c_10461])).

tff(c_10468,plain,(
    ! [D_1056] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_1056) = k7_relat_1('#skF_5',D_1056) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_10463])).

tff(c_10465,plain,(
    ! [D_1056] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_1056) = k7_relat_1('#skF_6',D_1056)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_68,c_10461])).

tff(c_10471,plain,(
    ! [D_1056] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_1056) = k7_relat_1('#skF_6',D_1056) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_10465])).

tff(c_60,plain,(
    ! [E_177,F_178,B_174,D_176,C_175,A_173] :
      ( m1_subset_1(k1_tmap_1(A_173,B_174,C_175,D_176,E_177,F_178),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_173,C_175,D_176),B_174)))
      | ~ m1_subset_1(F_178,k1_zfmisc_1(k2_zfmisc_1(D_176,B_174)))
      | ~ v1_funct_2(F_178,D_176,B_174)
      | ~ v1_funct_1(F_178)
      | ~ m1_subset_1(E_177,k1_zfmisc_1(k2_zfmisc_1(C_175,B_174)))
      | ~ v1_funct_2(E_177,C_175,B_174)
      | ~ v1_funct_1(E_177)
      | ~ m1_subset_1(D_176,k1_zfmisc_1(A_173))
      | v1_xboole_0(D_176)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(A_173))
      | v1_xboole_0(C_175)
      | v1_xboole_0(B_174)
      | v1_xboole_0(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_12722,plain,(
    ! [E_1224,C_1227,F_1223,A_1228,B_1225,D_1226] :
      ( k2_partfun1(k4_subset_1(A_1228,C_1227,D_1226),B_1225,k1_tmap_1(A_1228,B_1225,C_1227,D_1226,E_1224,F_1223),D_1226) = F_1223
      | ~ m1_subset_1(k1_tmap_1(A_1228,B_1225,C_1227,D_1226,E_1224,F_1223),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1228,C_1227,D_1226),B_1225)))
      | ~ v1_funct_2(k1_tmap_1(A_1228,B_1225,C_1227,D_1226,E_1224,F_1223),k4_subset_1(A_1228,C_1227,D_1226),B_1225)
      | ~ v1_funct_1(k1_tmap_1(A_1228,B_1225,C_1227,D_1226,E_1224,F_1223))
      | k2_partfun1(D_1226,B_1225,F_1223,k9_subset_1(A_1228,C_1227,D_1226)) != k2_partfun1(C_1227,B_1225,E_1224,k9_subset_1(A_1228,C_1227,D_1226))
      | ~ m1_subset_1(F_1223,k1_zfmisc_1(k2_zfmisc_1(D_1226,B_1225)))
      | ~ v1_funct_2(F_1223,D_1226,B_1225)
      | ~ v1_funct_1(F_1223)
      | ~ m1_subset_1(E_1224,k1_zfmisc_1(k2_zfmisc_1(C_1227,B_1225)))
      | ~ v1_funct_2(E_1224,C_1227,B_1225)
      | ~ v1_funct_1(E_1224)
      | ~ m1_subset_1(D_1226,k1_zfmisc_1(A_1228))
      | v1_xboole_0(D_1226)
      | ~ m1_subset_1(C_1227,k1_zfmisc_1(A_1228))
      | v1_xboole_0(C_1227)
      | v1_xboole_0(B_1225)
      | v1_xboole_0(A_1228) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_20075,plain,(
    ! [F_1499,B_1497,C_1494,A_1495,E_1496,D_1498] :
      ( k2_partfun1(k4_subset_1(A_1495,C_1494,D_1498),B_1497,k1_tmap_1(A_1495,B_1497,C_1494,D_1498,E_1496,F_1499),D_1498) = F_1499
      | ~ v1_funct_2(k1_tmap_1(A_1495,B_1497,C_1494,D_1498,E_1496,F_1499),k4_subset_1(A_1495,C_1494,D_1498),B_1497)
      | ~ v1_funct_1(k1_tmap_1(A_1495,B_1497,C_1494,D_1498,E_1496,F_1499))
      | k2_partfun1(D_1498,B_1497,F_1499,k9_subset_1(A_1495,C_1494,D_1498)) != k2_partfun1(C_1494,B_1497,E_1496,k9_subset_1(A_1495,C_1494,D_1498))
      | ~ m1_subset_1(F_1499,k1_zfmisc_1(k2_zfmisc_1(D_1498,B_1497)))
      | ~ v1_funct_2(F_1499,D_1498,B_1497)
      | ~ v1_funct_1(F_1499)
      | ~ m1_subset_1(E_1496,k1_zfmisc_1(k2_zfmisc_1(C_1494,B_1497)))
      | ~ v1_funct_2(E_1496,C_1494,B_1497)
      | ~ v1_funct_1(E_1496)
      | ~ m1_subset_1(D_1498,k1_zfmisc_1(A_1495))
      | v1_xboole_0(D_1498)
      | ~ m1_subset_1(C_1494,k1_zfmisc_1(A_1495))
      | v1_xboole_0(C_1494)
      | v1_xboole_0(B_1497)
      | v1_xboole_0(A_1495) ) ),
    inference(resolution,[status(thm)],[c_60,c_12722])).

tff(c_27503,plain,(
    ! [A_1646,F_1650,E_1647,D_1649,C_1645,B_1648] :
      ( k2_partfun1(k4_subset_1(A_1646,C_1645,D_1649),B_1648,k1_tmap_1(A_1646,B_1648,C_1645,D_1649,E_1647,F_1650),D_1649) = F_1650
      | ~ v1_funct_1(k1_tmap_1(A_1646,B_1648,C_1645,D_1649,E_1647,F_1650))
      | k2_partfun1(D_1649,B_1648,F_1650,k9_subset_1(A_1646,C_1645,D_1649)) != k2_partfun1(C_1645,B_1648,E_1647,k9_subset_1(A_1646,C_1645,D_1649))
      | ~ m1_subset_1(F_1650,k1_zfmisc_1(k2_zfmisc_1(D_1649,B_1648)))
      | ~ v1_funct_2(F_1650,D_1649,B_1648)
      | ~ v1_funct_1(F_1650)
      | ~ m1_subset_1(E_1647,k1_zfmisc_1(k2_zfmisc_1(C_1645,B_1648)))
      | ~ v1_funct_2(E_1647,C_1645,B_1648)
      | ~ v1_funct_1(E_1647)
      | ~ m1_subset_1(D_1649,k1_zfmisc_1(A_1646))
      | v1_xboole_0(D_1649)
      | ~ m1_subset_1(C_1645,k1_zfmisc_1(A_1646))
      | v1_xboole_0(C_1645)
      | v1_xboole_0(B_1648)
      | v1_xboole_0(A_1646) ) ),
    inference(resolution,[status(thm)],[c_62,c_20075])).

tff(c_27509,plain,(
    ! [A_1646,C_1645,E_1647] :
      ( k2_partfun1(k4_subset_1(A_1646,C_1645,'#skF_4'),'#skF_2',k1_tmap_1(A_1646,'#skF_2',C_1645,'#skF_4',E_1647,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1646,'#skF_2',C_1645,'#skF_4',E_1647,'#skF_6'))
      | k2_partfun1(C_1645,'#skF_2',E_1647,k9_subset_1(A_1646,C_1645,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_1646,C_1645,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1647,k1_zfmisc_1(k2_zfmisc_1(C_1645,'#skF_2')))
      | ~ v1_funct_2(E_1647,C_1645,'#skF_2')
      | ~ v1_funct_1(E_1647)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1646))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1645,k1_zfmisc_1(A_1646))
      | v1_xboole_0(C_1645)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1646) ) ),
    inference(resolution,[status(thm)],[c_68,c_27503])).

tff(c_27517,plain,(
    ! [A_1646,C_1645,E_1647] :
      ( k2_partfun1(k4_subset_1(A_1646,C_1645,'#skF_4'),'#skF_2',k1_tmap_1(A_1646,'#skF_2',C_1645,'#skF_4',E_1647,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1646,'#skF_2',C_1645,'#skF_4',E_1647,'#skF_6'))
      | k2_partfun1(C_1645,'#skF_2',E_1647,k9_subset_1(A_1646,C_1645,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1646,C_1645,'#skF_4'))
      | ~ m1_subset_1(E_1647,k1_zfmisc_1(k2_zfmisc_1(C_1645,'#skF_2')))
      | ~ v1_funct_2(E_1647,C_1645,'#skF_2')
      | ~ v1_funct_1(E_1647)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1646))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1645,k1_zfmisc_1(A_1646))
      | v1_xboole_0(C_1645)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1646) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_10471,c_27509])).

tff(c_29598,plain,(
    ! [A_1684,C_1685,E_1686] :
      ( k2_partfun1(k4_subset_1(A_1684,C_1685,'#skF_4'),'#skF_2',k1_tmap_1(A_1684,'#skF_2',C_1685,'#skF_4',E_1686,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1684,'#skF_2',C_1685,'#skF_4',E_1686,'#skF_6'))
      | k2_partfun1(C_1685,'#skF_2',E_1686,k9_subset_1(A_1684,C_1685,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1684,C_1685,'#skF_4'))
      | ~ m1_subset_1(E_1686,k1_zfmisc_1(k2_zfmisc_1(C_1685,'#skF_2')))
      | ~ v1_funct_2(E_1686,C_1685,'#skF_2')
      | ~ v1_funct_1(E_1686)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1684))
      | ~ m1_subset_1(C_1685,k1_zfmisc_1(A_1684))
      | v1_xboole_0(C_1685)
      | v1_xboole_0(A_1684) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_27517])).

tff(c_29603,plain,(
    ! [A_1684] :
      ( k2_partfun1(k4_subset_1(A_1684,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1684,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1684,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1684,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1684,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1684))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1684))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1684) ) ),
    inference(resolution,[status(thm)],[c_74,c_29598])).

tff(c_29611,plain,(
    ! [A_1684] :
      ( k2_partfun1(k4_subset_1(A_1684,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1684,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1684,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1684,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1684,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1684))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1684))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1684) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_10468,c_29603])).

tff(c_31056,plain,(
    ! [A_1707] :
      ( k2_partfun1(k4_subset_1(A_1707,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1707,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1707,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1707,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1707,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1707))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1707))
      | v1_xboole_0(A_1707) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_29611])).

tff(c_140,plain,(
    ! [C_248,A_249,B_250] :
      ( v1_relat_1(C_248)
      | ~ m1_subset_1(C_248,k1_zfmisc_1(k2_zfmisc_1(A_249,B_250))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_148,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_140])).

tff(c_862,plain,(
    ! [C_335,A_336,B_337] :
      ( v4_relat_1(C_335,A_336)
      | ~ m1_subset_1(C_335,k1_zfmisc_1(k2_zfmisc_1(A_336,B_337))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_870,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_862])).

tff(c_1283,plain,(
    ! [B_369,A_370] :
      ( k1_relat_1(B_369) = A_370
      | ~ v1_partfun1(B_369,A_370)
      | ~ v4_relat_1(B_369,A_370)
      | ~ v1_relat_1(B_369) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1286,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_870,c_1283])).

tff(c_1292,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_1286])).

tff(c_1296,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1292])).

tff(c_2055,plain,(
    ! [C_434,A_435,B_436] :
      ( v1_partfun1(C_434,A_435)
      | ~ v1_funct_2(C_434,A_435,B_436)
      | ~ v1_funct_1(C_434)
      | ~ m1_subset_1(C_434,k1_zfmisc_1(k2_zfmisc_1(A_435,B_436)))
      | v1_xboole_0(B_436) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2061,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_2055])).

tff(c_2068,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_2061])).

tff(c_2070,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_1296,c_2068])).

tff(c_2071,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1292])).

tff(c_2088,plain,(
    ! [A_14] :
      ( r1_xboole_0('#skF_4',A_14)
      | k9_relat_1('#skF_6',A_14) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2071,c_18])).

tff(c_2746,plain,(
    ! [A_478] :
      ( r1_xboole_0('#skF_4',A_478)
      | k9_relat_1('#skF_6',A_478) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_2088])).

tff(c_149,plain,(
    ! [A_251] :
      ( k9_relat_1(A_251,k1_relat_1(A_251)) = k2_relat_1(A_251)
      | ~ v1_relat_1(A_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

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

tff(c_147,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_140])).

tff(c_163,plain,(
    ! [C_252,A_253,B_254] :
      ( v4_relat_1(C_252,A_253)
      | ~ m1_subset_1(C_252,k1_zfmisc_1(k2_zfmisc_1(A_253,B_254))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_170,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_163])).

tff(c_346,plain,(
    ! [B_277,A_278] :
      ( k1_relat_1(B_277) = A_278
      | ~ v1_partfun1(B_277,A_278)
      | ~ v4_relat_1(B_277,A_278)
      | ~ v1_relat_1(B_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_352,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_170,c_346])).

tff(c_358,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_352])).

tff(c_360,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_358])).

tff(c_511,plain,(
    ! [C_305,A_306,B_307] :
      ( v1_partfun1(C_305,A_306)
      | ~ v1_funct_2(C_305,A_306,B_307)
      | ~ v1_funct_1(C_305)
      | ~ m1_subset_1(C_305,k1_zfmisc_1(k2_zfmisc_1(A_306,B_307)))
      | v1_xboole_0(B_307) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_514,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_511])).

tff(c_520,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_514])).

tff(c_522,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_360,c_520])).

tff(c_523,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_358])).

tff(c_529,plain,(
    ! [A_26] :
      ( k7_relat_1('#skF_5',A_26) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_26)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_523,c_30])).

tff(c_706,plain,(
    ! [A_318] :
      ( k7_relat_1('#skF_5',A_318) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_318) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_529])).

tff(c_746,plain,(
    ! [B_322] :
      ( k7_relat_1('#skF_5',B_322) = k1_xboole_0
      | k3_xboole_0('#skF_3',B_322) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_706])).

tff(c_761,plain,(
    ! [B_322] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1('#skF_5')
      | k3_xboole_0('#skF_3',B_322) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_746,c_12])).

tff(c_772,plain,(
    ! [B_322] :
      ( v1_relat_1(k1_xboole_0)
      | k3_xboole_0('#skF_3',B_322) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_761])).

tff(c_773,plain,(
    ! [B_322] : k3_xboole_0('#skF_3',B_322) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_772])).

tff(c_532,plain,(
    ! [A_14] :
      ( r1_xboole_0('#skF_3',A_14)
      | k9_relat_1('#skF_5',A_14) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_523,c_18])).

tff(c_640,plain,(
    ! [A_315] :
      ( r1_xboole_0('#skF_3',A_315)
      | k9_relat_1('#skF_5',A_315) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_532])).

tff(c_662,plain,(
    ! [A_315] :
      ( k3_xboole_0('#skF_3',A_315) = k1_xboole_0
      | k9_relat_1('#skF_5',A_315) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_640,c_2])).

tff(c_785,plain,(
    ! [A_315] : k9_relat_1('#skF_5',A_315) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_773,c_662])).

tff(c_16,plain,(
    ! [B_15,A_14] :
      ( k9_relat_1(B_15,A_14) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_15),A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_535,plain,(
    ! [A_14] :
      ( k9_relat_1('#skF_5',A_14) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_14)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_523,c_16])).

tff(c_555,plain,(
    ! [A_14] :
      ( k9_relat_1('#skF_5',A_14) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_535])).

tff(c_798,plain,(
    ! [A_326] : ~ r1_xboole_0('#skF_3',A_326) ),
    inference(negUnitSimplification,[status(thm)],[c_785,c_555])).

tff(c_802,plain,(
    ! [B_29] :
      ( ~ r1_subset_1('#skF_3',B_29)
      | v1_xboole_0(B_29)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36,c_798])).

tff(c_848,plain,(
    ! [B_334] :
      ( ~ r1_subset_1('#skF_3',B_334)
      | v1_xboole_0(B_334) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_802])).

tff(c_851,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_848])).

tff(c_855,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_851])).

tff(c_857,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_161])).

tff(c_931,plain,(
    ! [A_348,B_349] :
      ( k7_relat_1(A_348,B_349) = k1_xboole_0
      | ~ r1_xboole_0(B_349,k1_relat_1(A_348))
      | ~ v1_relat_1(A_348) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_946,plain,(
    ! [B_349] :
      ( k7_relat_1(k1_xboole_0,B_349) = k1_xboole_0
      | ~ r1_xboole_0(B_349,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_931])).

tff(c_951,plain,(
    ! [B_349] :
      ( k7_relat_1(k1_xboole_0,B_349) = k1_xboole_0
      | ~ r1_xboole_0(B_349,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_857,c_946])).

tff(c_2772,plain,
    ( k7_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0
    | k9_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2746,c_951])).

tff(c_2981,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2772])).

tff(c_869,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_862])).

tff(c_1289,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_869,c_1283])).

tff(c_1295,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_1289])).

tff(c_2113,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1295])).

tff(c_2512,plain,(
    ! [C_464,A_465,B_466] :
      ( v1_partfun1(C_464,A_465)
      | ~ v1_funct_2(C_464,A_465,B_466)
      | ~ v1_funct_1(C_464)
      | ~ m1_subset_1(C_464,k1_zfmisc_1(k2_zfmisc_1(A_465,B_466)))
      | v1_xboole_0(B_466) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2515,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_2512])).

tff(c_2521,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_2515])).

tff(c_2523,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_2113,c_2521])).

tff(c_2524,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1295])).

tff(c_2535,plain,(
    ! [A_26] :
      ( r1_xboole_0('#skF_3',A_26)
      | k7_relat_1('#skF_5',A_26) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2524,c_32])).

tff(c_2698,plain,(
    ! [A_476] :
      ( r1_xboole_0('#skF_3',A_476)
      | k7_relat_1('#skF_5',A_476) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_2535])).

tff(c_2532,plain,(
    ! [A_14] :
      ( k9_relat_1('#skF_5',A_14) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_14)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2524,c_16])).

tff(c_2553,plain,(
    ! [A_14] :
      ( k9_relat_1('#skF_5',A_14) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_2532])).

tff(c_3013,plain,(
    ! [A_496] :
      ( k9_relat_1('#skF_5',A_496) = k1_xboole_0
      | k7_relat_1('#skF_5',A_496) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2698,c_2553])).

tff(c_2541,plain,(
    ! [A_14] :
      ( r1_xboole_0('#skF_3',A_14)
      | k9_relat_1('#skF_5',A_14) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2524,c_18])).

tff(c_2851,plain,(
    ! [A_482] :
      ( r1_xboole_0('#skF_3',A_482)
      | k9_relat_1('#skF_5',A_482) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_2541])).

tff(c_2085,plain,(
    ! [B_23] :
      ( k7_relat_1('#skF_6',B_23) = k1_xboole_0
      | ~ r1_xboole_0(B_23,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2071,c_22])).

tff(c_2104,plain,(
    ! [B_23] :
      ( k7_relat_1('#skF_6',B_23) = k1_xboole_0
      | ~ r1_xboole_0(B_23,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_2085])).

tff(c_2882,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | k9_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2851,c_2104])).

tff(c_3012,plain,(
    k9_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2882])).

tff(c_3038,plain,(
    k7_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3013,c_3012])).

tff(c_2082,plain,(
    ! [A_26] :
      ( r1_xboole_0('#skF_4',A_26)
      | k7_relat_1('#skF_6',A_26) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2071,c_32])).

tff(c_2812,plain,(
    ! [A_481] :
      ( r1_xboole_0('#skF_4',A_481)
      | k7_relat_1('#skF_6',A_481) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_2082])).

tff(c_2837,plain,(
    ! [A_481] :
      ( r1_subset_1('#skF_4',A_481)
      | v1_xboole_0(A_481)
      | v1_xboole_0('#skF_4')
      | k7_relat_1('#skF_6',A_481) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2812,c_34])).

tff(c_3063,plain,(
    ! [A_500] :
      ( r1_subset_1('#skF_4',A_500)
      | v1_xboole_0(A_500)
      | k7_relat_1('#skF_6',A_500) != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2837])).

tff(c_2538,plain,(
    ! [B_23] :
      ( k7_relat_1('#skF_5',B_23) = k1_xboole_0
      | ~ r1_xboole_0(B_23,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2524,c_22])).

tff(c_2574,plain,(
    ! [B_467] :
      ( k7_relat_1('#skF_5',B_467) = k1_xboole_0
      | ~ r1_xboole_0(B_467,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_2538])).

tff(c_2578,plain,(
    ! [A_28] :
      ( k7_relat_1('#skF_5',A_28) = k1_xboole_0
      | ~ r1_subset_1(A_28,'#skF_3')
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_28) ) ),
    inference(resolution,[status(thm)],[c_36,c_2574])).

tff(c_2601,plain,(
    ! [A_28] :
      ( k7_relat_1('#skF_5',A_28) = k1_xboole_0
      | ~ r1_subset_1(A_28,'#skF_3')
      | v1_xboole_0(A_28) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_2578])).

tff(c_3067,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | k7_relat_1('#skF_6','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3063,c_2601])).

tff(c_3070,plain,(
    k7_relat_1('#skF_6','#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_84,c_3038,c_3067])).

tff(c_2607,plain,(
    ! [B_468] :
      ( k7_relat_1('#skF_6',B_468) = k1_xboole_0
      | ~ r1_xboole_0(B_468,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_2085])).

tff(c_2611,plain,(
    ! [A_28] :
      ( k7_relat_1('#skF_6',A_28) = k1_xboole_0
      | ~ r1_subset_1(A_28,'#skF_4')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_28) ) ),
    inference(resolution,[status(thm)],[c_36,c_2607])).

tff(c_3294,plain,(
    ! [A_527] :
      ( k7_relat_1('#skF_6',A_527) = k1_xboole_0
      | ~ r1_subset_1(A_527,'#skF_4')
      | v1_xboole_0(A_527) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2611])).

tff(c_3305,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_3294])).

tff(c_3313,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_3070,c_3305])).

tff(c_3315,plain,(
    k9_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2882])).

tff(c_3371,plain,(
    ! [A_532] :
      ( k3_xboole_0('#skF_3',A_532) = k1_xboole_0
      | k9_relat_1('#skF_5',A_532) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2851,c_2])).

tff(c_3382,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3315,c_3371])).

tff(c_856,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_161])).

tff(c_3550,plain,(
    ! [A_553] :
      ( k7_relat_1('#skF_6',A_553) = k1_xboole_0
      | k3_xboole_0(A_553,'#skF_4') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_2607])).

tff(c_3574,plain,(
    ! [A_553] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),A_553)
      | ~ v1_relat_1('#skF_6')
      | k3_xboole_0(A_553,'#skF_4') != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3550,c_28])).

tff(c_3598,plain,(
    ! [A_553] :
      ( r1_tarski(k1_xboole_0,A_553)
      | k3_xboole_0(A_553,'#skF_4') != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_26,c_3574])).

tff(c_3314,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2882])).

tff(c_3319,plain,(
    ! [B_19] :
      ( k9_relat_1(k1_xboole_0,B_19) = k9_relat_1('#skF_6',B_19)
      | ~ r1_tarski(B_19,'#skF_3')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3314,c_20])).

tff(c_4091,plain,(
    ! [B_595] :
      ( k9_relat_1(k1_xboole_0,B_595) = k9_relat_1('#skF_6',B_595)
      | ~ r1_tarski(B_595,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_3319])).

tff(c_4103,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1('#skF_6',k1_xboole_0)
    | k3_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3598,c_4091])).

tff(c_4131,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3382,c_856,c_4103])).

tff(c_4133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2981,c_4131])).

tff(c_4135,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2772])).

tff(c_2106,plain,(
    ! [A_14] :
      ( r1_xboole_0('#skF_4',A_14)
      | k9_relat_1('#skF_6',A_14) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_2088])).

tff(c_2076,plain,(
    ! [A_26] :
      ( k7_relat_1('#skF_6',A_26) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_26)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2071,c_30])).

tff(c_2778,plain,(
    ! [A_479] :
      ( k7_relat_1('#skF_6',A_479) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_479) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_2076])).

tff(c_4617,plain,(
    ! [A_639] :
      ( k7_relat_1('#skF_6',A_639) = k1_xboole_0
      | k9_relat_1('#skF_6',A_639) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2106,c_2778])).

tff(c_4632,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4135,c_4617])).

tff(c_2729,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | k7_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2698,c_2104])).

tff(c_4278,plain,(
    k7_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2729])).

tff(c_2529,plain,(
    ! [A_26] :
      ( k7_relat_1('#skF_5',A_26) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_26)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2524,c_30])).

tff(c_2653,plain,(
    ! [A_470] :
      ( k7_relat_1('#skF_5',A_470) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_470) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_2529])).

tff(c_2657,plain,(
    ! [B_29] :
      ( k7_relat_1('#skF_5',B_29) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_29)
      | v1_xboole_0(B_29)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36,c_2653])).

tff(c_4487,plain,(
    ! [B_628] :
      ( k7_relat_1('#skF_5',B_628) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_628)
      | v1_xboole_0(B_628) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_2657])).

tff(c_4490,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_4487])).

tff(c_4494,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_4278,c_4490])).

tff(c_4496,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2729])).

tff(c_5785,plain,(
    ! [A_729] :
      ( k3_xboole_0('#skF_3',A_729) = k1_xboole_0
      | k7_relat_1('#skF_5',A_729) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2698,c_2])).

tff(c_5802,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4496,c_5785])).

tff(c_2885,plain,
    ( k7_relat_1(k1_xboole_0,'#skF_3') = k1_xboole_0
    | k9_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2851,c_951])).

tff(c_4768,plain,(
    k9_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2885])).

tff(c_5120,plain,(
    ! [A_684] :
      ( k3_xboole_0('#skF_3',A_684) = k1_xboole_0
      | k7_relat_1('#skF_5',A_684) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2698,c_2])).

tff(c_5132,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4496,c_5120])).

tff(c_5069,plain,(
    ! [B_677] :
      ( k7_relat_1('#skF_5',B_677) = k1_xboole_0
      | k3_xboole_0('#skF_3',B_677) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_2653])).

tff(c_5090,plain,(
    ! [B_677] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),B_677)
      | ~ v1_relat_1('#skF_5')
      | k3_xboole_0('#skF_3',B_677) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5069,c_28])).

tff(c_5111,plain,(
    ! [B_677] :
      ( r1_tarski(k1_xboole_0,B_677)
      | k3_xboole_0('#skF_3',B_677) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_26,c_5090])).

tff(c_4519,plain,(
    ! [B_19] :
      ( k9_relat_1(k1_xboole_0,B_19) = k9_relat_1('#skF_5',B_19)
      | ~ r1_tarski(B_19,'#skF_4')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4496,c_20])).

tff(c_5314,plain,(
    ! [B_694] :
      ( k9_relat_1(k1_xboole_0,B_694) = k9_relat_1('#skF_5',B_694)
      | ~ r1_tarski(B_694,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_4519])).

tff(c_5318,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1('#skF_5',k1_xboole_0)
    | k3_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5111,c_5314])).

tff(c_5348,plain,(
    k9_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5132,c_856,c_5318])).

tff(c_5350,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4768,c_5348])).

tff(c_5352,plain,(
    k9_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2885])).

tff(c_2551,plain,(
    ! [A_26] :
      ( k7_relat_1('#skF_5',A_26) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_2529])).

tff(c_5492,plain,(
    ! [A_704] :
      ( k7_relat_1('#skF_5',A_704) = k1_xboole_0
      | k9_relat_1('#skF_5',A_704) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2851,c_2551])).

tff(c_5506,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5352,c_5492])).

tff(c_4180,plain,(
    ! [A_596,B_597,C_598,D_599] :
      ( k2_partfun1(A_596,B_597,C_598,D_599) = k7_relat_1(C_598,D_599)
      | ~ m1_subset_1(C_598,k1_zfmisc_1(k2_zfmisc_1(A_596,B_597)))
      | ~ v1_funct_1(C_598) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_4182,plain,(
    ! [D_599] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_599) = k7_relat_1('#skF_5',D_599)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_74,c_4180])).

tff(c_4187,plain,(
    ! [D_599] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_599) = k7_relat_1('#skF_5',D_599) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_4182])).

tff(c_4184,plain,(
    ! [D_599] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_599) = k7_relat_1('#skF_6',D_599)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_68,c_4180])).

tff(c_4190,plain,(
    ! [D_599] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_599) = k7_relat_1('#skF_6',D_599) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4184])).

tff(c_2666,plain,(
    ! [A_471,B_472,C_473] :
      ( k9_subset_1(A_471,B_472,C_473) = k3_xboole_0(B_472,C_473)
      | ~ m1_subset_1(C_473,k1_zfmisc_1(A_471)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2678,plain,(
    ! [B_472] : k9_subset_1('#skF_1',B_472,'#skF_4') = k3_xboole_0(B_472,'#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_2666])).

tff(c_66,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_117,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_2688,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2678,c_2678,c_117])).

tff(c_7091,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4632,c_5802,c_5506,c_5802,c_4187,c_4190,c_2688])).

tff(c_7092,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_8080,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_7092])).

tff(c_31067,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_31056,c_8080])).

tff(c_31081,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_12604,c_11442,c_11700,c_10097,c_11700,c_10097,c_14452,c_31067])).

tff(c_31083,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_31081])).

tff(c_31084,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_7092])).

tff(c_31575,plain,(
    ! [B_1743,A_1744] :
      ( k1_relat_1(B_1743) = A_1744
      | ~ v1_partfun1(B_1743,A_1744)
      | ~ v4_relat_1(B_1743,A_1744)
      | ~ v1_relat_1(B_1743) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_31578,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_8060,c_31575])).

tff(c_31584,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7123,c_31578])).

tff(c_31588,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_31584])).

tff(c_32264,plain,(
    ! [C_1797,A_1798,B_1799] :
      ( v1_partfun1(C_1797,A_1798)
      | ~ v1_funct_2(C_1797,A_1798,B_1799)
      | ~ v1_funct_1(C_1797)
      | ~ m1_subset_1(C_1797,k1_zfmisc_1(k2_zfmisc_1(A_1798,B_1799)))
      | v1_xboole_0(B_1799) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_32270,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_32264])).

tff(c_32277,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_32270])).

tff(c_32279,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_31588,c_32277])).

tff(c_32280,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_31584])).

tff(c_32288,plain,(
    ! [B_23] :
      ( k7_relat_1('#skF_6',B_23) = k1_xboole_0
      | ~ r1_xboole_0(B_23,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32280,c_22])).

tff(c_32800,plain,(
    ! [B_1828] :
      ( k7_relat_1('#skF_6',B_1828) = k1_xboole_0
      | ~ r1_xboole_0(B_1828,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7123,c_32288])).

tff(c_32841,plain,
    ( k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0
    | k7_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8079,c_32800])).

tff(c_32977,plain,(
    k7_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32841])).

tff(c_32297,plain,(
    ! [A_14] :
      ( r1_xboole_0('#skF_4',A_14)
      | k9_relat_1('#skF_6',A_14) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32280,c_18])).

tff(c_32766,plain,(
    ! [A_1827] :
      ( r1_xboole_0('#skF_4',A_1827)
      | k9_relat_1('#skF_6',A_1827) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7123,c_32297])).

tff(c_31203,plain,(
    ! [A_1722,B_1723] :
      ( k7_relat_1(A_1722,B_1723) = k1_xboole_0
      | ~ r1_xboole_0(B_1723,k1_relat_1(A_1722))
      | ~ v1_relat_1(A_1722) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_31230,plain,(
    ! [B_1723] :
      ( k7_relat_1(k1_xboole_0,B_1723) = k1_xboole_0
      | ~ r1_xboole_0(B_1723,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_31203])).

tff(c_31238,plain,(
    ! [B_1723] :
      ( k7_relat_1(k1_xboole_0,B_1723) = k1_xboole_0
      | ~ r1_xboole_0(B_1723,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8043,c_31230])).

tff(c_32794,plain,
    ( k7_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0
    | k9_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32766,c_31238])).

tff(c_34636,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_32977,c_32794])).

tff(c_32300,plain,(
    ! [A_26] :
      ( r1_xboole_0('#skF_4',A_26)
      | k7_relat_1('#skF_6',A_26) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32280,c_32])).

tff(c_32901,plain,(
    ! [A_1832] :
      ( r1_xboole_0('#skF_4',A_1832)
      | k7_relat_1('#skF_6',A_1832) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7123,c_32300])).

tff(c_32285,plain,(
    ! [A_14] :
      ( k9_relat_1('#skF_6',A_14) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_14)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32280,c_16])).

tff(c_32307,plain,(
    ! [A_14] :
      ( k9_relat_1('#skF_6',A_14) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7123,c_32285])).

tff(c_33066,plain,(
    ! [A_1854] :
      ( k9_relat_1('#skF_6',A_1854) = k1_xboole_0
      | k7_relat_1('#skF_6',A_1854) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32901,c_32307])).

tff(c_31581,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_8059,c_31575])).

tff(c_31587,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7122,c_31581])).

tff(c_32330,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_31587])).

tff(c_32570,plain,(
    ! [C_1816,A_1817,B_1818] :
      ( v1_partfun1(C_1816,A_1817)
      | ~ v1_funct_2(C_1816,A_1817,B_1818)
      | ~ v1_funct_1(C_1816)
      | ~ m1_subset_1(C_1816,k1_zfmisc_1(k2_zfmisc_1(A_1817,B_1818)))
      | v1_xboole_0(B_1818) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_32573,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_32570])).

tff(c_32579,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_32573])).

tff(c_32581,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_32330,c_32579])).

tff(c_32582,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_31587])).

tff(c_32590,plain,(
    ! [B_23] :
      ( k7_relat_1('#skF_5',B_23) = k1_xboole_0
      | ~ r1_xboole_0(B_23,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32582,c_22])).

tff(c_32611,plain,(
    ! [B_23] :
      ( k7_relat_1('#skF_5',B_23) = k1_xboole_0
      | ~ r1_xboole_0(B_23,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7122,c_32590])).

tff(c_32791,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | k9_relat_1('#skF_6','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32766,c_32611])).

tff(c_33002,plain,(
    k9_relat_1('#skF_6','#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32791])).

tff(c_33091,plain,(
    k7_relat_1('#skF_6','#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_33066,c_33002])).

tff(c_32599,plain,(
    ! [A_14] :
      ( r1_xboole_0('#skF_3',A_14)
      | k9_relat_1('#skF_5',A_14) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32582,c_18])).

tff(c_32617,plain,(
    ! [A_14] :
      ( r1_xboole_0('#skF_3',A_14)
      | k9_relat_1('#skF_5',A_14) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7122,c_32599])).

tff(c_32835,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | k9_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32617,c_32800])).

tff(c_33185,plain,(
    k9_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_33091,c_32835])).

tff(c_32587,plain,(
    ! [A_14] :
      ( k9_relat_1('#skF_5',A_14) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_14)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32582,c_16])).

tff(c_32714,plain,(
    ! [A_1823] :
      ( k9_relat_1('#skF_5',A_1823) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_1823) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7122,c_32587])).

tff(c_32721,plain,(
    ! [B_29] :
      ( k9_relat_1('#skF_5',B_29) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_29)
      | v1_xboole_0(B_29)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36,c_32714])).

tff(c_33271,plain,(
    ! [B_1874] :
      ( k9_relat_1('#skF_5',B_1874) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_1874)
      | v1_xboole_0(B_1874) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_32721])).

tff(c_33277,plain,
    ( k9_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_33271])).

tff(c_33282,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_33185,c_33277])).

tff(c_33283,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32791])).

tff(c_32602,plain,(
    ! [A_26] :
      ( r1_xboole_0('#skF_3',A_26)
      | k7_relat_1('#skF_5',A_26) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32582,c_32])).

tff(c_32844,plain,(
    ! [A_1829] :
      ( r1_xboole_0('#skF_3',A_1829)
      | k7_relat_1('#skF_5',A_1829) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7122,c_32602])).

tff(c_32609,plain,(
    ! [A_14] :
      ( k9_relat_1('#skF_5',A_14) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7122,c_32587])).

tff(c_34558,plain,(
    ! [A_1978] :
      ( k9_relat_1('#skF_5',A_1978) = k1_xboole_0
      | k7_relat_1('#skF_5',A_1978) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32844,c_32609])).

tff(c_34518,plain,(
    k9_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32835])).

tff(c_34564,plain,(
    k7_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_34558,c_34518])).

tff(c_34592,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33283,c_34564])).

tff(c_34593,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32835])).

tff(c_32939,plain,(
    ! [A_1832] :
      ( k3_xboole_0('#skF_4',A_1832) = k1_xboole_0
      | k7_relat_1('#skF_6',A_1832) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32901,c_2])).

tff(c_34610,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_34593,c_32939])).

tff(c_32291,plain,(
    ! [A_26] :
      ( k7_relat_1('#skF_6',A_26) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_26)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32280,c_30])).

tff(c_32628,plain,(
    ! [A_1819] :
      ( k7_relat_1('#skF_6',A_1819) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_1819) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7123,c_32291])).

tff(c_35086,plain,(
    ! [B_2018] :
      ( k7_relat_1('#skF_6',B_2018) = k1_xboole_0
      | k3_xboole_0('#skF_4',B_2018) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_32628])).

tff(c_35110,plain,(
    ! [B_2018] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),B_2018)
      | ~ v1_relat_1('#skF_6')
      | k3_xboole_0('#skF_4',B_2018) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35086,c_28])).

tff(c_35134,plain,(
    ! [B_2018] :
      ( r1_tarski(k1_xboole_0,B_2018)
      | k3_xboole_0('#skF_4',B_2018) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7123,c_26,c_35110])).

tff(c_34601,plain,(
    ! [B_19] :
      ( k9_relat_1(k1_xboole_0,B_19) = k9_relat_1('#skF_6',B_19)
      | ~ r1_tarski(B_19,'#skF_3')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34593,c_20])).

tff(c_35301,plain,(
    ! [B_2032] :
      ( k9_relat_1(k1_xboole_0,B_2032) = k9_relat_1('#skF_6',B_2032)
      | ~ r1_tarski(B_2032,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7123,c_34601])).

tff(c_35305,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1('#skF_6',k1_xboole_0)
    | k3_xboole_0('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_35134,c_35301])).

tff(c_35335,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34610,c_8042,c_35305])).

tff(c_35337,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34636,c_35335])).

tff(c_35338,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32841])).

tff(c_35486,plain,(
    ! [A_2047] :
      ( k9_relat_1('#skF_6',A_2047) = k1_xboole_0
      | k7_relat_1('#skF_6',A_2047) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32901,c_32307])).

tff(c_35424,plain,(
    k9_relat_1('#skF_6','#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32791])).

tff(c_35511,plain,(
    k7_relat_1('#skF_6','#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_35486,c_35424])).

tff(c_32820,plain,(
    ! [A_28] :
      ( k7_relat_1('#skF_6',A_28) = k1_xboole_0
      | ~ r1_subset_1(A_28,'#skF_4')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_28) ) ),
    inference(resolution,[status(thm)],[c_36,c_32800])).

tff(c_35522,plain,(
    ! [A_2054] :
      ( k7_relat_1('#skF_6',A_2054) = k1_xboole_0
      | ~ r1_subset_1(A_2054,'#skF_4')
      | v1_xboole_0(A_2054) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_32820])).

tff(c_35537,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_35522])).

tff(c_35549,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_35511,c_35537])).

tff(c_35550,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32791])).

tff(c_36998,plain,(
    ! [A_2152] :
      ( k3_xboole_0('#skF_3',A_2152) = k1_xboole_0
      | k7_relat_1('#skF_5',A_2152) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32844,c_2])).

tff(c_37014,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_35550,c_36998])).

tff(c_31520,plain,(
    ! [A_1735,B_1736,C_1737] :
      ( k9_subset_1(A_1735,B_1736,C_1737) = k3_xboole_0(B_1736,C_1737)
      | ~ m1_subset_1(C_1737,k1_zfmisc_1(A_1735)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_31532,plain,(
    ! [B_1736] : k9_subset_1('#skF_1',B_1736,'#skF_4') = k3_xboole_0(B_1736,'#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_31520])).

tff(c_32593,plain,(
    ! [A_26] :
      ( k7_relat_1('#skF_5',A_26) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_26)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32582,c_30])).

tff(c_32880,plain,(
    ! [A_1831] :
      ( k7_relat_1('#skF_5',A_1831) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_1831) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7122,c_32593])).

tff(c_32900,plain,(
    ! [B_2] :
      ( k7_relat_1('#skF_5',B_2) = k1_xboole_0
      | k3_xboole_0('#skF_3',B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_32880])).

tff(c_32873,plain,
    ( k7_relat_1(k1_xboole_0,'#skF_3') = k1_xboole_0
    | k7_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32844,c_31238])).

tff(c_35695,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32873])).

tff(c_35710,plain,(
    k3_xboole_0('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_32900,c_35695])).

tff(c_32641,plain,(
    ! [A_1820] :
      ( r1_xboole_0('#skF_3',A_1820)
      | k9_relat_1('#skF_5',A_1820) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7122,c_32599])).

tff(c_32656,plain,
    ( k7_relat_1(k1_xboole_0,'#skF_3') = k1_xboole_0
    | k9_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32641,c_31238])).

tff(c_35978,plain,(
    k9_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32656])).

tff(c_32309,plain,(
    ! [B_23] :
      ( k7_relat_1('#skF_6',B_23) = k1_xboole_0
      | ~ r1_xboole_0(B_23,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7123,c_32288])).

tff(c_32870,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | k7_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32844,c_32309])).

tff(c_35820,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_35550,c_32870])).

tff(c_35840,plain,(
    ! [A_2081] :
      ( k3_xboole_0('#skF_4',A_2081) = k1_xboole_0
      | k7_relat_1('#skF_6',A_2081) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32901,c_2])).

tff(c_35847,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_35820,c_35840])).

tff(c_32675,plain,(
    ! [B_1822] :
      ( k7_relat_1('#skF_5',B_1822) = k1_xboole_0
      | ~ r1_xboole_0(B_1822,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7122,c_32590])).

tff(c_36137,plain,(
    ! [A_2103] :
      ( k7_relat_1('#skF_5',A_2103) = k1_xboole_0
      | k3_xboole_0(A_2103,'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_32675])).

tff(c_36158,plain,(
    ! [A_2103] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),A_2103)
      | ~ v1_relat_1('#skF_5')
      | k3_xboole_0(A_2103,'#skF_3') != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36137,c_28])).

tff(c_36181,plain,(
    ! [A_2103] :
      ( r1_tarski(k1_xboole_0,A_2103)
      | k3_xboole_0(A_2103,'#skF_3') != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7122,c_26,c_36158])).

tff(c_35555,plain,(
    ! [B_19] :
      ( k9_relat_1(k1_xboole_0,B_19) = k9_relat_1('#skF_5',B_19)
      | ~ r1_tarski(B_19,'#skF_4')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35550,c_20])).

tff(c_36404,plain,(
    ! [B_2119] :
      ( k9_relat_1(k1_xboole_0,B_2119) = k9_relat_1('#skF_5',B_2119)
      | ~ r1_tarski(B_2119,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7122,c_35555])).

tff(c_36408,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1('#skF_5',k1_xboole_0)
    | k3_xboole_0('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36181,c_36404])).

tff(c_36438,plain,(
    k9_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_35847,c_8042,c_36408])).

tff(c_36440,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35978,c_36438])).

tff(c_36442,plain,(
    k9_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32656])).

tff(c_32661,plain,(
    ! [A_1820] :
      ( k3_xboole_0('#skF_3',A_1820) = k1_xboole_0
      | k9_relat_1('#skF_5',A_1820) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32641,c_2])).

tff(c_36493,plain,(
    k3_xboole_0('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_36442,c_32661])).

tff(c_36511,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35710,c_36493])).

tff(c_36513,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32873])).

tff(c_32942,plain,(
    ! [A_1833,B_1834,C_1835,D_1836] :
      ( k2_partfun1(A_1833,B_1834,C_1835,D_1836) = k7_relat_1(C_1835,D_1836)
      | ~ m1_subset_1(C_1835,k1_zfmisc_1(k2_zfmisc_1(A_1833,B_1834)))
      | ~ v1_funct_1(C_1835) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_32944,plain,(
    ! [D_1836] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_1836) = k7_relat_1('#skF_5',D_1836)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_74,c_32942])).

tff(c_32949,plain,(
    ! [D_1836] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_1836) = k7_relat_1('#skF_5',D_1836) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_32944])).

tff(c_32946,plain,(
    ! [D_1836] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_1836) = k7_relat_1('#skF_6',D_1836)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_68,c_32942])).

tff(c_32952,plain,(
    ! [D_1836] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_1836) = k7_relat_1('#skF_6',D_1836) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_32946])).

tff(c_35608,plain,(
    ! [D_2060,E_2058,C_2056,B_2059,F_2061,A_2057] :
      ( v1_funct_1(k1_tmap_1(A_2057,B_2059,C_2056,D_2060,E_2058,F_2061))
      | ~ m1_subset_1(F_2061,k1_zfmisc_1(k2_zfmisc_1(D_2060,B_2059)))
      | ~ v1_funct_2(F_2061,D_2060,B_2059)
      | ~ v1_funct_1(F_2061)
      | ~ m1_subset_1(E_2058,k1_zfmisc_1(k2_zfmisc_1(C_2056,B_2059)))
      | ~ v1_funct_2(E_2058,C_2056,B_2059)
      | ~ v1_funct_1(E_2058)
      | ~ m1_subset_1(D_2060,k1_zfmisc_1(A_2057))
      | v1_xboole_0(D_2060)
      | ~ m1_subset_1(C_2056,k1_zfmisc_1(A_2057))
      | v1_xboole_0(C_2056)
      | v1_xboole_0(B_2059)
      | v1_xboole_0(A_2057) ) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_35612,plain,(
    ! [A_2057,C_2056,E_2058] :
      ( v1_funct_1(k1_tmap_1(A_2057,'#skF_2',C_2056,'#skF_4',E_2058,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_2058,k1_zfmisc_1(k2_zfmisc_1(C_2056,'#skF_2')))
      | ~ v1_funct_2(E_2058,C_2056,'#skF_2')
      | ~ v1_funct_1(E_2058)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2057))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_2056,k1_zfmisc_1(A_2057))
      | v1_xboole_0(C_2056)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_2057) ) ),
    inference(resolution,[status(thm)],[c_68,c_35608])).

tff(c_35619,plain,(
    ! [A_2057,C_2056,E_2058] :
      ( v1_funct_1(k1_tmap_1(A_2057,'#skF_2',C_2056,'#skF_4',E_2058,'#skF_6'))
      | ~ m1_subset_1(E_2058,k1_zfmisc_1(k2_zfmisc_1(C_2056,'#skF_2')))
      | ~ v1_funct_2(E_2058,C_2056,'#skF_2')
      | ~ v1_funct_1(E_2058)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2057))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_2056,k1_zfmisc_1(A_2057))
      | v1_xboole_0(C_2056)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_2057) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_35612])).

tff(c_37397,plain,(
    ! [A_2171,C_2172,E_2173] :
      ( v1_funct_1(k1_tmap_1(A_2171,'#skF_2',C_2172,'#skF_4',E_2173,'#skF_6'))
      | ~ m1_subset_1(E_2173,k1_zfmisc_1(k2_zfmisc_1(C_2172,'#skF_2')))
      | ~ v1_funct_2(E_2173,C_2172,'#skF_2')
      | ~ v1_funct_1(E_2173)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2171))
      | ~ m1_subset_1(C_2172,k1_zfmisc_1(A_2171))
      | v1_xboole_0(C_2172)
      | v1_xboole_0(A_2171) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_35619])).

tff(c_37402,plain,(
    ! [A_2171] :
      ( v1_funct_1(k1_tmap_1(A_2171,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2171))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_2171))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2171) ) ),
    inference(resolution,[status(thm)],[c_74,c_37397])).

tff(c_37410,plain,(
    ! [A_2171] :
      ( v1_funct_1(k1_tmap_1(A_2171,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2171))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_2171))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_37402])).

tff(c_37689,plain,(
    ! [A_2182] :
      ( v1_funct_1(k1_tmap_1(A_2182,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2182))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_2182))
      | v1_xboole_0(A_2182) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_37410])).

tff(c_37692,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_86,c_37689])).

tff(c_37695,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_37692])).

tff(c_37696,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_37695])).

tff(c_36840,plain,(
    ! [B_2142,E_2141,D_2143,C_2144,F_2140,A_2145] :
      ( k2_partfun1(k4_subset_1(A_2145,C_2144,D_2143),B_2142,k1_tmap_1(A_2145,B_2142,C_2144,D_2143,E_2141,F_2140),C_2144) = E_2141
      | ~ m1_subset_1(k1_tmap_1(A_2145,B_2142,C_2144,D_2143,E_2141,F_2140),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_2145,C_2144,D_2143),B_2142)))
      | ~ v1_funct_2(k1_tmap_1(A_2145,B_2142,C_2144,D_2143,E_2141,F_2140),k4_subset_1(A_2145,C_2144,D_2143),B_2142)
      | ~ v1_funct_1(k1_tmap_1(A_2145,B_2142,C_2144,D_2143,E_2141,F_2140))
      | k2_partfun1(D_2143,B_2142,F_2140,k9_subset_1(A_2145,C_2144,D_2143)) != k2_partfun1(C_2144,B_2142,E_2141,k9_subset_1(A_2145,C_2144,D_2143))
      | ~ m1_subset_1(F_2140,k1_zfmisc_1(k2_zfmisc_1(D_2143,B_2142)))
      | ~ v1_funct_2(F_2140,D_2143,B_2142)
      | ~ v1_funct_1(F_2140)
      | ~ m1_subset_1(E_2141,k1_zfmisc_1(k2_zfmisc_1(C_2144,B_2142)))
      | ~ v1_funct_2(E_2141,C_2144,B_2142)
      | ~ v1_funct_1(E_2141)
      | ~ m1_subset_1(D_2143,k1_zfmisc_1(A_2145))
      | v1_xboole_0(D_2143)
      | ~ m1_subset_1(C_2144,k1_zfmisc_1(A_2145))
      | v1_xboole_0(C_2144)
      | v1_xboole_0(B_2142)
      | v1_xboole_0(A_2145) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_45304,plain,(
    ! [E_2426,F_2429,D_2428,C_2424,B_2427,A_2425] :
      ( k2_partfun1(k4_subset_1(A_2425,C_2424,D_2428),B_2427,k1_tmap_1(A_2425,B_2427,C_2424,D_2428,E_2426,F_2429),C_2424) = E_2426
      | ~ v1_funct_2(k1_tmap_1(A_2425,B_2427,C_2424,D_2428,E_2426,F_2429),k4_subset_1(A_2425,C_2424,D_2428),B_2427)
      | ~ v1_funct_1(k1_tmap_1(A_2425,B_2427,C_2424,D_2428,E_2426,F_2429))
      | k2_partfun1(D_2428,B_2427,F_2429,k9_subset_1(A_2425,C_2424,D_2428)) != k2_partfun1(C_2424,B_2427,E_2426,k9_subset_1(A_2425,C_2424,D_2428))
      | ~ m1_subset_1(F_2429,k1_zfmisc_1(k2_zfmisc_1(D_2428,B_2427)))
      | ~ v1_funct_2(F_2429,D_2428,B_2427)
      | ~ v1_funct_1(F_2429)
      | ~ m1_subset_1(E_2426,k1_zfmisc_1(k2_zfmisc_1(C_2424,B_2427)))
      | ~ v1_funct_2(E_2426,C_2424,B_2427)
      | ~ v1_funct_1(E_2426)
      | ~ m1_subset_1(D_2428,k1_zfmisc_1(A_2425))
      | v1_xboole_0(D_2428)
      | ~ m1_subset_1(C_2424,k1_zfmisc_1(A_2425))
      | v1_xboole_0(C_2424)
      | v1_xboole_0(B_2427)
      | v1_xboole_0(A_2425) ) ),
    inference(resolution,[status(thm)],[c_60,c_36840])).

tff(c_50814,plain,(
    ! [C_2565,D_2569,F_2570,B_2568,A_2566,E_2567] :
      ( k2_partfun1(k4_subset_1(A_2566,C_2565,D_2569),B_2568,k1_tmap_1(A_2566,B_2568,C_2565,D_2569,E_2567,F_2570),C_2565) = E_2567
      | ~ v1_funct_1(k1_tmap_1(A_2566,B_2568,C_2565,D_2569,E_2567,F_2570))
      | k2_partfun1(D_2569,B_2568,F_2570,k9_subset_1(A_2566,C_2565,D_2569)) != k2_partfun1(C_2565,B_2568,E_2567,k9_subset_1(A_2566,C_2565,D_2569))
      | ~ m1_subset_1(F_2570,k1_zfmisc_1(k2_zfmisc_1(D_2569,B_2568)))
      | ~ v1_funct_2(F_2570,D_2569,B_2568)
      | ~ v1_funct_1(F_2570)
      | ~ m1_subset_1(E_2567,k1_zfmisc_1(k2_zfmisc_1(C_2565,B_2568)))
      | ~ v1_funct_2(E_2567,C_2565,B_2568)
      | ~ v1_funct_1(E_2567)
      | ~ m1_subset_1(D_2569,k1_zfmisc_1(A_2566))
      | v1_xboole_0(D_2569)
      | ~ m1_subset_1(C_2565,k1_zfmisc_1(A_2566))
      | v1_xboole_0(C_2565)
      | v1_xboole_0(B_2568)
      | v1_xboole_0(A_2566) ) ),
    inference(resolution,[status(thm)],[c_62,c_45304])).

tff(c_50820,plain,(
    ! [A_2566,C_2565,E_2567] :
      ( k2_partfun1(k4_subset_1(A_2566,C_2565,'#skF_4'),'#skF_2',k1_tmap_1(A_2566,'#skF_2',C_2565,'#skF_4',E_2567,'#skF_6'),C_2565) = E_2567
      | ~ v1_funct_1(k1_tmap_1(A_2566,'#skF_2',C_2565,'#skF_4',E_2567,'#skF_6'))
      | k2_partfun1(C_2565,'#skF_2',E_2567,k9_subset_1(A_2566,C_2565,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_2566,C_2565,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_2567,k1_zfmisc_1(k2_zfmisc_1(C_2565,'#skF_2')))
      | ~ v1_funct_2(E_2567,C_2565,'#skF_2')
      | ~ v1_funct_1(E_2567)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2566))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_2565,k1_zfmisc_1(A_2566))
      | v1_xboole_0(C_2565)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_2566) ) ),
    inference(resolution,[status(thm)],[c_68,c_50814])).

tff(c_50828,plain,(
    ! [A_2566,C_2565,E_2567] :
      ( k2_partfun1(k4_subset_1(A_2566,C_2565,'#skF_4'),'#skF_2',k1_tmap_1(A_2566,'#skF_2',C_2565,'#skF_4',E_2567,'#skF_6'),C_2565) = E_2567
      | ~ v1_funct_1(k1_tmap_1(A_2566,'#skF_2',C_2565,'#skF_4',E_2567,'#skF_6'))
      | k2_partfun1(C_2565,'#skF_2',E_2567,k9_subset_1(A_2566,C_2565,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2566,C_2565,'#skF_4'))
      | ~ m1_subset_1(E_2567,k1_zfmisc_1(k2_zfmisc_1(C_2565,'#skF_2')))
      | ~ v1_funct_2(E_2567,C_2565,'#skF_2')
      | ~ v1_funct_1(E_2567)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2566))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_2565,k1_zfmisc_1(A_2566))
      | v1_xboole_0(C_2565)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_2566) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_32952,c_50820])).

tff(c_53643,plain,(
    ! [A_2614,C_2615,E_2616] :
      ( k2_partfun1(k4_subset_1(A_2614,C_2615,'#skF_4'),'#skF_2',k1_tmap_1(A_2614,'#skF_2',C_2615,'#skF_4',E_2616,'#skF_6'),C_2615) = E_2616
      | ~ v1_funct_1(k1_tmap_1(A_2614,'#skF_2',C_2615,'#skF_4',E_2616,'#skF_6'))
      | k2_partfun1(C_2615,'#skF_2',E_2616,k9_subset_1(A_2614,C_2615,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2614,C_2615,'#skF_4'))
      | ~ m1_subset_1(E_2616,k1_zfmisc_1(k2_zfmisc_1(C_2615,'#skF_2')))
      | ~ v1_funct_2(E_2616,C_2615,'#skF_2')
      | ~ v1_funct_1(E_2616)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2614))
      | ~ m1_subset_1(C_2615,k1_zfmisc_1(A_2614))
      | v1_xboole_0(C_2615)
      | v1_xboole_0(A_2614) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_50828])).

tff(c_53648,plain,(
    ! [A_2614] :
      ( k2_partfun1(k4_subset_1(A_2614,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_2614,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_2614,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_2614,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2614,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2614))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_2614))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2614) ) ),
    inference(resolution,[status(thm)],[c_74,c_53643])).

tff(c_53656,plain,(
    ! [A_2614] :
      ( k2_partfun1(k4_subset_1(A_2614,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_2614,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_2614,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_2614,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2614,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2614))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_2614))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2614) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_32949,c_53648])).

tff(c_53924,plain,(
    ! [A_2630] :
      ( k2_partfun1(k4_subset_1(A_2630,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_2630,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_2630,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_2630,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2630,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2630))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_2630))
      | v1_xboole_0(A_2630) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_53656])).

tff(c_31085,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_7092])).

tff(c_37015,plain,(
    ! [B_2153,C_2155,D_2154,A_2156,G_2157] :
      ( k1_tmap_1(A_2156,B_2153,C_2155,D_2154,k2_partfun1(k4_subset_1(A_2156,C_2155,D_2154),B_2153,G_2157,C_2155),k2_partfun1(k4_subset_1(A_2156,C_2155,D_2154),B_2153,G_2157,D_2154)) = G_2157
      | ~ m1_subset_1(G_2157,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_2156,C_2155,D_2154),B_2153)))
      | ~ v1_funct_2(G_2157,k4_subset_1(A_2156,C_2155,D_2154),B_2153)
      | ~ v1_funct_1(G_2157)
      | k2_partfun1(D_2154,B_2153,k2_partfun1(k4_subset_1(A_2156,C_2155,D_2154),B_2153,G_2157,D_2154),k9_subset_1(A_2156,C_2155,D_2154)) != k2_partfun1(C_2155,B_2153,k2_partfun1(k4_subset_1(A_2156,C_2155,D_2154),B_2153,G_2157,C_2155),k9_subset_1(A_2156,C_2155,D_2154))
      | ~ m1_subset_1(k2_partfun1(k4_subset_1(A_2156,C_2155,D_2154),B_2153,G_2157,D_2154),k1_zfmisc_1(k2_zfmisc_1(D_2154,B_2153)))
      | ~ v1_funct_2(k2_partfun1(k4_subset_1(A_2156,C_2155,D_2154),B_2153,G_2157,D_2154),D_2154,B_2153)
      | ~ v1_funct_1(k2_partfun1(k4_subset_1(A_2156,C_2155,D_2154),B_2153,G_2157,D_2154))
      | ~ m1_subset_1(k2_partfun1(k4_subset_1(A_2156,C_2155,D_2154),B_2153,G_2157,C_2155),k1_zfmisc_1(k2_zfmisc_1(C_2155,B_2153)))
      | ~ v1_funct_2(k2_partfun1(k4_subset_1(A_2156,C_2155,D_2154),B_2153,G_2157,C_2155),C_2155,B_2153)
      | ~ v1_funct_1(k2_partfun1(k4_subset_1(A_2156,C_2155,D_2154),B_2153,G_2157,C_2155))
      | ~ m1_subset_1(D_2154,k1_zfmisc_1(A_2156))
      | v1_xboole_0(D_2154)
      | ~ m1_subset_1(C_2155,k1_zfmisc_1(A_2156))
      | v1_xboole_0(C_2155)
      | v1_xboole_0(B_2153)
      | v1_xboole_0(A_2156) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_37017,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_31085,c_37015])).

tff(c_37019,plain,
    ( k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_6') = k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')))
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k2_partfun1('#skF_3','#skF_2',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k3_xboole_0('#skF_3','#skF_4')) != k7_relat_1('#skF_6',k3_xboole_0('#skF_3','#skF_4'))
    | ~ m1_subset_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'))
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_72,c_31085,c_70,c_31085,c_68,c_32952,c_31085,c_31532,c_31532,c_31085,c_37017])).

tff(c_37020,plain,
    ( k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_6') = k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')))
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k2_partfun1('#skF_3','#skF_2',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k3_xboole_0('#skF_3','#skF_4')) != k7_relat_1('#skF_6',k3_xboole_0('#skF_3','#skF_4'))
    | ~ m1_subset_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_90,c_88,c_84,c_37019])).

tff(c_38985,plain,
    ( k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_6') = k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')))
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | k2_partfun1('#skF_3','#skF_2',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_xboole_0) != k1_xboole_0
    | ~ m1_subset_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35338,c_37014,c_37014,c_37696,c_37020])).

tff(c_38986,plain,(
    ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_38985])).

tff(c_53933,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_53924,c_38986])).

tff(c_53946,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_35338,c_37014,c_31532,c_36513,c_37014,c_31532,c_37696,c_78,c_53933])).

tff(c_53948,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_53946])).

tff(c_53949,plain,
    ( ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | k2_partfun1('#skF_3','#skF_2',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_xboole_0) != k1_xboole_0
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')))
    | k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_6') = k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_38985])).

tff(c_54848,plain,(
    ~ m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_53949])).

tff(c_55374,plain,
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
    inference(resolution,[status(thm)],[c_60,c_54848])).

tff(c_55377,plain,
    ( v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_78,c_76,c_74,c_72,c_70,c_68,c_55374])).

tff(c_55379,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_90,c_88,c_84,c_55377])).

tff(c_55381,plain,(
    m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_53949])).

tff(c_58,plain,(
    ! [A_46,E_166,F_170,B_110,D_158,C_142] :
      ( k2_partfun1(k4_subset_1(A_46,C_142,D_158),B_110,k1_tmap_1(A_46,B_110,C_142,D_158,E_166,F_170),C_142) = E_166
      | ~ m1_subset_1(k1_tmap_1(A_46,B_110,C_142,D_158,E_166,F_170),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_46,C_142,D_158),B_110)))
      | ~ v1_funct_2(k1_tmap_1(A_46,B_110,C_142,D_158,E_166,F_170),k4_subset_1(A_46,C_142,D_158),B_110)
      | ~ v1_funct_1(k1_tmap_1(A_46,B_110,C_142,D_158,E_166,F_170))
      | k2_partfun1(D_158,B_110,F_170,k9_subset_1(A_46,C_142,D_158)) != k2_partfun1(C_142,B_110,E_166,k9_subset_1(A_46,C_142,D_158))
      | ~ m1_subset_1(F_170,k1_zfmisc_1(k2_zfmisc_1(D_158,B_110)))
      | ~ v1_funct_2(F_170,D_158,B_110)
      | ~ v1_funct_1(F_170)
      | ~ m1_subset_1(E_166,k1_zfmisc_1(k2_zfmisc_1(C_142,B_110)))
      | ~ v1_funct_2(E_166,C_142,B_110)
      | ~ v1_funct_1(E_166)
      | ~ m1_subset_1(D_158,k1_zfmisc_1(A_46))
      | v1_xboole_0(D_158)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(A_46))
      | v1_xboole_0(C_142)
      | v1_xboole_0(B_110)
      | v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_55910,plain,
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
    inference(resolution,[status(thm)],[c_55381,c_58])).

tff(c_55942,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_78,c_76,c_74,c_72,c_70,c_68,c_35338,c_37014,c_31532,c_36513,c_37014,c_31532,c_32949,c_32952,c_37696,c_55910])).

tff(c_55943,plain,(
    ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_90,c_88,c_84,c_31084,c_55942])).

tff(c_55975,plain,
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
    inference(resolution,[status(thm)],[c_62,c_55943])).

tff(c_55978,plain,
    ( v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_78,c_76,c_74,c_72,c_70,c_68,c_55975])).

tff(c_55980,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_90,c_88,c_84,c_55978])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:39:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.37/8.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.63/8.31  
% 16.63/8.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.63/8.32  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 16.63/8.32  
% 16.63/8.32  %Foreground sorts:
% 16.63/8.32  
% 16.63/8.32  
% 16.63/8.32  %Background operators:
% 16.63/8.32  
% 16.63/8.32  
% 16.63/8.32  %Foreground operators:
% 16.63/8.32  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 16.63/8.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 16.63/8.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.63/8.32  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 16.63/8.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.63/8.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.63/8.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 16.63/8.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 16.63/8.32  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 16.63/8.32  tff('#skF_5', type, '#skF_5': $i).
% 16.63/8.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 16.63/8.32  tff('#skF_6', type, '#skF_6': $i).
% 16.63/8.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 16.63/8.32  tff('#skF_2', type, '#skF_2': $i).
% 16.63/8.32  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 16.63/8.32  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 16.63/8.32  tff('#skF_3', type, '#skF_3': $i).
% 16.63/8.32  tff('#skF_1', type, '#skF_1': $i).
% 16.63/8.32  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 16.63/8.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.63/8.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.63/8.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 16.63/8.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 16.63/8.32  tff('#skF_4', type, '#skF_4': $i).
% 16.63/8.32  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 16.63/8.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.63/8.32  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 16.63/8.32  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 16.63/8.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 16.63/8.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 16.63/8.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 16.63/8.32  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 16.63/8.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.63/8.32  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 16.63/8.32  
% 16.97/8.37  tff(f_255, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 16.97/8.37  tff(f_213, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 16.97/8.37  tff(f_93, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 16.97/8.37  tff(f_73, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 16.97/8.37  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 16.97/8.37  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 16.97/8.37  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 16.97/8.37  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 16.97/8.37  tff(f_125, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 16.97/8.37  tff(f_117, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 16.97/8.37  tff(f_83, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 16.97/8.37  tff(f_46, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 16.97/8.37  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 16.97/8.37  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 16.97/8.37  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 16.97/8.37  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 16.97/8.37  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 16.97/8.37  tff(f_131, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 16.97/8.37  tff(f_179, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 16.97/8.37  tff(c_92, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_255])).
% 16.97/8.37  tff(c_90, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_255])).
% 16.97/8.37  tff(c_88, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_255])).
% 16.97/8.37  tff(c_84, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_255])).
% 16.97/8.37  tff(c_86, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_255])).
% 16.97/8.37  tff(c_82, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_255])).
% 16.97/8.37  tff(c_78, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_255])).
% 16.97/8.37  tff(c_76, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_255])).
% 16.97/8.37  tff(c_74, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_255])).
% 16.97/8.37  tff(c_72, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_255])).
% 16.97/8.37  tff(c_70, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_255])).
% 16.97/8.37  tff(c_68, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_255])).
% 16.97/8.37  tff(c_62, plain, (![E_177, F_178, B_174, D_176, C_175, A_173]: (v1_funct_2(k1_tmap_1(A_173, B_174, C_175, D_176, E_177, F_178), k4_subset_1(A_173, C_175, D_176), B_174) | ~m1_subset_1(F_178, k1_zfmisc_1(k2_zfmisc_1(D_176, B_174))) | ~v1_funct_2(F_178, D_176, B_174) | ~v1_funct_1(F_178) | ~m1_subset_1(E_177, k1_zfmisc_1(k2_zfmisc_1(C_175, B_174))) | ~v1_funct_2(E_177, C_175, B_174) | ~v1_funct_1(E_177) | ~m1_subset_1(D_176, k1_zfmisc_1(A_173)) | v1_xboole_0(D_176) | ~m1_subset_1(C_175, k1_zfmisc_1(A_173)) | v1_xboole_0(C_175) | v1_xboole_0(B_174) | v1_xboole_0(A_173))), inference(cnfTransformation, [status(thm)], [f_213])).
% 16.97/8.37  tff(c_80, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_255])).
% 16.97/8.37  tff(c_36, plain, (![A_28, B_29]: (r1_xboole_0(A_28, B_29) | ~r1_subset_1(A_28, B_29) | v1_xboole_0(B_29) | v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_93])).
% 16.97/8.37  tff(c_24, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 16.97/8.37  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 16.97/8.37  tff(c_7125, plain, (![A_788]: (k9_relat_1(A_788, k1_relat_1(A_788))=k2_relat_1(A_788) | ~v1_relat_1(A_788))), inference(cnfTransformation, [status(thm)], [f_50])).
% 16.97/8.37  tff(c_7134, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_7125])).
% 16.97/8.37  tff(c_7137, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_7134])).
% 16.97/8.37  tff(c_7138, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_7137])).
% 16.97/8.37  tff(c_7115, plain, (![C_783, A_784, B_785]: (v1_relat_1(C_783) | ~m1_subset_1(C_783, k1_zfmisc_1(k2_zfmisc_1(A_784, B_785))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 16.97/8.37  tff(c_7122, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_7115])).
% 16.97/8.37  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 16.97/8.37  tff(c_7139, plain, (![C_789, A_790, B_791]: (v4_relat_1(C_789, A_790) | ~m1_subset_1(C_789, k1_zfmisc_1(k2_zfmisc_1(A_790, B_791))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 16.97/8.37  tff(c_7146, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_7139])).
% 16.97/8.37  tff(c_7303, plain, (![B_813, A_814]: (k1_relat_1(B_813)=A_814 | ~v1_partfun1(B_813, A_814) | ~v4_relat_1(B_813, A_814) | ~v1_relat_1(B_813))), inference(cnfTransformation, [status(thm)], [f_125])).
% 16.97/8.37  tff(c_7309, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_7146, c_7303])).
% 16.97/8.37  tff(c_7315, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7122, c_7309])).
% 16.97/8.37  tff(c_7317, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_7315])).
% 16.97/8.37  tff(c_7624, plain, (![C_850, A_851, B_852]: (v1_partfun1(C_850, A_851) | ~v1_funct_2(C_850, A_851, B_852) | ~v1_funct_1(C_850) | ~m1_subset_1(C_850, k1_zfmisc_1(k2_zfmisc_1(A_851, B_852))) | v1_xboole_0(B_852))), inference(cnfTransformation, [status(thm)], [f_117])).
% 16.97/8.37  tff(c_7627, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_74, c_7624])).
% 16.97/8.37  tff(c_7633, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_7627])).
% 16.97/8.37  tff(c_7635, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_7317, c_7633])).
% 16.97/8.37  tff(c_7636, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_7315])).
% 16.97/8.37  tff(c_30, plain, (![B_27, A_26]: (k7_relat_1(B_27, A_26)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_27), A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_83])).
% 16.97/8.37  tff(c_7650, plain, (![A_26]: (k7_relat_1('#skF_5', A_26)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_26) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_7636, c_30])).
% 16.97/8.37  tff(c_7716, plain, (![A_855]: (k7_relat_1('#skF_5', A_855)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_855))), inference(demodulation, [status(thm), theory('equality')], [c_7122, c_7650])).
% 16.97/8.37  tff(c_7932, plain, (![B_872]: (k7_relat_1('#skF_5', B_872)=k1_xboole_0 | k3_xboole_0('#skF_3', B_872)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_7716])).
% 16.97/8.37  tff(c_12, plain, (![A_11, B_12]: (v1_relat_1(k7_relat_1(A_11, B_12)) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 16.97/8.37  tff(c_7950, plain, (![B_872]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_5') | k3_xboole_0('#skF_3', B_872)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7932, c_12])).
% 16.97/8.37  tff(c_7962, plain, (![B_872]: (v1_relat_1(k1_xboole_0) | k3_xboole_0('#skF_3', B_872)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7122, c_7950])).
% 16.97/8.37  tff(c_7963, plain, (![B_872]: (k3_xboole_0('#skF_3', B_872)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_7138, c_7962])).
% 16.97/8.37  tff(c_32, plain, (![B_27, A_26]: (r1_xboole_0(k1_relat_1(B_27), A_26) | k7_relat_1(B_27, A_26)!=k1_xboole_0 | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_83])).
% 16.97/8.37  tff(c_7647, plain, (![A_26]: (r1_xboole_0('#skF_3', A_26) | k7_relat_1('#skF_5', A_26)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_7636, c_32])).
% 16.97/8.37  tff(c_7733, plain, (![A_856]: (r1_xboole_0('#skF_3', A_856) | k7_relat_1('#skF_5', A_856)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7122, c_7647])).
% 16.97/8.37  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 16.97/8.37  tff(c_7756, plain, (![A_856]: (k3_xboole_0('#skF_3', A_856)=k1_xboole_0 | k7_relat_1('#skF_5', A_856)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_7733, c_2])).
% 16.97/8.37  tff(c_7965, plain, (![A_856]: (k7_relat_1('#skF_5', A_856)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_7963, c_7756])).
% 16.97/8.37  tff(c_7669, plain, (![A_26]: (k7_relat_1('#skF_5', A_26)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_26))), inference(demodulation, [status(thm), theory('equality')], [c_7122, c_7650])).
% 16.97/8.37  tff(c_8000, plain, (![A_876]: (~r1_xboole_0('#skF_3', A_876))), inference(negUnitSimplification, [status(thm)], [c_7965, c_7669])).
% 16.97/8.37  tff(c_8004, plain, (![B_29]: (~r1_subset_1('#skF_3', B_29) | v1_xboole_0(B_29) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_8000])).
% 16.97/8.37  tff(c_8034, plain, (![B_883]: (~r1_subset_1('#skF_3', B_883) | v1_xboole_0(B_883))), inference(negUnitSimplification, [status(thm)], [c_88, c_8004])).
% 16.97/8.37  tff(c_8037, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_80, c_8034])).
% 16.97/8.37  tff(c_8041, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_8037])).
% 16.97/8.37  tff(c_8043, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_7137])).
% 16.97/8.37  tff(c_8070, plain, (![B_890, A_891]: (r1_xboole_0(k1_relat_1(B_890), A_891) | k7_relat_1(B_890, A_891)!=k1_xboole_0 | ~v1_relat_1(B_890))), inference(cnfTransformation, [status(thm)], [f_83])).
% 16.97/8.37  tff(c_8076, plain, (![A_891]: (r1_xboole_0(k1_xboole_0, A_891) | k7_relat_1(k1_xboole_0, A_891)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_8070])).
% 16.97/8.37  tff(c_8079, plain, (![A_891]: (r1_xboole_0(k1_xboole_0, A_891) | k7_relat_1(k1_xboole_0, A_891)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8043, c_8076])).
% 16.97/8.37  tff(c_8286, plain, (![B_909, A_910]: (k9_relat_1(B_909, A_910)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_909), A_910) | ~v1_relat_1(B_909))), inference(cnfTransformation, [status(thm)], [f_56])).
% 16.97/8.37  tff(c_8303, plain, (![A_910]: (k9_relat_1(k1_xboole_0, A_910)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_910) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_8286])).
% 16.97/8.37  tff(c_8310, plain, (![A_911]: (k9_relat_1(k1_xboole_0, A_911)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_911))), inference(demodulation, [status(thm), theory('equality')], [c_8043, c_8303])).
% 16.97/8.37  tff(c_8327, plain, (![A_891]: (k9_relat_1(k1_xboole_0, A_891)=k1_xboole_0 | k7_relat_1(k1_xboole_0, A_891)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8079, c_8310])).
% 16.97/8.37  tff(c_8109, plain, (![B_898, A_899]: (r1_xboole_0(k1_relat_1(B_898), A_899) | k9_relat_1(B_898, A_899)!=k1_xboole_0 | ~v1_relat_1(B_898))), inference(cnfTransformation, [status(thm)], [f_56])).
% 16.97/8.37  tff(c_8118, plain, (![A_899]: (r1_xboole_0(k1_xboole_0, A_899) | k9_relat_1(k1_xboole_0, A_899)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_8109])).
% 16.97/8.37  tff(c_8122, plain, (![A_899]: (r1_xboole_0(k1_xboole_0, A_899) | k9_relat_1(k1_xboole_0, A_899)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8043, c_8118])).
% 16.97/8.37  tff(c_8052, plain, (![C_884, A_885, B_886]: (v4_relat_1(C_884, A_885) | ~m1_subset_1(C_884, k1_zfmisc_1(k2_zfmisc_1(A_885, B_886))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 16.97/8.37  tff(c_8059, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_8052])).
% 16.97/8.37  tff(c_8409, plain, (![B_916, A_917]: (k1_relat_1(B_916)=A_917 | ~v1_partfun1(B_916, A_917) | ~v4_relat_1(B_916, A_917) | ~v1_relat_1(B_916))), inference(cnfTransformation, [status(thm)], [f_125])).
% 16.97/8.37  tff(c_8415, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_8059, c_8409])).
% 16.97/8.37  tff(c_8421, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7122, c_8415])).
% 16.97/8.37  tff(c_9475, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_8421])).
% 16.97/8.37  tff(c_9929, plain, (![C_1026, A_1027, B_1028]: (v1_partfun1(C_1026, A_1027) | ~v1_funct_2(C_1026, A_1027, B_1028) | ~v1_funct_1(C_1026) | ~m1_subset_1(C_1026, k1_zfmisc_1(k2_zfmisc_1(A_1027, B_1028))) | v1_xboole_0(B_1028))), inference(cnfTransformation, [status(thm)], [f_117])).
% 16.97/8.37  tff(c_9932, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_74, c_9929])).
% 16.97/8.37  tff(c_9938, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_9932])).
% 16.97/8.37  tff(c_9940, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_9475, c_9938])).
% 16.97/8.37  tff(c_9941, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_8421])).
% 16.97/8.37  tff(c_22, plain, (![A_21, B_23]: (k7_relat_1(A_21, B_23)=k1_xboole_0 | ~r1_xboole_0(B_23, k1_relat_1(A_21)) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_70])).
% 16.97/8.37  tff(c_9949, plain, (![B_23]: (k7_relat_1('#skF_5', B_23)=k1_xboole_0 | ~r1_xboole_0(B_23, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_9941, c_22])).
% 16.97/8.37  tff(c_9991, plain, (![B_1029]: (k7_relat_1('#skF_5', B_1029)=k1_xboole_0 | ~r1_xboole_0(B_1029, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7122, c_9949])).
% 16.97/8.37  tff(c_10016, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0 | k9_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_8122, c_9991])).
% 16.97/8.37  tff(c_11783, plain, (k9_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_10016])).
% 16.97/8.37  tff(c_11790, plain, (k7_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_8327, c_11783])).
% 16.97/8.37  tff(c_18, plain, (![B_15, A_14]: (r1_xboole_0(k1_relat_1(B_15), A_14) | k9_relat_1(B_15, A_14)!=k1_xboole_0 | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 16.97/8.37  tff(c_9958, plain, (![A_14]: (r1_xboole_0('#skF_3', A_14) | k9_relat_1('#skF_5', A_14)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_9941, c_18])).
% 16.97/8.37  tff(c_10024, plain, (![A_1030]: (r1_xboole_0('#skF_3', A_1030) | k9_relat_1('#skF_5', A_1030)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7122, c_9958])).
% 16.97/8.37  tff(c_8198, plain, (![A_906, B_907]: (k7_relat_1(A_906, B_907)=k1_xboole_0 | ~r1_xboole_0(B_907, k1_relat_1(A_906)) | ~v1_relat_1(A_906))), inference(cnfTransformation, [status(thm)], [f_70])).
% 16.97/8.37  tff(c_8225, plain, (![B_907]: (k7_relat_1(k1_xboole_0, B_907)=k1_xboole_0 | ~r1_xboole_0(B_907, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_8198])).
% 16.97/8.37  tff(c_8233, plain, (![B_907]: (k7_relat_1(k1_xboole_0, B_907)=k1_xboole_0 | ~r1_xboole_0(B_907, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8043, c_8225])).
% 16.97/8.37  tff(c_10045, plain, (k7_relat_1(k1_xboole_0, '#skF_3')=k1_xboole_0 | k9_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_10024, c_8233])).
% 16.97/8.37  tff(c_12021, plain, (k9_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_11790, c_10045])).
% 16.97/8.37  tff(c_9961, plain, (![A_26]: (r1_xboole_0('#skF_3', A_26) | k7_relat_1('#skF_5', A_26)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_9941, c_32])).
% 16.97/8.37  tff(c_9978, plain, (![A_26]: (r1_xboole_0('#skF_3', A_26) | k7_relat_1('#skF_5', A_26)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7122, c_9961])).
% 16.97/8.37  tff(c_7123, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_68, c_7115])).
% 16.97/8.37  tff(c_8060, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_68, c_8052])).
% 16.97/8.37  tff(c_8412, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_8060, c_8409])).
% 16.97/8.37  tff(c_8418, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7123, c_8412])).
% 16.97/8.37  tff(c_8422, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_8418])).
% 16.97/8.37  tff(c_9417, plain, (![C_995, A_996, B_997]: (v1_partfun1(C_995, A_996) | ~v1_funct_2(C_995, A_996, B_997) | ~v1_funct_1(C_995) | ~m1_subset_1(C_995, k1_zfmisc_1(k2_zfmisc_1(A_996, B_997))) | v1_xboole_0(B_997))), inference(cnfTransformation, [status(thm)], [f_117])).
% 16.97/8.37  tff(c_9423, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_9417])).
% 16.97/8.37  tff(c_9430, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_9423])).
% 16.97/8.37  tff(c_9432, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_8422, c_9430])).
% 16.97/8.37  tff(c_9433, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_8418])).
% 16.97/8.37  tff(c_9441, plain, (![B_23]: (k7_relat_1('#skF_6', B_23)=k1_xboole_0 | ~r1_xboole_0(B_23, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_9433, c_22])).
% 16.97/8.37  tff(c_10254, plain, (![B_1044]: (k7_relat_1('#skF_6', B_1044)=k1_xboole_0 | ~r1_xboole_0(B_1044, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7123, c_9441])).
% 16.97/8.37  tff(c_10295, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | k7_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_9978, c_10254])).
% 16.97/8.37  tff(c_11597, plain, (k7_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_10295])).
% 16.97/8.37  tff(c_10282, plain, (![A_28]: (k7_relat_1('#skF_6', A_28)=k1_xboole_0 | ~r1_subset_1(A_28, '#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(A_28))), inference(resolution, [status(thm)], [c_36, c_10254])).
% 16.97/8.37  tff(c_11598, plain, (![A_1160]: (k7_relat_1('#skF_6', A_1160)=k1_xboole_0 | ~r1_subset_1(A_1160, '#skF_4') | v1_xboole_0(A_1160))), inference(negUnitSimplification, [status(thm)], [c_84, c_10282])).
% 16.97/8.37  tff(c_11605, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_80, c_11598])).
% 16.97/8.37  tff(c_11611, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_88, c_11605])).
% 16.97/8.37  tff(c_9453, plain, (![A_26]: (r1_xboole_0('#skF_4', A_26) | k7_relat_1('#skF_6', A_26)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_9433, c_32])).
% 16.97/8.37  tff(c_10186, plain, (![A_1042]: (r1_xboole_0('#skF_4', A_1042) | k7_relat_1('#skF_6', A_1042)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7123, c_9453])).
% 16.97/8.37  tff(c_9970, plain, (![B_23]: (k7_relat_1('#skF_5', B_23)=k1_xboole_0 | ~r1_xboole_0(B_23, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7122, c_9949])).
% 16.97/8.37  tff(c_10213, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | k7_relat_1('#skF_6', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_10186, c_9970])).
% 16.97/8.37  tff(c_11632, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_11611, c_10213])).
% 16.97/8.37  tff(c_11633, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11597, c_11632])).
% 16.97/8.37  tff(c_11634, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_10295])).
% 16.97/8.37  tff(c_11713, plain, (![A_1168]: (k3_xboole_0('#skF_4', A_1168)=k1_xboole_0 | k7_relat_1('#skF_6', A_1168)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10186, c_2])).
% 16.97/8.37  tff(c_11720, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_11634, c_11713])).
% 16.97/8.37  tff(c_8042, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_7137])).
% 16.97/8.37  tff(c_11944, plain, (![A_1194]: (k7_relat_1('#skF_5', A_1194)=k1_xboole_0 | k3_xboole_0(A_1194, '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_9991])).
% 16.97/8.37  tff(c_28, plain, (![B_25, A_24]: (r1_tarski(k1_relat_1(k7_relat_1(B_25, A_24)), A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_77])).
% 16.97/8.37  tff(c_11965, plain, (![A_1194]: (r1_tarski(k1_relat_1(k1_xboole_0), A_1194) | ~v1_relat_1('#skF_5') | k3_xboole_0(A_1194, '#skF_3')!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_11944, c_28])).
% 16.97/8.37  tff(c_11988, plain, (![A_1194]: (r1_tarski(k1_xboole_0, A_1194) | k3_xboole_0(A_1194, '#skF_3')!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7122, c_26, c_11965])).
% 16.97/8.37  tff(c_11635, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_10295])).
% 16.97/8.37  tff(c_20, plain, (![A_16, C_20, B_19]: (k9_relat_1(k7_relat_1(A_16, C_20), B_19)=k9_relat_1(A_16, B_19) | ~r1_tarski(B_19, C_20) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 16.97/8.37  tff(c_11691, plain, (![B_19]: (k9_relat_1(k1_xboole_0, B_19)=k9_relat_1('#skF_5', B_19) | ~r1_tarski(B_19, '#skF_4') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_11635, c_20])).
% 16.97/8.37  tff(c_12561, plain, (![B_1221]: (k9_relat_1(k1_xboole_0, B_1221)=k9_relat_1('#skF_5', B_1221) | ~r1_tarski(B_1221, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7122, c_11691])).
% 16.97/8.37  tff(c_12573, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k9_relat_1('#skF_5', k1_xboole_0) | k3_xboole_0('#skF_4', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_11988, c_12561])).
% 16.97/8.37  tff(c_12601, plain, (k9_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_11720, c_8042, c_12573])).
% 16.97/8.37  tff(c_12603, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12021, c_12601])).
% 16.97/8.37  tff(c_12604, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_10016])).
% 16.97/8.37  tff(c_10300, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0 | k9_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_8122, c_10254])).
% 16.97/8.37  tff(c_10538, plain, (k9_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_10300])).
% 16.97/8.37  tff(c_10545, plain, (k7_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_8327, c_10538])).
% 16.97/8.37  tff(c_9450, plain, (![A_14]: (r1_xboole_0('#skF_4', A_14) | k9_relat_1('#skF_6', A_14)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_9433, c_18])).
% 16.97/8.37  tff(c_10117, plain, (![A_1038]: (r1_xboole_0('#skF_4', A_1038) | k9_relat_1('#skF_6', A_1038)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7123, c_9450])).
% 16.97/8.37  tff(c_10137, plain, (k7_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0 | k9_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_10117, c_8233])).
% 16.97/8.37  tff(c_11247, plain, (k9_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_10545, c_10137])).
% 16.97/8.37  tff(c_34, plain, (![A_28, B_29]: (r1_subset_1(A_28, B_29) | ~r1_xboole_0(A_28, B_29) | v1_xboole_0(B_29) | v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_93])).
% 16.97/8.37  tff(c_10207, plain, (![A_1042]: (r1_subset_1('#skF_4', A_1042) | v1_xboole_0(A_1042) | v1_xboole_0('#skF_4') | k7_relat_1('#skF_6', A_1042)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10186, c_34])).
% 16.97/8.37  tff(c_10555, plain, (![A_1065]: (r1_subset_1('#skF_4', A_1065) | v1_xboole_0(A_1065) | k7_relat_1('#skF_6', A_1065)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_84, c_10207])).
% 16.97/8.37  tff(c_10003, plain, (![A_28]: (k7_relat_1('#skF_5', A_28)=k1_xboole_0 | ~r1_subset_1(A_28, '#skF_3') | v1_xboole_0('#skF_3') | v1_xboole_0(A_28))), inference(resolution, [status(thm)], [c_36, c_9991])).
% 16.97/8.37  tff(c_10020, plain, (![A_28]: (k7_relat_1('#skF_5', A_28)=k1_xboole_0 | ~r1_subset_1(A_28, '#skF_3') | v1_xboole_0(A_28))), inference(negUnitSimplification, [status(thm)], [c_88, c_10003])).
% 16.97/8.37  tff(c_10559, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | k7_relat_1('#skF_6', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_10555, c_10020])).
% 16.97/8.37  tff(c_10562, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | k7_relat_1('#skF_6', '#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_88, c_84, c_10559])).
% 16.97/8.37  tff(c_10640, plain, (k7_relat_1('#skF_6', '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_10562])).
% 16.97/8.37  tff(c_10749, plain, (![A_1090]: (k7_relat_1('#skF_6', A_1090)=k1_xboole_0 | ~r1_subset_1(A_1090, '#skF_4') | v1_xboole_0(A_1090))), inference(negUnitSimplification, [status(thm)], [c_84, c_10282])).
% 16.97/8.37  tff(c_10756, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_80, c_10749])).
% 16.97/8.37  tff(c_10762, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_10640, c_10756])).
% 16.97/8.37  tff(c_10763, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_10562])).
% 16.97/8.37  tff(c_10220, plain, (![A_1043]: (r1_xboole_0('#skF_3', A_1043) | k7_relat_1('#skF_5', A_1043)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7122, c_9961])).
% 16.97/8.37  tff(c_10253, plain, (![A_1043]: (k3_xboole_0('#skF_3', A_1043)=k1_xboole_0 | k7_relat_1('#skF_5', A_1043)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10220, c_2])).
% 16.97/8.37  tff(c_10780, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_10763, c_10253])).
% 16.97/8.37  tff(c_11258, plain, (![A_1136]: (k7_relat_1('#skF_6', A_1136)=k1_xboole_0 | k3_xboole_0(A_1136, '#skF_4')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_10254])).
% 16.97/8.37  tff(c_11282, plain, (![A_1136]: (r1_tarski(k1_relat_1(k1_xboole_0), A_1136) | ~v1_relat_1('#skF_6') | k3_xboole_0(A_1136, '#skF_4')!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_11258, c_28])).
% 16.97/8.37  tff(c_11306, plain, (![A_1136]: (r1_tarski(k1_xboole_0, A_1136) | k3_xboole_0(A_1136, '#skF_4')!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7123, c_26, c_11282])).
% 16.97/8.37  tff(c_10764, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_10562])).
% 16.97/8.37  tff(c_10794, plain, (![B_19]: (k9_relat_1(k1_xboole_0, B_19)=k9_relat_1('#skF_6', B_19) | ~r1_tarski(B_19, '#skF_3') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_10764, c_20])).
% 16.97/8.37  tff(c_11405, plain, (![B_1145]: (k9_relat_1(k1_xboole_0, B_1145)=k9_relat_1('#skF_6', B_1145) | ~r1_tarski(B_1145, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7123, c_10794])).
% 16.97/8.37  tff(c_11409, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k9_relat_1('#skF_6', k1_xboole_0) | k3_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_11306, c_11405])).
% 16.97/8.37  tff(c_11439, plain, (k9_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10780, c_8042, c_11409])).
% 16.97/8.37  tff(c_11441, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11247, c_11439])).
% 16.97/8.37  tff(c_11442, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_10300])).
% 16.97/8.37  tff(c_11700, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_11635, c_10253])).
% 16.97/8.37  tff(c_10085, plain, (![A_1033, B_1034, C_1035]: (k9_subset_1(A_1033, B_1034, C_1035)=k3_xboole_0(B_1034, C_1035) | ~m1_subset_1(C_1035, k1_zfmisc_1(A_1033)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 16.97/8.37  tff(c_10097, plain, (![B_1034]: (k9_subset_1('#skF_1', B_1034, '#skF_4')=k3_xboole_0(B_1034, '#skF_4'))), inference(resolution, [status(thm)], [c_82, c_10085])).
% 16.97/8.37  tff(c_11463, plain, (![E_1148, D_1150, C_1146, A_1147, F_1151, B_1149]: (v1_funct_1(k1_tmap_1(A_1147, B_1149, C_1146, D_1150, E_1148, F_1151)) | ~m1_subset_1(F_1151, k1_zfmisc_1(k2_zfmisc_1(D_1150, B_1149))) | ~v1_funct_2(F_1151, D_1150, B_1149) | ~v1_funct_1(F_1151) | ~m1_subset_1(E_1148, k1_zfmisc_1(k2_zfmisc_1(C_1146, B_1149))) | ~v1_funct_2(E_1148, C_1146, B_1149) | ~v1_funct_1(E_1148) | ~m1_subset_1(D_1150, k1_zfmisc_1(A_1147)) | v1_xboole_0(D_1150) | ~m1_subset_1(C_1146, k1_zfmisc_1(A_1147)) | v1_xboole_0(C_1146) | v1_xboole_0(B_1149) | v1_xboole_0(A_1147))), inference(cnfTransformation, [status(thm)], [f_213])).
% 16.97/8.37  tff(c_11467, plain, (![A_1147, C_1146, E_1148]: (v1_funct_1(k1_tmap_1(A_1147, '#skF_2', C_1146, '#skF_4', E_1148, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1148, k1_zfmisc_1(k2_zfmisc_1(C_1146, '#skF_2'))) | ~v1_funct_2(E_1148, C_1146, '#skF_2') | ~v1_funct_1(E_1148) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1147)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1146, k1_zfmisc_1(A_1147)) | v1_xboole_0(C_1146) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1147))), inference(resolution, [status(thm)], [c_68, c_11463])).
% 16.97/8.37  tff(c_11474, plain, (![A_1147, C_1146, E_1148]: (v1_funct_1(k1_tmap_1(A_1147, '#skF_2', C_1146, '#skF_4', E_1148, '#skF_6')) | ~m1_subset_1(E_1148, k1_zfmisc_1(k2_zfmisc_1(C_1146, '#skF_2'))) | ~v1_funct_2(E_1148, C_1146, '#skF_2') | ~v1_funct_1(E_1148) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1147)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1146, k1_zfmisc_1(A_1147)) | v1_xboole_0(C_1146) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1147))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_11467])).
% 16.97/8.37  tff(c_14003, plain, (![A_1284, C_1285, E_1286]: (v1_funct_1(k1_tmap_1(A_1284, '#skF_2', C_1285, '#skF_4', E_1286, '#skF_6')) | ~m1_subset_1(E_1286, k1_zfmisc_1(k2_zfmisc_1(C_1285, '#skF_2'))) | ~v1_funct_2(E_1286, C_1285, '#skF_2') | ~v1_funct_1(E_1286) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1284)) | ~m1_subset_1(C_1285, k1_zfmisc_1(A_1284)) | v1_xboole_0(C_1285) | v1_xboole_0(A_1284))), inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_11474])).
% 16.97/8.37  tff(c_14008, plain, (![A_1284]: (v1_funct_1(k1_tmap_1(A_1284, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1284)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1284)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1284))), inference(resolution, [status(thm)], [c_74, c_14003])).
% 16.97/8.37  tff(c_14016, plain, (![A_1284]: (v1_funct_1(k1_tmap_1(A_1284, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1284)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1284)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1284))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_14008])).
% 16.97/8.37  tff(c_14445, plain, (![A_1300]: (v1_funct_1(k1_tmap_1(A_1300, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1300)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1300)) | v1_xboole_0(A_1300))), inference(negUnitSimplification, [status(thm)], [c_88, c_14016])).
% 16.97/8.37  tff(c_14448, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_86, c_14445])).
% 16.97/8.37  tff(c_14451, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_14448])).
% 16.97/8.37  tff(c_14452, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_92, c_14451])).
% 16.97/8.37  tff(c_10461, plain, (![A_1053, B_1054, C_1055, D_1056]: (k2_partfun1(A_1053, B_1054, C_1055, D_1056)=k7_relat_1(C_1055, D_1056) | ~m1_subset_1(C_1055, k1_zfmisc_1(k2_zfmisc_1(A_1053, B_1054))) | ~v1_funct_1(C_1055))), inference(cnfTransformation, [status(thm)], [f_131])).
% 16.97/8.37  tff(c_10463, plain, (![D_1056]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_1056)=k7_relat_1('#skF_5', D_1056) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_74, c_10461])).
% 16.97/8.37  tff(c_10468, plain, (![D_1056]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_1056)=k7_relat_1('#skF_5', D_1056))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_10463])).
% 16.97/8.37  tff(c_10465, plain, (![D_1056]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_1056)=k7_relat_1('#skF_6', D_1056) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_68, c_10461])).
% 16.97/8.37  tff(c_10471, plain, (![D_1056]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_1056)=k7_relat_1('#skF_6', D_1056))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_10465])).
% 16.97/8.37  tff(c_60, plain, (![E_177, F_178, B_174, D_176, C_175, A_173]: (m1_subset_1(k1_tmap_1(A_173, B_174, C_175, D_176, E_177, F_178), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_173, C_175, D_176), B_174))) | ~m1_subset_1(F_178, k1_zfmisc_1(k2_zfmisc_1(D_176, B_174))) | ~v1_funct_2(F_178, D_176, B_174) | ~v1_funct_1(F_178) | ~m1_subset_1(E_177, k1_zfmisc_1(k2_zfmisc_1(C_175, B_174))) | ~v1_funct_2(E_177, C_175, B_174) | ~v1_funct_1(E_177) | ~m1_subset_1(D_176, k1_zfmisc_1(A_173)) | v1_xboole_0(D_176) | ~m1_subset_1(C_175, k1_zfmisc_1(A_173)) | v1_xboole_0(C_175) | v1_xboole_0(B_174) | v1_xboole_0(A_173))), inference(cnfTransformation, [status(thm)], [f_213])).
% 16.97/8.37  tff(c_12722, plain, (![E_1224, C_1227, F_1223, A_1228, B_1225, D_1226]: (k2_partfun1(k4_subset_1(A_1228, C_1227, D_1226), B_1225, k1_tmap_1(A_1228, B_1225, C_1227, D_1226, E_1224, F_1223), D_1226)=F_1223 | ~m1_subset_1(k1_tmap_1(A_1228, B_1225, C_1227, D_1226, E_1224, F_1223), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1228, C_1227, D_1226), B_1225))) | ~v1_funct_2(k1_tmap_1(A_1228, B_1225, C_1227, D_1226, E_1224, F_1223), k4_subset_1(A_1228, C_1227, D_1226), B_1225) | ~v1_funct_1(k1_tmap_1(A_1228, B_1225, C_1227, D_1226, E_1224, F_1223)) | k2_partfun1(D_1226, B_1225, F_1223, k9_subset_1(A_1228, C_1227, D_1226))!=k2_partfun1(C_1227, B_1225, E_1224, k9_subset_1(A_1228, C_1227, D_1226)) | ~m1_subset_1(F_1223, k1_zfmisc_1(k2_zfmisc_1(D_1226, B_1225))) | ~v1_funct_2(F_1223, D_1226, B_1225) | ~v1_funct_1(F_1223) | ~m1_subset_1(E_1224, k1_zfmisc_1(k2_zfmisc_1(C_1227, B_1225))) | ~v1_funct_2(E_1224, C_1227, B_1225) | ~v1_funct_1(E_1224) | ~m1_subset_1(D_1226, k1_zfmisc_1(A_1228)) | v1_xboole_0(D_1226) | ~m1_subset_1(C_1227, k1_zfmisc_1(A_1228)) | v1_xboole_0(C_1227) | v1_xboole_0(B_1225) | v1_xboole_0(A_1228))), inference(cnfTransformation, [status(thm)], [f_179])).
% 16.97/8.37  tff(c_20075, plain, (![F_1499, B_1497, C_1494, A_1495, E_1496, D_1498]: (k2_partfun1(k4_subset_1(A_1495, C_1494, D_1498), B_1497, k1_tmap_1(A_1495, B_1497, C_1494, D_1498, E_1496, F_1499), D_1498)=F_1499 | ~v1_funct_2(k1_tmap_1(A_1495, B_1497, C_1494, D_1498, E_1496, F_1499), k4_subset_1(A_1495, C_1494, D_1498), B_1497) | ~v1_funct_1(k1_tmap_1(A_1495, B_1497, C_1494, D_1498, E_1496, F_1499)) | k2_partfun1(D_1498, B_1497, F_1499, k9_subset_1(A_1495, C_1494, D_1498))!=k2_partfun1(C_1494, B_1497, E_1496, k9_subset_1(A_1495, C_1494, D_1498)) | ~m1_subset_1(F_1499, k1_zfmisc_1(k2_zfmisc_1(D_1498, B_1497))) | ~v1_funct_2(F_1499, D_1498, B_1497) | ~v1_funct_1(F_1499) | ~m1_subset_1(E_1496, k1_zfmisc_1(k2_zfmisc_1(C_1494, B_1497))) | ~v1_funct_2(E_1496, C_1494, B_1497) | ~v1_funct_1(E_1496) | ~m1_subset_1(D_1498, k1_zfmisc_1(A_1495)) | v1_xboole_0(D_1498) | ~m1_subset_1(C_1494, k1_zfmisc_1(A_1495)) | v1_xboole_0(C_1494) | v1_xboole_0(B_1497) | v1_xboole_0(A_1495))), inference(resolution, [status(thm)], [c_60, c_12722])).
% 16.97/8.37  tff(c_27503, plain, (![A_1646, F_1650, E_1647, D_1649, C_1645, B_1648]: (k2_partfun1(k4_subset_1(A_1646, C_1645, D_1649), B_1648, k1_tmap_1(A_1646, B_1648, C_1645, D_1649, E_1647, F_1650), D_1649)=F_1650 | ~v1_funct_1(k1_tmap_1(A_1646, B_1648, C_1645, D_1649, E_1647, F_1650)) | k2_partfun1(D_1649, B_1648, F_1650, k9_subset_1(A_1646, C_1645, D_1649))!=k2_partfun1(C_1645, B_1648, E_1647, k9_subset_1(A_1646, C_1645, D_1649)) | ~m1_subset_1(F_1650, k1_zfmisc_1(k2_zfmisc_1(D_1649, B_1648))) | ~v1_funct_2(F_1650, D_1649, B_1648) | ~v1_funct_1(F_1650) | ~m1_subset_1(E_1647, k1_zfmisc_1(k2_zfmisc_1(C_1645, B_1648))) | ~v1_funct_2(E_1647, C_1645, B_1648) | ~v1_funct_1(E_1647) | ~m1_subset_1(D_1649, k1_zfmisc_1(A_1646)) | v1_xboole_0(D_1649) | ~m1_subset_1(C_1645, k1_zfmisc_1(A_1646)) | v1_xboole_0(C_1645) | v1_xboole_0(B_1648) | v1_xboole_0(A_1646))), inference(resolution, [status(thm)], [c_62, c_20075])).
% 16.97/8.37  tff(c_27509, plain, (![A_1646, C_1645, E_1647]: (k2_partfun1(k4_subset_1(A_1646, C_1645, '#skF_4'), '#skF_2', k1_tmap_1(A_1646, '#skF_2', C_1645, '#skF_4', E_1647, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1646, '#skF_2', C_1645, '#skF_4', E_1647, '#skF_6')) | k2_partfun1(C_1645, '#skF_2', E_1647, k9_subset_1(A_1646, C_1645, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_1646, C_1645, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1647, k1_zfmisc_1(k2_zfmisc_1(C_1645, '#skF_2'))) | ~v1_funct_2(E_1647, C_1645, '#skF_2') | ~v1_funct_1(E_1647) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1646)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1645, k1_zfmisc_1(A_1646)) | v1_xboole_0(C_1645) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1646))), inference(resolution, [status(thm)], [c_68, c_27503])).
% 16.97/8.37  tff(c_27517, plain, (![A_1646, C_1645, E_1647]: (k2_partfun1(k4_subset_1(A_1646, C_1645, '#skF_4'), '#skF_2', k1_tmap_1(A_1646, '#skF_2', C_1645, '#skF_4', E_1647, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1646, '#skF_2', C_1645, '#skF_4', E_1647, '#skF_6')) | k2_partfun1(C_1645, '#skF_2', E_1647, k9_subset_1(A_1646, C_1645, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1646, C_1645, '#skF_4')) | ~m1_subset_1(E_1647, k1_zfmisc_1(k2_zfmisc_1(C_1645, '#skF_2'))) | ~v1_funct_2(E_1647, C_1645, '#skF_2') | ~v1_funct_1(E_1647) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1646)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1645, k1_zfmisc_1(A_1646)) | v1_xboole_0(C_1645) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1646))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_10471, c_27509])).
% 16.97/8.37  tff(c_29598, plain, (![A_1684, C_1685, E_1686]: (k2_partfun1(k4_subset_1(A_1684, C_1685, '#skF_4'), '#skF_2', k1_tmap_1(A_1684, '#skF_2', C_1685, '#skF_4', E_1686, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1684, '#skF_2', C_1685, '#skF_4', E_1686, '#skF_6')) | k2_partfun1(C_1685, '#skF_2', E_1686, k9_subset_1(A_1684, C_1685, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1684, C_1685, '#skF_4')) | ~m1_subset_1(E_1686, k1_zfmisc_1(k2_zfmisc_1(C_1685, '#skF_2'))) | ~v1_funct_2(E_1686, C_1685, '#skF_2') | ~v1_funct_1(E_1686) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1684)) | ~m1_subset_1(C_1685, k1_zfmisc_1(A_1684)) | v1_xboole_0(C_1685) | v1_xboole_0(A_1684))), inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_27517])).
% 16.97/8.37  tff(c_29603, plain, (![A_1684]: (k2_partfun1(k4_subset_1(A_1684, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1684, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1684, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_1684, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1684, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1684)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1684)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1684))), inference(resolution, [status(thm)], [c_74, c_29598])).
% 16.97/8.37  tff(c_29611, plain, (![A_1684]: (k2_partfun1(k4_subset_1(A_1684, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1684, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1684, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1684, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1684, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1684)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1684)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1684))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_10468, c_29603])).
% 16.97/8.37  tff(c_31056, plain, (![A_1707]: (k2_partfun1(k4_subset_1(A_1707, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1707, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1707, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1707, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1707, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1707)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1707)) | v1_xboole_0(A_1707))), inference(negUnitSimplification, [status(thm)], [c_88, c_29611])).
% 16.97/8.37  tff(c_140, plain, (![C_248, A_249, B_250]: (v1_relat_1(C_248) | ~m1_subset_1(C_248, k1_zfmisc_1(k2_zfmisc_1(A_249, B_250))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 16.97/8.37  tff(c_148, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_68, c_140])).
% 16.97/8.37  tff(c_862, plain, (![C_335, A_336, B_337]: (v4_relat_1(C_335, A_336) | ~m1_subset_1(C_335, k1_zfmisc_1(k2_zfmisc_1(A_336, B_337))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 16.97/8.37  tff(c_870, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_68, c_862])).
% 16.97/8.37  tff(c_1283, plain, (![B_369, A_370]: (k1_relat_1(B_369)=A_370 | ~v1_partfun1(B_369, A_370) | ~v4_relat_1(B_369, A_370) | ~v1_relat_1(B_369))), inference(cnfTransformation, [status(thm)], [f_125])).
% 16.97/8.37  tff(c_1286, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_870, c_1283])).
% 16.97/8.37  tff(c_1292, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_1286])).
% 16.97/8.37  tff(c_1296, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_1292])).
% 16.97/8.37  tff(c_2055, plain, (![C_434, A_435, B_436]: (v1_partfun1(C_434, A_435) | ~v1_funct_2(C_434, A_435, B_436) | ~v1_funct_1(C_434) | ~m1_subset_1(C_434, k1_zfmisc_1(k2_zfmisc_1(A_435, B_436))) | v1_xboole_0(B_436))), inference(cnfTransformation, [status(thm)], [f_117])).
% 16.97/8.37  tff(c_2061, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_2055])).
% 16.97/8.37  tff(c_2068, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_2061])).
% 16.97/8.37  tff(c_2070, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_1296, c_2068])).
% 16.97/8.37  tff(c_2071, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_1292])).
% 16.97/8.37  tff(c_2088, plain, (![A_14]: (r1_xboole_0('#skF_4', A_14) | k9_relat_1('#skF_6', A_14)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2071, c_18])).
% 16.97/8.37  tff(c_2746, plain, (![A_478]: (r1_xboole_0('#skF_4', A_478) | k9_relat_1('#skF_6', A_478)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_148, c_2088])).
% 16.97/8.37  tff(c_149, plain, (![A_251]: (k9_relat_1(A_251, k1_relat_1(A_251))=k2_relat_1(A_251) | ~v1_relat_1(A_251))), inference(cnfTransformation, [status(thm)], [f_50])).
% 16.97/8.37  tff(c_158, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_149])).
% 16.97/8.37  tff(c_161, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_158])).
% 16.97/8.37  tff(c_162, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_161])).
% 16.97/8.37  tff(c_147, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_140])).
% 16.97/8.37  tff(c_163, plain, (![C_252, A_253, B_254]: (v4_relat_1(C_252, A_253) | ~m1_subset_1(C_252, k1_zfmisc_1(k2_zfmisc_1(A_253, B_254))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 16.97/8.37  tff(c_170, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_163])).
% 16.97/8.37  tff(c_346, plain, (![B_277, A_278]: (k1_relat_1(B_277)=A_278 | ~v1_partfun1(B_277, A_278) | ~v4_relat_1(B_277, A_278) | ~v1_relat_1(B_277))), inference(cnfTransformation, [status(thm)], [f_125])).
% 16.97/8.37  tff(c_352, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_170, c_346])).
% 16.97/8.37  tff(c_358, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_147, c_352])).
% 16.97/8.37  tff(c_360, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_358])).
% 16.97/8.37  tff(c_511, plain, (![C_305, A_306, B_307]: (v1_partfun1(C_305, A_306) | ~v1_funct_2(C_305, A_306, B_307) | ~v1_funct_1(C_305) | ~m1_subset_1(C_305, k1_zfmisc_1(k2_zfmisc_1(A_306, B_307))) | v1_xboole_0(B_307))), inference(cnfTransformation, [status(thm)], [f_117])).
% 16.97/8.37  tff(c_514, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_74, c_511])).
% 16.97/8.37  tff(c_520, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_514])).
% 16.97/8.37  tff(c_522, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_360, c_520])).
% 16.97/8.37  tff(c_523, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_358])).
% 16.97/8.37  tff(c_529, plain, (![A_26]: (k7_relat_1('#skF_5', A_26)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_26) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_523, c_30])).
% 16.97/8.37  tff(c_706, plain, (![A_318]: (k7_relat_1('#skF_5', A_318)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_318))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_529])).
% 16.97/8.37  tff(c_746, plain, (![B_322]: (k7_relat_1('#skF_5', B_322)=k1_xboole_0 | k3_xboole_0('#skF_3', B_322)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_706])).
% 16.97/8.37  tff(c_761, plain, (![B_322]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_5') | k3_xboole_0('#skF_3', B_322)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_746, c_12])).
% 16.97/8.37  tff(c_772, plain, (![B_322]: (v1_relat_1(k1_xboole_0) | k3_xboole_0('#skF_3', B_322)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_147, c_761])).
% 16.97/8.37  tff(c_773, plain, (![B_322]: (k3_xboole_0('#skF_3', B_322)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_162, c_772])).
% 16.97/8.37  tff(c_532, plain, (![A_14]: (r1_xboole_0('#skF_3', A_14) | k9_relat_1('#skF_5', A_14)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_523, c_18])).
% 16.97/8.37  tff(c_640, plain, (![A_315]: (r1_xboole_0('#skF_3', A_315) | k9_relat_1('#skF_5', A_315)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_147, c_532])).
% 16.97/8.37  tff(c_662, plain, (![A_315]: (k3_xboole_0('#skF_3', A_315)=k1_xboole_0 | k9_relat_1('#skF_5', A_315)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_640, c_2])).
% 16.97/8.37  tff(c_785, plain, (![A_315]: (k9_relat_1('#skF_5', A_315)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_773, c_662])).
% 16.97/8.37  tff(c_16, plain, (![B_15, A_14]: (k9_relat_1(B_15, A_14)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_15), A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 16.97/8.37  tff(c_535, plain, (![A_14]: (k9_relat_1('#skF_5', A_14)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_14) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_523, c_16])).
% 16.97/8.37  tff(c_555, plain, (![A_14]: (k9_relat_1('#skF_5', A_14)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_535])).
% 16.97/8.37  tff(c_798, plain, (![A_326]: (~r1_xboole_0('#skF_3', A_326))), inference(negUnitSimplification, [status(thm)], [c_785, c_555])).
% 16.97/8.37  tff(c_802, plain, (![B_29]: (~r1_subset_1('#skF_3', B_29) | v1_xboole_0(B_29) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_798])).
% 16.97/8.37  tff(c_848, plain, (![B_334]: (~r1_subset_1('#skF_3', B_334) | v1_xboole_0(B_334))), inference(negUnitSimplification, [status(thm)], [c_88, c_802])).
% 16.97/8.37  tff(c_851, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_80, c_848])).
% 16.97/8.37  tff(c_855, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_851])).
% 16.97/8.37  tff(c_857, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_161])).
% 16.97/8.37  tff(c_931, plain, (![A_348, B_349]: (k7_relat_1(A_348, B_349)=k1_xboole_0 | ~r1_xboole_0(B_349, k1_relat_1(A_348)) | ~v1_relat_1(A_348))), inference(cnfTransformation, [status(thm)], [f_70])).
% 16.97/8.37  tff(c_946, plain, (![B_349]: (k7_relat_1(k1_xboole_0, B_349)=k1_xboole_0 | ~r1_xboole_0(B_349, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_931])).
% 16.97/8.37  tff(c_951, plain, (![B_349]: (k7_relat_1(k1_xboole_0, B_349)=k1_xboole_0 | ~r1_xboole_0(B_349, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_857, c_946])).
% 16.97/8.37  tff(c_2772, plain, (k7_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0 | k9_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_2746, c_951])).
% 16.97/8.37  tff(c_2981, plain, (k9_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2772])).
% 16.97/8.37  tff(c_869, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_862])).
% 16.97/8.37  tff(c_1289, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_869, c_1283])).
% 16.97/8.37  tff(c_1295, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_147, c_1289])).
% 16.97/8.37  tff(c_2113, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_1295])).
% 16.97/8.37  tff(c_2512, plain, (![C_464, A_465, B_466]: (v1_partfun1(C_464, A_465) | ~v1_funct_2(C_464, A_465, B_466) | ~v1_funct_1(C_464) | ~m1_subset_1(C_464, k1_zfmisc_1(k2_zfmisc_1(A_465, B_466))) | v1_xboole_0(B_466))), inference(cnfTransformation, [status(thm)], [f_117])).
% 16.97/8.37  tff(c_2515, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_74, c_2512])).
% 16.97/8.37  tff(c_2521, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_2515])).
% 16.97/8.37  tff(c_2523, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_2113, c_2521])).
% 16.97/8.37  tff(c_2524, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_1295])).
% 16.97/8.37  tff(c_2535, plain, (![A_26]: (r1_xboole_0('#skF_3', A_26) | k7_relat_1('#skF_5', A_26)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2524, c_32])).
% 16.97/8.37  tff(c_2698, plain, (![A_476]: (r1_xboole_0('#skF_3', A_476) | k7_relat_1('#skF_5', A_476)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_147, c_2535])).
% 16.97/8.37  tff(c_2532, plain, (![A_14]: (k9_relat_1('#skF_5', A_14)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_14) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2524, c_16])).
% 16.97/8.37  tff(c_2553, plain, (![A_14]: (k9_relat_1('#skF_5', A_14)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_2532])).
% 16.97/8.37  tff(c_3013, plain, (![A_496]: (k9_relat_1('#skF_5', A_496)=k1_xboole_0 | k7_relat_1('#skF_5', A_496)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2698, c_2553])).
% 16.97/8.37  tff(c_2541, plain, (![A_14]: (r1_xboole_0('#skF_3', A_14) | k9_relat_1('#skF_5', A_14)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2524, c_18])).
% 16.97/8.37  tff(c_2851, plain, (![A_482]: (r1_xboole_0('#skF_3', A_482) | k9_relat_1('#skF_5', A_482)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_147, c_2541])).
% 16.97/8.37  tff(c_2085, plain, (![B_23]: (k7_relat_1('#skF_6', B_23)=k1_xboole_0 | ~r1_xboole_0(B_23, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2071, c_22])).
% 16.97/8.37  tff(c_2104, plain, (![B_23]: (k7_relat_1('#skF_6', B_23)=k1_xboole_0 | ~r1_xboole_0(B_23, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_2085])).
% 16.97/8.37  tff(c_2882, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | k9_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_2851, c_2104])).
% 16.97/8.37  tff(c_3012, plain, (k9_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2882])).
% 16.97/8.37  tff(c_3038, plain, (k7_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3013, c_3012])).
% 16.97/8.37  tff(c_2082, plain, (![A_26]: (r1_xboole_0('#skF_4', A_26) | k7_relat_1('#skF_6', A_26)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2071, c_32])).
% 16.97/8.37  tff(c_2812, plain, (![A_481]: (r1_xboole_0('#skF_4', A_481) | k7_relat_1('#skF_6', A_481)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_148, c_2082])).
% 16.97/8.37  tff(c_2837, plain, (![A_481]: (r1_subset_1('#skF_4', A_481) | v1_xboole_0(A_481) | v1_xboole_0('#skF_4') | k7_relat_1('#skF_6', A_481)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2812, c_34])).
% 16.97/8.37  tff(c_3063, plain, (![A_500]: (r1_subset_1('#skF_4', A_500) | v1_xboole_0(A_500) | k7_relat_1('#skF_6', A_500)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_84, c_2837])).
% 16.97/8.37  tff(c_2538, plain, (![B_23]: (k7_relat_1('#skF_5', B_23)=k1_xboole_0 | ~r1_xboole_0(B_23, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2524, c_22])).
% 16.97/8.37  tff(c_2574, plain, (![B_467]: (k7_relat_1('#skF_5', B_467)=k1_xboole_0 | ~r1_xboole_0(B_467, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_2538])).
% 16.97/8.37  tff(c_2578, plain, (![A_28]: (k7_relat_1('#skF_5', A_28)=k1_xboole_0 | ~r1_subset_1(A_28, '#skF_3') | v1_xboole_0('#skF_3') | v1_xboole_0(A_28))), inference(resolution, [status(thm)], [c_36, c_2574])).
% 16.97/8.37  tff(c_2601, plain, (![A_28]: (k7_relat_1('#skF_5', A_28)=k1_xboole_0 | ~r1_subset_1(A_28, '#skF_3') | v1_xboole_0(A_28))), inference(negUnitSimplification, [status(thm)], [c_88, c_2578])).
% 16.97/8.37  tff(c_3067, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | k7_relat_1('#skF_6', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_3063, c_2601])).
% 16.97/8.37  tff(c_3070, plain, (k7_relat_1('#skF_6', '#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_88, c_84, c_3038, c_3067])).
% 16.97/8.37  tff(c_2607, plain, (![B_468]: (k7_relat_1('#skF_6', B_468)=k1_xboole_0 | ~r1_xboole_0(B_468, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_2085])).
% 16.97/8.37  tff(c_2611, plain, (![A_28]: (k7_relat_1('#skF_6', A_28)=k1_xboole_0 | ~r1_subset_1(A_28, '#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(A_28))), inference(resolution, [status(thm)], [c_36, c_2607])).
% 16.97/8.37  tff(c_3294, plain, (![A_527]: (k7_relat_1('#skF_6', A_527)=k1_xboole_0 | ~r1_subset_1(A_527, '#skF_4') | v1_xboole_0(A_527))), inference(negUnitSimplification, [status(thm)], [c_84, c_2611])).
% 16.97/8.37  tff(c_3305, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_80, c_3294])).
% 16.97/8.37  tff(c_3313, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_3070, c_3305])).
% 16.97/8.37  tff(c_3315, plain, (k9_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2882])).
% 16.97/8.37  tff(c_3371, plain, (![A_532]: (k3_xboole_0('#skF_3', A_532)=k1_xboole_0 | k9_relat_1('#skF_5', A_532)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2851, c_2])).
% 16.97/8.37  tff(c_3382, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3315, c_3371])).
% 16.97/8.37  tff(c_856, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_161])).
% 16.97/8.37  tff(c_3550, plain, (![A_553]: (k7_relat_1('#skF_6', A_553)=k1_xboole_0 | k3_xboole_0(A_553, '#skF_4')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_2607])).
% 16.97/8.37  tff(c_3574, plain, (![A_553]: (r1_tarski(k1_relat_1(k1_xboole_0), A_553) | ~v1_relat_1('#skF_6') | k3_xboole_0(A_553, '#skF_4')!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3550, c_28])).
% 16.97/8.37  tff(c_3598, plain, (![A_553]: (r1_tarski(k1_xboole_0, A_553) | k3_xboole_0(A_553, '#skF_4')!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_148, c_26, c_3574])).
% 16.97/8.37  tff(c_3314, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2882])).
% 16.97/8.37  tff(c_3319, plain, (![B_19]: (k9_relat_1(k1_xboole_0, B_19)=k9_relat_1('#skF_6', B_19) | ~r1_tarski(B_19, '#skF_3') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3314, c_20])).
% 16.97/8.37  tff(c_4091, plain, (![B_595]: (k9_relat_1(k1_xboole_0, B_595)=k9_relat_1('#skF_6', B_595) | ~r1_tarski(B_595, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_3319])).
% 16.97/8.37  tff(c_4103, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k9_relat_1('#skF_6', k1_xboole_0) | k3_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_3598, c_4091])).
% 16.97/8.37  tff(c_4131, plain, (k9_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3382, c_856, c_4103])).
% 16.97/8.37  tff(c_4133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2981, c_4131])).
% 16.97/8.37  tff(c_4135, plain, (k9_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_2772])).
% 16.97/8.37  tff(c_2106, plain, (![A_14]: (r1_xboole_0('#skF_4', A_14) | k9_relat_1('#skF_6', A_14)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_148, c_2088])).
% 16.97/8.37  tff(c_2076, plain, (![A_26]: (k7_relat_1('#skF_6', A_26)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_26) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2071, c_30])).
% 16.97/8.37  tff(c_2778, plain, (![A_479]: (k7_relat_1('#skF_6', A_479)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_479))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_2076])).
% 16.97/8.37  tff(c_4617, plain, (![A_639]: (k7_relat_1('#skF_6', A_639)=k1_xboole_0 | k9_relat_1('#skF_6', A_639)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2106, c_2778])).
% 16.97/8.37  tff(c_4632, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4135, c_4617])).
% 16.97/8.37  tff(c_2729, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | k7_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_2698, c_2104])).
% 16.97/8.37  tff(c_4278, plain, (k7_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2729])).
% 16.97/8.37  tff(c_2529, plain, (![A_26]: (k7_relat_1('#skF_5', A_26)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_26) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2524, c_30])).
% 16.97/8.37  tff(c_2653, plain, (![A_470]: (k7_relat_1('#skF_5', A_470)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_470))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_2529])).
% 16.97/8.37  tff(c_2657, plain, (![B_29]: (k7_relat_1('#skF_5', B_29)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_29) | v1_xboole_0(B_29) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_2653])).
% 16.97/8.37  tff(c_4487, plain, (![B_628]: (k7_relat_1('#skF_5', B_628)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_628) | v1_xboole_0(B_628))), inference(negUnitSimplification, [status(thm)], [c_88, c_2657])).
% 16.97/8.37  tff(c_4490, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_80, c_4487])).
% 16.97/8.37  tff(c_4494, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_4278, c_4490])).
% 16.97/8.37  tff(c_4496, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2729])).
% 16.97/8.37  tff(c_5785, plain, (![A_729]: (k3_xboole_0('#skF_3', A_729)=k1_xboole_0 | k7_relat_1('#skF_5', A_729)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2698, c_2])).
% 16.97/8.37  tff(c_5802, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4496, c_5785])).
% 16.97/8.37  tff(c_2885, plain, (k7_relat_1(k1_xboole_0, '#skF_3')=k1_xboole_0 | k9_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_2851, c_951])).
% 16.97/8.37  tff(c_4768, plain, (k9_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2885])).
% 16.97/8.37  tff(c_5120, plain, (![A_684]: (k3_xboole_0('#skF_3', A_684)=k1_xboole_0 | k7_relat_1('#skF_5', A_684)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2698, c_2])).
% 16.97/8.37  tff(c_5132, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4496, c_5120])).
% 16.97/8.37  tff(c_5069, plain, (![B_677]: (k7_relat_1('#skF_5', B_677)=k1_xboole_0 | k3_xboole_0('#skF_3', B_677)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_2653])).
% 16.97/8.37  tff(c_5090, plain, (![B_677]: (r1_tarski(k1_relat_1(k1_xboole_0), B_677) | ~v1_relat_1('#skF_5') | k3_xboole_0('#skF_3', B_677)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5069, c_28])).
% 16.97/8.37  tff(c_5111, plain, (![B_677]: (r1_tarski(k1_xboole_0, B_677) | k3_xboole_0('#skF_3', B_677)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_147, c_26, c_5090])).
% 16.97/8.37  tff(c_4519, plain, (![B_19]: (k9_relat_1(k1_xboole_0, B_19)=k9_relat_1('#skF_5', B_19) | ~r1_tarski(B_19, '#skF_4') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4496, c_20])).
% 16.97/8.37  tff(c_5314, plain, (![B_694]: (k9_relat_1(k1_xboole_0, B_694)=k9_relat_1('#skF_5', B_694) | ~r1_tarski(B_694, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_4519])).
% 16.97/8.37  tff(c_5318, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k9_relat_1('#skF_5', k1_xboole_0) | k3_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_5111, c_5314])).
% 16.97/8.37  tff(c_5348, plain, (k9_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5132, c_856, c_5318])).
% 16.97/8.37  tff(c_5350, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4768, c_5348])).
% 16.97/8.37  tff(c_5352, plain, (k9_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_2885])).
% 16.97/8.37  tff(c_2551, plain, (![A_26]: (k7_relat_1('#skF_5', A_26)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_26))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_2529])).
% 16.97/8.37  tff(c_5492, plain, (![A_704]: (k7_relat_1('#skF_5', A_704)=k1_xboole_0 | k9_relat_1('#skF_5', A_704)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2851, c_2551])).
% 16.97/8.37  tff(c_5506, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5352, c_5492])).
% 16.97/8.37  tff(c_4180, plain, (![A_596, B_597, C_598, D_599]: (k2_partfun1(A_596, B_597, C_598, D_599)=k7_relat_1(C_598, D_599) | ~m1_subset_1(C_598, k1_zfmisc_1(k2_zfmisc_1(A_596, B_597))) | ~v1_funct_1(C_598))), inference(cnfTransformation, [status(thm)], [f_131])).
% 16.97/8.37  tff(c_4182, plain, (![D_599]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_599)=k7_relat_1('#skF_5', D_599) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_74, c_4180])).
% 16.97/8.37  tff(c_4187, plain, (![D_599]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_599)=k7_relat_1('#skF_5', D_599))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_4182])).
% 16.97/8.37  tff(c_4184, plain, (![D_599]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_599)=k7_relat_1('#skF_6', D_599) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_68, c_4180])).
% 16.97/8.37  tff(c_4190, plain, (![D_599]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_599)=k7_relat_1('#skF_6', D_599))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_4184])).
% 16.97/8.37  tff(c_2666, plain, (![A_471, B_472, C_473]: (k9_subset_1(A_471, B_472, C_473)=k3_xboole_0(B_472, C_473) | ~m1_subset_1(C_473, k1_zfmisc_1(A_471)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 16.97/8.37  tff(c_2678, plain, (![B_472]: (k9_subset_1('#skF_1', B_472, '#skF_4')=k3_xboole_0(B_472, '#skF_4'))), inference(resolution, [status(thm)], [c_82, c_2666])).
% 16.97/8.37  tff(c_66, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_255])).
% 16.97/8.37  tff(c_117, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_66])).
% 16.97/8.37  tff(c_2688, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2678, c_2678, c_117])).
% 16.97/8.37  tff(c_7091, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4632, c_5802, c_5506, c_5802, c_4187, c_4190, c_2688])).
% 16.97/8.37  tff(c_7092, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_66])).
% 16.97/8.37  tff(c_8080, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_7092])).
% 16.97/8.37  tff(c_31067, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_31056, c_8080])).
% 16.97/8.37  tff(c_31081, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_12604, c_11442, c_11700, c_10097, c_11700, c_10097, c_14452, c_31067])).
% 16.97/8.37  tff(c_31083, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_31081])).
% 16.97/8.37  tff(c_31084, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_7092])).
% 16.97/8.37  tff(c_31575, plain, (![B_1743, A_1744]: (k1_relat_1(B_1743)=A_1744 | ~v1_partfun1(B_1743, A_1744) | ~v4_relat_1(B_1743, A_1744) | ~v1_relat_1(B_1743))), inference(cnfTransformation, [status(thm)], [f_125])).
% 16.97/8.37  tff(c_31578, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_8060, c_31575])).
% 16.97/8.37  tff(c_31584, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7123, c_31578])).
% 16.97/8.37  tff(c_31588, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_31584])).
% 16.97/8.37  tff(c_32264, plain, (![C_1797, A_1798, B_1799]: (v1_partfun1(C_1797, A_1798) | ~v1_funct_2(C_1797, A_1798, B_1799) | ~v1_funct_1(C_1797) | ~m1_subset_1(C_1797, k1_zfmisc_1(k2_zfmisc_1(A_1798, B_1799))) | v1_xboole_0(B_1799))), inference(cnfTransformation, [status(thm)], [f_117])).
% 16.97/8.37  tff(c_32270, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_32264])).
% 16.97/8.37  tff(c_32277, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_32270])).
% 16.97/8.37  tff(c_32279, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_31588, c_32277])).
% 16.97/8.37  tff(c_32280, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_31584])).
% 16.97/8.37  tff(c_32288, plain, (![B_23]: (k7_relat_1('#skF_6', B_23)=k1_xboole_0 | ~r1_xboole_0(B_23, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_32280, c_22])).
% 16.97/8.37  tff(c_32800, plain, (![B_1828]: (k7_relat_1('#skF_6', B_1828)=k1_xboole_0 | ~r1_xboole_0(B_1828, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7123, c_32288])).
% 16.97/8.37  tff(c_32841, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0 | k7_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_8079, c_32800])).
% 16.97/8.37  tff(c_32977, plain, (k7_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32841])).
% 16.97/8.37  tff(c_32297, plain, (![A_14]: (r1_xboole_0('#skF_4', A_14) | k9_relat_1('#skF_6', A_14)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_32280, c_18])).
% 16.97/8.37  tff(c_32766, plain, (![A_1827]: (r1_xboole_0('#skF_4', A_1827) | k9_relat_1('#skF_6', A_1827)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7123, c_32297])).
% 16.97/8.37  tff(c_31203, plain, (![A_1722, B_1723]: (k7_relat_1(A_1722, B_1723)=k1_xboole_0 | ~r1_xboole_0(B_1723, k1_relat_1(A_1722)) | ~v1_relat_1(A_1722))), inference(cnfTransformation, [status(thm)], [f_70])).
% 16.97/8.37  tff(c_31230, plain, (![B_1723]: (k7_relat_1(k1_xboole_0, B_1723)=k1_xboole_0 | ~r1_xboole_0(B_1723, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_31203])).
% 16.97/8.37  tff(c_31238, plain, (![B_1723]: (k7_relat_1(k1_xboole_0, B_1723)=k1_xboole_0 | ~r1_xboole_0(B_1723, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8043, c_31230])).
% 16.97/8.37  tff(c_32794, plain, (k7_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0 | k9_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_32766, c_31238])).
% 16.97/8.37  tff(c_34636, plain, (k9_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_32977, c_32794])).
% 16.97/8.37  tff(c_32300, plain, (![A_26]: (r1_xboole_0('#skF_4', A_26) | k7_relat_1('#skF_6', A_26)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_32280, c_32])).
% 16.97/8.37  tff(c_32901, plain, (![A_1832]: (r1_xboole_0('#skF_4', A_1832) | k7_relat_1('#skF_6', A_1832)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7123, c_32300])).
% 16.97/8.37  tff(c_32285, plain, (![A_14]: (k9_relat_1('#skF_6', A_14)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_14) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_32280, c_16])).
% 16.97/8.37  tff(c_32307, plain, (![A_14]: (k9_relat_1('#skF_6', A_14)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_7123, c_32285])).
% 16.97/8.37  tff(c_33066, plain, (![A_1854]: (k9_relat_1('#skF_6', A_1854)=k1_xboole_0 | k7_relat_1('#skF_6', A_1854)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_32901, c_32307])).
% 16.97/8.37  tff(c_31581, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_8059, c_31575])).
% 16.97/8.37  tff(c_31587, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7122, c_31581])).
% 16.97/8.37  tff(c_32330, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_31587])).
% 16.97/8.37  tff(c_32570, plain, (![C_1816, A_1817, B_1818]: (v1_partfun1(C_1816, A_1817) | ~v1_funct_2(C_1816, A_1817, B_1818) | ~v1_funct_1(C_1816) | ~m1_subset_1(C_1816, k1_zfmisc_1(k2_zfmisc_1(A_1817, B_1818))) | v1_xboole_0(B_1818))), inference(cnfTransformation, [status(thm)], [f_117])).
% 16.97/8.37  tff(c_32573, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_74, c_32570])).
% 16.97/8.37  tff(c_32579, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_32573])).
% 16.97/8.37  tff(c_32581, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_32330, c_32579])).
% 16.97/8.37  tff(c_32582, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_31587])).
% 16.97/8.37  tff(c_32590, plain, (![B_23]: (k7_relat_1('#skF_5', B_23)=k1_xboole_0 | ~r1_xboole_0(B_23, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_32582, c_22])).
% 16.97/8.37  tff(c_32611, plain, (![B_23]: (k7_relat_1('#skF_5', B_23)=k1_xboole_0 | ~r1_xboole_0(B_23, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7122, c_32590])).
% 16.97/8.37  tff(c_32791, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | k9_relat_1('#skF_6', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_32766, c_32611])).
% 16.97/8.37  tff(c_33002, plain, (k9_relat_1('#skF_6', '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32791])).
% 16.97/8.37  tff(c_33091, plain, (k7_relat_1('#skF_6', '#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_33066, c_33002])).
% 16.97/8.37  tff(c_32599, plain, (![A_14]: (r1_xboole_0('#skF_3', A_14) | k9_relat_1('#skF_5', A_14)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_32582, c_18])).
% 16.97/8.37  tff(c_32617, plain, (![A_14]: (r1_xboole_0('#skF_3', A_14) | k9_relat_1('#skF_5', A_14)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7122, c_32599])).
% 16.97/8.37  tff(c_32835, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | k9_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_32617, c_32800])).
% 16.97/8.37  tff(c_33185, plain, (k9_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_33091, c_32835])).
% 16.97/8.37  tff(c_32587, plain, (![A_14]: (k9_relat_1('#skF_5', A_14)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_14) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_32582, c_16])).
% 16.97/8.37  tff(c_32714, plain, (![A_1823]: (k9_relat_1('#skF_5', A_1823)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_1823))), inference(demodulation, [status(thm), theory('equality')], [c_7122, c_32587])).
% 16.97/8.37  tff(c_32721, plain, (![B_29]: (k9_relat_1('#skF_5', B_29)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_29) | v1_xboole_0(B_29) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_32714])).
% 16.97/8.37  tff(c_33271, plain, (![B_1874]: (k9_relat_1('#skF_5', B_1874)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_1874) | v1_xboole_0(B_1874))), inference(negUnitSimplification, [status(thm)], [c_88, c_32721])).
% 16.97/8.37  tff(c_33277, plain, (k9_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_80, c_33271])).
% 16.97/8.37  tff(c_33282, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_33185, c_33277])).
% 16.97/8.37  tff(c_33283, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_32791])).
% 16.97/8.37  tff(c_32602, plain, (![A_26]: (r1_xboole_0('#skF_3', A_26) | k7_relat_1('#skF_5', A_26)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_32582, c_32])).
% 16.97/8.37  tff(c_32844, plain, (![A_1829]: (r1_xboole_0('#skF_3', A_1829) | k7_relat_1('#skF_5', A_1829)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7122, c_32602])).
% 16.97/8.37  tff(c_32609, plain, (![A_14]: (k9_relat_1('#skF_5', A_14)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_7122, c_32587])).
% 16.97/8.37  tff(c_34558, plain, (![A_1978]: (k9_relat_1('#skF_5', A_1978)=k1_xboole_0 | k7_relat_1('#skF_5', A_1978)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_32844, c_32609])).
% 16.97/8.37  tff(c_34518, plain, (k9_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32835])).
% 16.97/8.37  tff(c_34564, plain, (k7_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_34558, c_34518])).
% 16.97/8.37  tff(c_34592, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_33283, c_34564])).
% 16.97/8.37  tff(c_34593, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_32835])).
% 16.97/8.37  tff(c_32939, plain, (![A_1832]: (k3_xboole_0('#skF_4', A_1832)=k1_xboole_0 | k7_relat_1('#skF_6', A_1832)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_32901, c_2])).
% 16.97/8.37  tff(c_34610, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_34593, c_32939])).
% 16.97/8.37  tff(c_32291, plain, (![A_26]: (k7_relat_1('#skF_6', A_26)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_26) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_32280, c_30])).
% 16.97/8.37  tff(c_32628, plain, (![A_1819]: (k7_relat_1('#skF_6', A_1819)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_1819))), inference(demodulation, [status(thm), theory('equality')], [c_7123, c_32291])).
% 16.97/8.37  tff(c_35086, plain, (![B_2018]: (k7_relat_1('#skF_6', B_2018)=k1_xboole_0 | k3_xboole_0('#skF_4', B_2018)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_32628])).
% 16.97/8.37  tff(c_35110, plain, (![B_2018]: (r1_tarski(k1_relat_1(k1_xboole_0), B_2018) | ~v1_relat_1('#skF_6') | k3_xboole_0('#skF_4', B_2018)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_35086, c_28])).
% 16.97/8.37  tff(c_35134, plain, (![B_2018]: (r1_tarski(k1_xboole_0, B_2018) | k3_xboole_0('#skF_4', B_2018)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7123, c_26, c_35110])).
% 16.97/8.37  tff(c_34601, plain, (![B_19]: (k9_relat_1(k1_xboole_0, B_19)=k9_relat_1('#skF_6', B_19) | ~r1_tarski(B_19, '#skF_3') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_34593, c_20])).
% 16.97/8.37  tff(c_35301, plain, (![B_2032]: (k9_relat_1(k1_xboole_0, B_2032)=k9_relat_1('#skF_6', B_2032) | ~r1_tarski(B_2032, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7123, c_34601])).
% 16.97/8.37  tff(c_35305, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k9_relat_1('#skF_6', k1_xboole_0) | k3_xboole_0('#skF_4', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_35134, c_35301])).
% 16.97/8.37  tff(c_35335, plain, (k9_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34610, c_8042, c_35305])).
% 16.97/8.37  tff(c_35337, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34636, c_35335])).
% 16.97/8.37  tff(c_35338, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_32841])).
% 16.97/8.37  tff(c_35486, plain, (![A_2047]: (k9_relat_1('#skF_6', A_2047)=k1_xboole_0 | k7_relat_1('#skF_6', A_2047)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_32901, c_32307])).
% 16.97/8.37  tff(c_35424, plain, (k9_relat_1('#skF_6', '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32791])).
% 16.97/8.37  tff(c_35511, plain, (k7_relat_1('#skF_6', '#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_35486, c_35424])).
% 16.97/8.37  tff(c_32820, plain, (![A_28]: (k7_relat_1('#skF_6', A_28)=k1_xboole_0 | ~r1_subset_1(A_28, '#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(A_28))), inference(resolution, [status(thm)], [c_36, c_32800])).
% 16.97/8.37  tff(c_35522, plain, (![A_2054]: (k7_relat_1('#skF_6', A_2054)=k1_xboole_0 | ~r1_subset_1(A_2054, '#skF_4') | v1_xboole_0(A_2054))), inference(negUnitSimplification, [status(thm)], [c_84, c_32820])).
% 16.97/8.37  tff(c_35537, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_80, c_35522])).
% 16.97/8.37  tff(c_35549, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_35511, c_35537])).
% 16.97/8.37  tff(c_35550, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_32791])).
% 16.97/8.37  tff(c_36998, plain, (![A_2152]: (k3_xboole_0('#skF_3', A_2152)=k1_xboole_0 | k7_relat_1('#skF_5', A_2152)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_32844, c_2])).
% 16.97/8.37  tff(c_37014, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_35550, c_36998])).
% 16.97/8.37  tff(c_31520, plain, (![A_1735, B_1736, C_1737]: (k9_subset_1(A_1735, B_1736, C_1737)=k3_xboole_0(B_1736, C_1737) | ~m1_subset_1(C_1737, k1_zfmisc_1(A_1735)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 16.97/8.37  tff(c_31532, plain, (![B_1736]: (k9_subset_1('#skF_1', B_1736, '#skF_4')=k3_xboole_0(B_1736, '#skF_4'))), inference(resolution, [status(thm)], [c_82, c_31520])).
% 16.97/8.37  tff(c_32593, plain, (![A_26]: (k7_relat_1('#skF_5', A_26)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_26) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_32582, c_30])).
% 16.97/8.37  tff(c_32880, plain, (![A_1831]: (k7_relat_1('#skF_5', A_1831)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_1831))), inference(demodulation, [status(thm), theory('equality')], [c_7122, c_32593])).
% 16.97/8.37  tff(c_32900, plain, (![B_2]: (k7_relat_1('#skF_5', B_2)=k1_xboole_0 | k3_xboole_0('#skF_3', B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_32880])).
% 16.97/8.37  tff(c_32873, plain, (k7_relat_1(k1_xboole_0, '#skF_3')=k1_xboole_0 | k7_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_32844, c_31238])).
% 16.97/8.37  tff(c_35695, plain, (k7_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32873])).
% 16.97/8.37  tff(c_35710, plain, (k3_xboole_0('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_32900, c_35695])).
% 16.97/8.37  tff(c_32641, plain, (![A_1820]: (r1_xboole_0('#skF_3', A_1820) | k9_relat_1('#skF_5', A_1820)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7122, c_32599])).
% 16.97/8.37  tff(c_32656, plain, (k7_relat_1(k1_xboole_0, '#skF_3')=k1_xboole_0 | k9_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_32641, c_31238])).
% 16.97/8.37  tff(c_35978, plain, (k9_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32656])).
% 16.97/8.37  tff(c_32309, plain, (![B_23]: (k7_relat_1('#skF_6', B_23)=k1_xboole_0 | ~r1_xboole_0(B_23, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7123, c_32288])).
% 16.97/8.37  tff(c_32870, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | k7_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_32844, c_32309])).
% 16.97/8.37  tff(c_35820, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_35550, c_32870])).
% 16.97/8.37  tff(c_35840, plain, (![A_2081]: (k3_xboole_0('#skF_4', A_2081)=k1_xboole_0 | k7_relat_1('#skF_6', A_2081)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_32901, c_2])).
% 16.97/8.37  tff(c_35847, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_35820, c_35840])).
% 16.97/8.37  tff(c_32675, plain, (![B_1822]: (k7_relat_1('#skF_5', B_1822)=k1_xboole_0 | ~r1_xboole_0(B_1822, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7122, c_32590])).
% 16.97/8.37  tff(c_36137, plain, (![A_2103]: (k7_relat_1('#skF_5', A_2103)=k1_xboole_0 | k3_xboole_0(A_2103, '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_32675])).
% 16.97/8.37  tff(c_36158, plain, (![A_2103]: (r1_tarski(k1_relat_1(k1_xboole_0), A_2103) | ~v1_relat_1('#skF_5') | k3_xboole_0(A_2103, '#skF_3')!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_36137, c_28])).
% 16.97/8.37  tff(c_36181, plain, (![A_2103]: (r1_tarski(k1_xboole_0, A_2103) | k3_xboole_0(A_2103, '#skF_3')!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7122, c_26, c_36158])).
% 16.97/8.37  tff(c_35555, plain, (![B_19]: (k9_relat_1(k1_xboole_0, B_19)=k9_relat_1('#skF_5', B_19) | ~r1_tarski(B_19, '#skF_4') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_35550, c_20])).
% 16.97/8.37  tff(c_36404, plain, (![B_2119]: (k9_relat_1(k1_xboole_0, B_2119)=k9_relat_1('#skF_5', B_2119) | ~r1_tarski(B_2119, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7122, c_35555])).
% 16.97/8.37  tff(c_36408, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k9_relat_1('#skF_5', k1_xboole_0) | k3_xboole_0('#skF_4', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_36181, c_36404])).
% 16.97/8.37  tff(c_36438, plain, (k9_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_35847, c_8042, c_36408])).
% 16.97/8.37  tff(c_36440, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35978, c_36438])).
% 16.97/8.37  tff(c_36442, plain, (k9_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_32656])).
% 16.97/8.37  tff(c_32661, plain, (![A_1820]: (k3_xboole_0('#skF_3', A_1820)=k1_xboole_0 | k9_relat_1('#skF_5', A_1820)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_32641, c_2])).
% 16.97/8.37  tff(c_36493, plain, (k3_xboole_0('#skF_3', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_36442, c_32661])).
% 16.97/8.37  tff(c_36511, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35710, c_36493])).
% 16.97/8.37  tff(c_36513, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_32873])).
% 16.97/8.37  tff(c_32942, plain, (![A_1833, B_1834, C_1835, D_1836]: (k2_partfun1(A_1833, B_1834, C_1835, D_1836)=k7_relat_1(C_1835, D_1836) | ~m1_subset_1(C_1835, k1_zfmisc_1(k2_zfmisc_1(A_1833, B_1834))) | ~v1_funct_1(C_1835))), inference(cnfTransformation, [status(thm)], [f_131])).
% 16.97/8.37  tff(c_32944, plain, (![D_1836]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_1836)=k7_relat_1('#skF_5', D_1836) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_74, c_32942])).
% 16.97/8.37  tff(c_32949, plain, (![D_1836]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_1836)=k7_relat_1('#skF_5', D_1836))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_32944])).
% 16.97/8.37  tff(c_32946, plain, (![D_1836]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_1836)=k7_relat_1('#skF_6', D_1836) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_68, c_32942])).
% 16.97/8.37  tff(c_32952, plain, (![D_1836]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_1836)=k7_relat_1('#skF_6', D_1836))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_32946])).
% 16.97/8.37  tff(c_35608, plain, (![D_2060, E_2058, C_2056, B_2059, F_2061, A_2057]: (v1_funct_1(k1_tmap_1(A_2057, B_2059, C_2056, D_2060, E_2058, F_2061)) | ~m1_subset_1(F_2061, k1_zfmisc_1(k2_zfmisc_1(D_2060, B_2059))) | ~v1_funct_2(F_2061, D_2060, B_2059) | ~v1_funct_1(F_2061) | ~m1_subset_1(E_2058, k1_zfmisc_1(k2_zfmisc_1(C_2056, B_2059))) | ~v1_funct_2(E_2058, C_2056, B_2059) | ~v1_funct_1(E_2058) | ~m1_subset_1(D_2060, k1_zfmisc_1(A_2057)) | v1_xboole_0(D_2060) | ~m1_subset_1(C_2056, k1_zfmisc_1(A_2057)) | v1_xboole_0(C_2056) | v1_xboole_0(B_2059) | v1_xboole_0(A_2057))), inference(cnfTransformation, [status(thm)], [f_213])).
% 16.97/8.37  tff(c_35612, plain, (![A_2057, C_2056, E_2058]: (v1_funct_1(k1_tmap_1(A_2057, '#skF_2', C_2056, '#skF_4', E_2058, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_2058, k1_zfmisc_1(k2_zfmisc_1(C_2056, '#skF_2'))) | ~v1_funct_2(E_2058, C_2056, '#skF_2') | ~v1_funct_1(E_2058) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2057)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_2056, k1_zfmisc_1(A_2057)) | v1_xboole_0(C_2056) | v1_xboole_0('#skF_2') | v1_xboole_0(A_2057))), inference(resolution, [status(thm)], [c_68, c_35608])).
% 16.97/8.37  tff(c_35619, plain, (![A_2057, C_2056, E_2058]: (v1_funct_1(k1_tmap_1(A_2057, '#skF_2', C_2056, '#skF_4', E_2058, '#skF_6')) | ~m1_subset_1(E_2058, k1_zfmisc_1(k2_zfmisc_1(C_2056, '#skF_2'))) | ~v1_funct_2(E_2058, C_2056, '#skF_2') | ~v1_funct_1(E_2058) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2057)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_2056, k1_zfmisc_1(A_2057)) | v1_xboole_0(C_2056) | v1_xboole_0('#skF_2') | v1_xboole_0(A_2057))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_35612])).
% 16.97/8.37  tff(c_37397, plain, (![A_2171, C_2172, E_2173]: (v1_funct_1(k1_tmap_1(A_2171, '#skF_2', C_2172, '#skF_4', E_2173, '#skF_6')) | ~m1_subset_1(E_2173, k1_zfmisc_1(k2_zfmisc_1(C_2172, '#skF_2'))) | ~v1_funct_2(E_2173, C_2172, '#skF_2') | ~v1_funct_1(E_2173) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2171)) | ~m1_subset_1(C_2172, k1_zfmisc_1(A_2171)) | v1_xboole_0(C_2172) | v1_xboole_0(A_2171))), inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_35619])).
% 16.97/8.37  tff(c_37402, plain, (![A_2171]: (v1_funct_1(k1_tmap_1(A_2171, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2171)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_2171)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2171))), inference(resolution, [status(thm)], [c_74, c_37397])).
% 16.97/8.37  tff(c_37410, plain, (![A_2171]: (v1_funct_1(k1_tmap_1(A_2171, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2171)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_2171)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2171))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_37402])).
% 16.97/8.37  tff(c_37689, plain, (![A_2182]: (v1_funct_1(k1_tmap_1(A_2182, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2182)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_2182)) | v1_xboole_0(A_2182))), inference(negUnitSimplification, [status(thm)], [c_88, c_37410])).
% 16.97/8.37  tff(c_37692, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_86, c_37689])).
% 16.97/8.37  tff(c_37695, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_37692])).
% 16.97/8.37  tff(c_37696, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_92, c_37695])).
% 16.97/8.37  tff(c_36840, plain, (![B_2142, E_2141, D_2143, C_2144, F_2140, A_2145]: (k2_partfun1(k4_subset_1(A_2145, C_2144, D_2143), B_2142, k1_tmap_1(A_2145, B_2142, C_2144, D_2143, E_2141, F_2140), C_2144)=E_2141 | ~m1_subset_1(k1_tmap_1(A_2145, B_2142, C_2144, D_2143, E_2141, F_2140), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_2145, C_2144, D_2143), B_2142))) | ~v1_funct_2(k1_tmap_1(A_2145, B_2142, C_2144, D_2143, E_2141, F_2140), k4_subset_1(A_2145, C_2144, D_2143), B_2142) | ~v1_funct_1(k1_tmap_1(A_2145, B_2142, C_2144, D_2143, E_2141, F_2140)) | k2_partfun1(D_2143, B_2142, F_2140, k9_subset_1(A_2145, C_2144, D_2143))!=k2_partfun1(C_2144, B_2142, E_2141, k9_subset_1(A_2145, C_2144, D_2143)) | ~m1_subset_1(F_2140, k1_zfmisc_1(k2_zfmisc_1(D_2143, B_2142))) | ~v1_funct_2(F_2140, D_2143, B_2142) | ~v1_funct_1(F_2140) | ~m1_subset_1(E_2141, k1_zfmisc_1(k2_zfmisc_1(C_2144, B_2142))) | ~v1_funct_2(E_2141, C_2144, B_2142) | ~v1_funct_1(E_2141) | ~m1_subset_1(D_2143, k1_zfmisc_1(A_2145)) | v1_xboole_0(D_2143) | ~m1_subset_1(C_2144, k1_zfmisc_1(A_2145)) | v1_xboole_0(C_2144) | v1_xboole_0(B_2142) | v1_xboole_0(A_2145))), inference(cnfTransformation, [status(thm)], [f_179])).
% 16.97/8.37  tff(c_45304, plain, (![E_2426, F_2429, D_2428, C_2424, B_2427, A_2425]: (k2_partfun1(k4_subset_1(A_2425, C_2424, D_2428), B_2427, k1_tmap_1(A_2425, B_2427, C_2424, D_2428, E_2426, F_2429), C_2424)=E_2426 | ~v1_funct_2(k1_tmap_1(A_2425, B_2427, C_2424, D_2428, E_2426, F_2429), k4_subset_1(A_2425, C_2424, D_2428), B_2427) | ~v1_funct_1(k1_tmap_1(A_2425, B_2427, C_2424, D_2428, E_2426, F_2429)) | k2_partfun1(D_2428, B_2427, F_2429, k9_subset_1(A_2425, C_2424, D_2428))!=k2_partfun1(C_2424, B_2427, E_2426, k9_subset_1(A_2425, C_2424, D_2428)) | ~m1_subset_1(F_2429, k1_zfmisc_1(k2_zfmisc_1(D_2428, B_2427))) | ~v1_funct_2(F_2429, D_2428, B_2427) | ~v1_funct_1(F_2429) | ~m1_subset_1(E_2426, k1_zfmisc_1(k2_zfmisc_1(C_2424, B_2427))) | ~v1_funct_2(E_2426, C_2424, B_2427) | ~v1_funct_1(E_2426) | ~m1_subset_1(D_2428, k1_zfmisc_1(A_2425)) | v1_xboole_0(D_2428) | ~m1_subset_1(C_2424, k1_zfmisc_1(A_2425)) | v1_xboole_0(C_2424) | v1_xboole_0(B_2427) | v1_xboole_0(A_2425))), inference(resolution, [status(thm)], [c_60, c_36840])).
% 16.97/8.37  tff(c_50814, plain, (![C_2565, D_2569, F_2570, B_2568, A_2566, E_2567]: (k2_partfun1(k4_subset_1(A_2566, C_2565, D_2569), B_2568, k1_tmap_1(A_2566, B_2568, C_2565, D_2569, E_2567, F_2570), C_2565)=E_2567 | ~v1_funct_1(k1_tmap_1(A_2566, B_2568, C_2565, D_2569, E_2567, F_2570)) | k2_partfun1(D_2569, B_2568, F_2570, k9_subset_1(A_2566, C_2565, D_2569))!=k2_partfun1(C_2565, B_2568, E_2567, k9_subset_1(A_2566, C_2565, D_2569)) | ~m1_subset_1(F_2570, k1_zfmisc_1(k2_zfmisc_1(D_2569, B_2568))) | ~v1_funct_2(F_2570, D_2569, B_2568) | ~v1_funct_1(F_2570) | ~m1_subset_1(E_2567, k1_zfmisc_1(k2_zfmisc_1(C_2565, B_2568))) | ~v1_funct_2(E_2567, C_2565, B_2568) | ~v1_funct_1(E_2567) | ~m1_subset_1(D_2569, k1_zfmisc_1(A_2566)) | v1_xboole_0(D_2569) | ~m1_subset_1(C_2565, k1_zfmisc_1(A_2566)) | v1_xboole_0(C_2565) | v1_xboole_0(B_2568) | v1_xboole_0(A_2566))), inference(resolution, [status(thm)], [c_62, c_45304])).
% 16.97/8.37  tff(c_50820, plain, (![A_2566, C_2565, E_2567]: (k2_partfun1(k4_subset_1(A_2566, C_2565, '#skF_4'), '#skF_2', k1_tmap_1(A_2566, '#skF_2', C_2565, '#skF_4', E_2567, '#skF_6'), C_2565)=E_2567 | ~v1_funct_1(k1_tmap_1(A_2566, '#skF_2', C_2565, '#skF_4', E_2567, '#skF_6')) | k2_partfun1(C_2565, '#skF_2', E_2567, k9_subset_1(A_2566, C_2565, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_2566, C_2565, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_2567, k1_zfmisc_1(k2_zfmisc_1(C_2565, '#skF_2'))) | ~v1_funct_2(E_2567, C_2565, '#skF_2') | ~v1_funct_1(E_2567) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2566)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_2565, k1_zfmisc_1(A_2566)) | v1_xboole_0(C_2565) | v1_xboole_0('#skF_2') | v1_xboole_0(A_2566))), inference(resolution, [status(thm)], [c_68, c_50814])).
% 16.97/8.37  tff(c_50828, plain, (![A_2566, C_2565, E_2567]: (k2_partfun1(k4_subset_1(A_2566, C_2565, '#skF_4'), '#skF_2', k1_tmap_1(A_2566, '#skF_2', C_2565, '#skF_4', E_2567, '#skF_6'), C_2565)=E_2567 | ~v1_funct_1(k1_tmap_1(A_2566, '#skF_2', C_2565, '#skF_4', E_2567, '#skF_6')) | k2_partfun1(C_2565, '#skF_2', E_2567, k9_subset_1(A_2566, C_2565, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2566, C_2565, '#skF_4')) | ~m1_subset_1(E_2567, k1_zfmisc_1(k2_zfmisc_1(C_2565, '#skF_2'))) | ~v1_funct_2(E_2567, C_2565, '#skF_2') | ~v1_funct_1(E_2567) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2566)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_2565, k1_zfmisc_1(A_2566)) | v1_xboole_0(C_2565) | v1_xboole_0('#skF_2') | v1_xboole_0(A_2566))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_32952, c_50820])).
% 16.97/8.37  tff(c_53643, plain, (![A_2614, C_2615, E_2616]: (k2_partfun1(k4_subset_1(A_2614, C_2615, '#skF_4'), '#skF_2', k1_tmap_1(A_2614, '#skF_2', C_2615, '#skF_4', E_2616, '#skF_6'), C_2615)=E_2616 | ~v1_funct_1(k1_tmap_1(A_2614, '#skF_2', C_2615, '#skF_4', E_2616, '#skF_6')) | k2_partfun1(C_2615, '#skF_2', E_2616, k9_subset_1(A_2614, C_2615, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2614, C_2615, '#skF_4')) | ~m1_subset_1(E_2616, k1_zfmisc_1(k2_zfmisc_1(C_2615, '#skF_2'))) | ~v1_funct_2(E_2616, C_2615, '#skF_2') | ~v1_funct_1(E_2616) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2614)) | ~m1_subset_1(C_2615, k1_zfmisc_1(A_2614)) | v1_xboole_0(C_2615) | v1_xboole_0(A_2614))), inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_50828])).
% 16.97/8.37  tff(c_53648, plain, (![A_2614]: (k2_partfun1(k4_subset_1(A_2614, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_2614, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_2614, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_2614, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2614, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2614)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_2614)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2614))), inference(resolution, [status(thm)], [c_74, c_53643])).
% 16.97/8.37  tff(c_53656, plain, (![A_2614]: (k2_partfun1(k4_subset_1(A_2614, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_2614, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_2614, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_2614, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2614, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2614)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_2614)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2614))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_32949, c_53648])).
% 16.97/8.37  tff(c_53924, plain, (![A_2630]: (k2_partfun1(k4_subset_1(A_2630, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_2630, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_2630, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_2630, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2630, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2630)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_2630)) | v1_xboole_0(A_2630))), inference(negUnitSimplification, [status(thm)], [c_88, c_53656])).
% 16.97/8.37  tff(c_31085, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6'), inference(splitRight, [status(thm)], [c_7092])).
% 16.97/8.37  tff(c_37015, plain, (![B_2153, C_2155, D_2154, A_2156, G_2157]: (k1_tmap_1(A_2156, B_2153, C_2155, D_2154, k2_partfun1(k4_subset_1(A_2156, C_2155, D_2154), B_2153, G_2157, C_2155), k2_partfun1(k4_subset_1(A_2156, C_2155, D_2154), B_2153, G_2157, D_2154))=G_2157 | ~m1_subset_1(G_2157, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_2156, C_2155, D_2154), B_2153))) | ~v1_funct_2(G_2157, k4_subset_1(A_2156, C_2155, D_2154), B_2153) | ~v1_funct_1(G_2157) | k2_partfun1(D_2154, B_2153, k2_partfun1(k4_subset_1(A_2156, C_2155, D_2154), B_2153, G_2157, D_2154), k9_subset_1(A_2156, C_2155, D_2154))!=k2_partfun1(C_2155, B_2153, k2_partfun1(k4_subset_1(A_2156, C_2155, D_2154), B_2153, G_2157, C_2155), k9_subset_1(A_2156, C_2155, D_2154)) | ~m1_subset_1(k2_partfun1(k4_subset_1(A_2156, C_2155, D_2154), B_2153, G_2157, D_2154), k1_zfmisc_1(k2_zfmisc_1(D_2154, B_2153))) | ~v1_funct_2(k2_partfun1(k4_subset_1(A_2156, C_2155, D_2154), B_2153, G_2157, D_2154), D_2154, B_2153) | ~v1_funct_1(k2_partfun1(k4_subset_1(A_2156, C_2155, D_2154), B_2153, G_2157, D_2154)) | ~m1_subset_1(k2_partfun1(k4_subset_1(A_2156, C_2155, D_2154), B_2153, G_2157, C_2155), k1_zfmisc_1(k2_zfmisc_1(C_2155, B_2153))) | ~v1_funct_2(k2_partfun1(k4_subset_1(A_2156, C_2155, D_2154), B_2153, G_2157, C_2155), C_2155, B_2153) | ~v1_funct_1(k2_partfun1(k4_subset_1(A_2156, C_2155, D_2154), B_2153, G_2157, C_2155)) | ~m1_subset_1(D_2154, k1_zfmisc_1(A_2156)) | v1_xboole_0(D_2154) | ~m1_subset_1(C_2155, k1_zfmisc_1(A_2156)) | v1_xboole_0(C_2155) | v1_xboole_0(B_2153) | v1_xboole_0(A_2156))), inference(cnfTransformation, [status(thm)], [f_179])).
% 16.97/8.37  tff(c_37017, plain, (k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4'))=k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6') | ~m1_subset_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2'))) | ~v1_funct_2(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4'), k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_2(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')) | ~m1_subset_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_31085, c_37015])).
% 16.97/8.37  tff(c_37019, plain, (k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_6')=k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6') | ~m1_subset_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2'))) | ~v1_funct_2(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k3_xboole_0('#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k3_xboole_0('#skF_3', '#skF_4')) | ~m1_subset_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')) | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_72, c_31085, c_70, c_31085, c_68, c_32952, c_31085, c_31532, c_31532, c_31085, c_37017])).
% 16.97/8.37  tff(c_37020, plain, (k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_6')=k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6') | ~m1_subset_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2'))) | ~v1_funct_2(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k3_xboole_0('#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k3_xboole_0('#skF_3', '#skF_4')) | ~m1_subset_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_92, c_90, c_88, c_84, c_37019])).
% 16.97/8.37  tff(c_38985, plain, (k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_6')=k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6') | ~m1_subset_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2'))) | ~v1_funct_2(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | k2_partfun1('#skF_3', '#skF_2', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k1_xboole_0)!=k1_xboole_0 | ~m1_subset_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_35338, c_37014, c_37014, c_37696, c_37020])).
% 16.97/8.37  tff(c_38986, plain, (~v1_funct_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_38985])).
% 16.97/8.37  tff(c_53933, plain, (~v1_funct_1('#skF_5') | ~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_53924, c_38986])).
% 16.97/8.37  tff(c_53946, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_35338, c_37014, c_31532, c_36513, c_37014, c_31532, c_37696, c_78, c_53933])).
% 16.97/8.37  tff(c_53948, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_53946])).
% 16.97/8.37  tff(c_53949, plain, (~v1_funct_2(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | k2_partfun1('#skF_3', '#skF_2', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k1_xboole_0)!=k1_xboole_0 | ~v1_funct_2(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2'))) | k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_6')=k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_38985])).
% 16.97/8.37  tff(c_54848, plain, (~m1_subset_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2')))), inference(splitLeft, [status(thm)], [c_53949])).
% 16.97/8.37  tff(c_55374, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_54848])).
% 16.97/8.37  tff(c_55377, plain, (v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_78, c_76, c_74, c_72, c_70, c_68, c_55374])).
% 16.97/8.37  tff(c_55379, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_90, c_88, c_84, c_55377])).
% 16.97/8.37  tff(c_55381, plain, (m1_subset_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2')))), inference(splitRight, [status(thm)], [c_53949])).
% 16.97/8.37  tff(c_58, plain, (![A_46, E_166, F_170, B_110, D_158, C_142]: (k2_partfun1(k4_subset_1(A_46, C_142, D_158), B_110, k1_tmap_1(A_46, B_110, C_142, D_158, E_166, F_170), C_142)=E_166 | ~m1_subset_1(k1_tmap_1(A_46, B_110, C_142, D_158, E_166, F_170), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_46, C_142, D_158), B_110))) | ~v1_funct_2(k1_tmap_1(A_46, B_110, C_142, D_158, E_166, F_170), k4_subset_1(A_46, C_142, D_158), B_110) | ~v1_funct_1(k1_tmap_1(A_46, B_110, C_142, D_158, E_166, F_170)) | k2_partfun1(D_158, B_110, F_170, k9_subset_1(A_46, C_142, D_158))!=k2_partfun1(C_142, B_110, E_166, k9_subset_1(A_46, C_142, D_158)) | ~m1_subset_1(F_170, k1_zfmisc_1(k2_zfmisc_1(D_158, B_110))) | ~v1_funct_2(F_170, D_158, B_110) | ~v1_funct_1(F_170) | ~m1_subset_1(E_166, k1_zfmisc_1(k2_zfmisc_1(C_142, B_110))) | ~v1_funct_2(E_166, C_142, B_110) | ~v1_funct_1(E_166) | ~m1_subset_1(D_158, k1_zfmisc_1(A_46)) | v1_xboole_0(D_158) | ~m1_subset_1(C_142, k1_zfmisc_1(A_46)) | v1_xboole_0(C_142) | v1_xboole_0(B_110) | v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_179])).
% 16.97/8.37  tff(c_55910, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_2(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_55381, c_58])).
% 16.97/8.37  tff(c_55942, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_2(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_78, c_76, c_74, c_72, c_70, c_68, c_35338, c_37014, c_31532, c_36513, c_37014, c_31532, c_32949, c_32952, c_37696, c_55910])).
% 16.97/8.37  tff(c_55943, plain, (~v1_funct_2(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_92, c_90, c_88, c_84, c_31084, c_55942])).
% 16.97/8.37  tff(c_55975, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_62, c_55943])).
% 16.97/8.37  tff(c_55978, plain, (v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_78, c_76, c_74, c_72, c_70, c_68, c_55975])).
% 16.97/8.37  tff(c_55980, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_90, c_88, c_84, c_55978])).
% 16.97/8.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.97/8.37  
% 16.97/8.37  Inference rules
% 16.97/8.37  ----------------------
% 16.97/8.37  #Ref     : 0
% 16.97/8.37  #Sup     : 11237
% 16.97/8.37  #Fact    : 0
% 16.97/8.37  #Define  : 0
% 16.97/8.37  #Split   : 93
% 16.97/8.37  #Chain   : 0
% 16.97/8.37  #Close   : 0
% 16.97/8.37  
% 16.97/8.37  Ordering : KBO
% 16.97/8.37  
% 16.97/8.37  Simplification rules
% 16.97/8.37  ----------------------
% 16.97/8.37  #Subsume      : 2016
% 16.97/8.37  #Demod        : 18580
% 16.97/8.37  #Tautology    : 6504
% 16.97/8.37  #SimpNegUnit  : 872
% 16.97/8.37  #BackRed      : 31
% 16.97/8.37  
% 16.97/8.37  #Partial instantiations: 0
% 16.97/8.37  #Strategies tried      : 1
% 16.97/8.37  
% 16.97/8.37  Timing (in seconds)
% 16.97/8.37  ----------------------
% 16.97/8.38  Preprocessing        : 0.45
% 16.97/8.38  Parsing              : 0.23
% 16.97/8.38  CNF conversion       : 0.06
% 16.97/8.38  Main loop            : 6.96
% 16.97/8.38  Inferencing          : 1.87
% 16.97/8.38  Reduction            : 2.62
% 16.97/8.38  Demodulation         : 1.96
% 16.97/8.38  BG Simplification    : 0.16
% 16.97/8.38  Subsumption          : 1.94
% 16.97/8.38  Abstraction          : 0.21
% 16.97/8.38  MUC search           : 0.00
% 16.97/8.38  Cooper               : 0.00
% 16.97/8.38  Total                : 7.61
% 16.97/8.38  Index Insertion      : 0.00
% 16.97/8.38  Index Deletion       : 0.00
% 16.97/8.38  Index Matching       : 0.00
% 16.97/8.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
