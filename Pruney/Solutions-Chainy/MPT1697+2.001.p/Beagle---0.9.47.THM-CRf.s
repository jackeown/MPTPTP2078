%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:08 EST 2020

% Result     : Theorem 15.58s
% Output     : CNFRefutation 16.24s
% Verified   : 
% Statistics : Number of formulae       :  497 (5007 expanded)
%              Number of leaves         :   54 (1685 expanded)
%              Depth                    :   21
%              Number of atoms          : 1398 (20648 expanded)
%              Number of equality atoms :  429 (4318 expanded)
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

tff(f_256,negated_conjecture,(
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

tff(f_214,axiom,(
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

tff(f_30,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_74,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_126,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_118,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_94,axiom,(
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

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_132,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_180,axiom,(
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

tff(c_94,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_92,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_90,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_86,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_88,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_84,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_80,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_78,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_76,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_74,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_72,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_70,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_64,plain,(
    ! [F_177,D_175,A_172,C_174,E_176,B_173] :
      ( v1_funct_2(k1_tmap_1(A_172,B_173,C_174,D_175,E_176,F_177),k4_subset_1(A_172,C_174,D_175),B_173)
      | ~ m1_subset_1(F_177,k1_zfmisc_1(k2_zfmisc_1(D_175,B_173)))
      | ~ v1_funct_2(F_177,D_175,B_173)
      | ~ v1_funct_1(F_177)
      | ~ m1_subset_1(E_176,k1_zfmisc_1(k2_zfmisc_1(C_174,B_173)))
      | ~ v1_funct_2(E_176,C_174,B_173)
      | ~ v1_funct_1(E_176)
      | ~ m1_subset_1(D_175,k1_zfmisc_1(A_172))
      | v1_xboole_0(D_175)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(A_172))
      | v1_xboole_0(C_174)
      | v1_xboole_0(B_173)
      | v1_xboole_0(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_103,plain,(
    ! [A_235] :
      ( v1_relat_1(A_235)
      | ~ v1_xboole_0(A_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_107,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_103])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6598,plain,(
    ! [B_726,A_727] :
      ( r1_xboole_0(k1_relat_1(B_726),A_727)
      | k7_relat_1(B_726,A_727) != k1_xboole_0
      | ~ v1_relat_1(B_726) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_6607,plain,(
    ! [A_727] :
      ( r1_xboole_0(k1_xboole_0,A_727)
      | k7_relat_1(k1_xboole_0,A_727) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_6598])).

tff(c_6612,plain,(
    ! [A_728] :
      ( r1_xboole_0(k1_xboole_0,A_728)
      | k7_relat_1(k1_xboole_0,A_728) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_6607])).

tff(c_6551,plain,(
    ! [B_722,A_723] :
      ( k9_relat_1(B_722,A_723) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_722),A_723)
      | ~ v1_relat_1(B_722) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6558,plain,(
    ! [A_723] :
      ( k9_relat_1(k1_xboole_0,A_723) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_723)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_6551])).

tff(c_6561,plain,(
    ! [A_723] :
      ( k9_relat_1(k1_xboole_0,A_723) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_723) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_6558])).

tff(c_6619,plain,(
    ! [A_728] :
      ( k9_relat_1(k1_xboole_0,A_728) = k1_xboole_0
      | k7_relat_1(k1_xboole_0,A_728) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6612,c_6561])).

tff(c_6781,plain,(
    ! [B_743,A_744] :
      ( r1_xboole_0(k1_relat_1(B_743),A_744)
      | k9_relat_1(B_743,A_744) != k1_xboole_0
      | ~ v1_relat_1(B_743) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6800,plain,(
    ! [A_744] :
      ( r1_xboole_0(k1_xboole_0,A_744)
      | k9_relat_1(k1_xboole_0,A_744) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_6781])).

tff(c_6807,plain,(
    ! [A_744] :
      ( r1_xboole_0(k1_xboole_0,A_744)
      | k9_relat_1(k1_xboole_0,A_744) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_6800])).

tff(c_6480,plain,(
    ! [C_708,A_709,B_710] :
      ( v1_relat_1(C_708)
      | ~ m1_subset_1(C_708,k1_zfmisc_1(k2_zfmisc_1(A_709,B_710))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_6488,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_6480])).

tff(c_6533,plain,(
    ! [C_716,A_717,B_718] :
      ( v4_relat_1(C_716,A_717)
      | ~ m1_subset_1(C_716,k1_zfmisc_1(k2_zfmisc_1(A_717,B_718))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_6541,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_6533])).

tff(c_6886,plain,(
    ! [B_747,A_748] :
      ( k1_relat_1(B_747) = A_748
      | ~ v1_partfun1(B_747,A_748)
      | ~ v4_relat_1(B_747,A_748)
      | ~ v1_relat_1(B_747) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_6889,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_6541,c_6886])).

tff(c_6895,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6488,c_6889])).

tff(c_6903,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_6895])).

tff(c_7696,plain,(
    ! [C_816,A_817,B_818] :
      ( v1_partfun1(C_816,A_817)
      | ~ v1_funct_2(C_816,A_817,B_818)
      | ~ v1_funct_1(C_816)
      | ~ m1_subset_1(C_816,k1_zfmisc_1(k2_zfmisc_1(A_817,B_818)))
      | v1_xboole_0(B_818) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_7702,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_7696])).

tff(c_7709,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_7702])).

tff(c_7711,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_6903,c_7709])).

tff(c_7712,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6895])).

tff(c_24,plain,(
    ! [A_20,B_22] :
      ( k7_relat_1(A_20,B_22) = k1_xboole_0
      | ~ r1_xboole_0(B_22,k1_relat_1(A_20))
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_7720,plain,(
    ! [B_22] :
      ( k7_relat_1('#skF_6',B_22) = k1_xboole_0
      | ~ r1_xboole_0(B_22,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7712,c_24])).

tff(c_8497,plain,(
    ! [B_870] :
      ( k7_relat_1('#skF_6',B_870) = k1_xboole_0
      | ~ r1_xboole_0(B_870,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6488,c_7720])).

tff(c_8543,plain,
    ( k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0
    | k9_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6807,c_8497])).

tff(c_9998,plain,(
    k9_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_8543])).

tff(c_10005,plain,(
    k7_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6619,c_9998])).

tff(c_20,plain,(
    ! [B_14,A_13] :
      ( r1_xboole_0(k1_relat_1(B_14),A_13)
      | k9_relat_1(B_14,A_13) != k1_xboole_0
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_7717,plain,(
    ! [A_13] :
      ( r1_xboole_0('#skF_4',A_13)
      | k9_relat_1('#skF_6',A_13) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7712,c_20])).

tff(c_8330,plain,(
    ! [A_864] :
      ( r1_xboole_0('#skF_4',A_864)
      | k9_relat_1('#skF_6',A_864) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6488,c_7717])).

tff(c_6755,plain,(
    ! [A_741,B_742] :
      ( k7_relat_1(A_741,B_742) = k1_xboole_0
      | ~ r1_xboole_0(B_742,k1_relat_1(A_741))
      | ~ v1_relat_1(A_741) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6774,plain,(
    ! [B_742] :
      ( k7_relat_1(k1_xboole_0,B_742) = k1_xboole_0
      | ~ r1_xboole_0(B_742,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_6755])).

tff(c_6780,plain,(
    ! [B_742] :
      ( k7_relat_1(k1_xboole_0,B_742) = k1_xboole_0
      | ~ r1_xboole_0(B_742,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_6774])).

tff(c_8349,plain,
    ( k7_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0
    | k9_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8330,c_6780])).

tff(c_10109,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_10005,c_8349])).

tff(c_82,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_38,plain,(
    ! [A_27,B_28] :
      ( r1_xboole_0(A_27,B_28)
      | ~ r1_subset_1(A_27,B_28)
      | v1_xboole_0(B_28)
      | v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_6487,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_6480])).

tff(c_6540,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_6533])).

tff(c_6892,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_6540,c_6886])).

tff(c_6898,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6487,c_6892])).

tff(c_7754,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_6898])).

tff(c_8172,plain,(
    ! [C_852,A_853,B_854] :
      ( v1_partfun1(C_852,A_853)
      | ~ v1_funct_2(C_852,A_853,B_854)
      | ~ v1_funct_1(C_852)
      | ~ m1_subset_1(C_852,k1_zfmisc_1(k2_zfmisc_1(A_853,B_854)))
      | v1_xboole_0(B_854) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_8175,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_8172])).

tff(c_8181,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_8175])).

tff(c_8183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_7754,c_8181])).

tff(c_8184,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_6898])).

tff(c_18,plain,(
    ! [B_14,A_13] :
      ( k9_relat_1(B_14,A_13) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_14),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8204,plain,(
    ! [A_13] :
      ( k9_relat_1('#skF_5',A_13) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_13)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8184,c_18])).

tff(c_8272,plain,(
    ! [A_857] :
      ( k9_relat_1('#skF_5',A_857) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_857) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6487,c_8204])).

tff(c_8276,plain,(
    ! [B_28] :
      ( k9_relat_1('#skF_5',B_28) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_28)
      | v1_xboole_0(B_28)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_8272])).

tff(c_8710,plain,(
    ! [B_886] :
      ( k9_relat_1('#skF_5',B_886) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_886)
      | v1_xboole_0(B_886) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_8276])).

tff(c_8713,plain,
    ( k9_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_8710])).

tff(c_8716,plain,(
    k9_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_8713])).

tff(c_8189,plain,(
    ! [A_13] :
      ( r1_xboole_0('#skF_3',A_13)
      | k9_relat_1('#skF_5',A_13) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8184,c_20])).

tff(c_8211,plain,(
    ! [A_13] :
      ( r1_xboole_0('#skF_3',A_13)
      | k9_relat_1('#skF_5',A_13) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6487,c_8189])).

tff(c_8539,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | k9_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8211,c_8497])).

tff(c_9983,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8716,c_8539])).

tff(c_34,plain,(
    ! [B_26,A_25] :
      ( r1_xboole_0(k1_relat_1(B_26),A_25)
      | k7_relat_1(B_26,A_25) != k1_xboole_0
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_7729,plain,(
    ! [A_25] :
      ( r1_xboole_0('#skF_4',A_25)
      | k7_relat_1('#skF_6',A_25) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7712,c_34])).

tff(c_8247,plain,(
    ! [A_856] :
      ( r1_xboole_0('#skF_4',A_856)
      | k7_relat_1('#skF_6',A_856) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6488,c_7729])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10433,plain,(
    ! [A_1027] :
      ( k3_xboole_0('#skF_4',A_1027) = k1_xboole_0
      | k7_relat_1('#skF_6',A_1027) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8247,c_2])).

tff(c_10445,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_9983,c_10433])).

tff(c_26,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6510,plain,(
    ! [A_715] :
      ( k9_relat_1(A_715,k1_relat_1(A_715)) = k2_relat_1(A_715)
      | ~ v1_relat_1(A_715) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6519,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_6510])).

tff(c_6523,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_26,c_6519])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_32,plain,(
    ! [B_26,A_25] :
      ( k7_relat_1(B_26,A_25) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_26),A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_7723,plain,(
    ! [A_25] :
      ( k7_relat_1('#skF_6',A_25) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_25)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7712,c_32])).

tff(c_8364,plain,(
    ! [A_866] :
      ( k7_relat_1('#skF_6',A_866) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_866) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6488,c_7723])).

tff(c_10309,plain,(
    ! [B_1017] :
      ( k7_relat_1('#skF_6',B_1017) = k1_xboole_0
      | k3_xboole_0('#skF_4',B_1017) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_8364])).

tff(c_30,plain,(
    ! [B_24,A_23] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_24,A_23)),A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_10324,plain,(
    ! [B_1017] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),B_1017)
      | ~ v1_relat_1('#skF_6')
      | k3_xboole_0('#skF_4',B_1017) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10309,c_30])).

tff(c_10340,plain,(
    ! [B_1017] :
      ( r1_tarski(k1_xboole_0,B_1017)
      | k3_xboole_0('#skF_4',B_1017) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6488,c_28,c_10324])).

tff(c_22,plain,(
    ! [A_15,C_19,B_18] :
      ( k9_relat_1(k7_relat_1(A_15,C_19),B_18) = k9_relat_1(A_15,B_18)
      | ~ r1_tarski(B_18,C_19)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_9987,plain,(
    ! [B_18] :
      ( k9_relat_1(k1_xboole_0,B_18) = k9_relat_1('#skF_6',B_18)
      | ~ r1_tarski(B_18,'#skF_3')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9983,c_22])).

tff(c_10892,plain,(
    ! [B_1057] :
      ( k9_relat_1(k1_xboole_0,B_1057) = k9_relat_1('#skF_6',B_1057)
      | ~ r1_tarski(B_1057,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6488,c_9987])).

tff(c_10900,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1('#skF_6',k1_xboole_0)
    | k3_xboole_0('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10340,c_10892])).

tff(c_10929,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10445,c_6523,c_10900])).

tff(c_10931,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10109,c_10929])).

tff(c_10932,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_8543])).

tff(c_36,plain,(
    ! [A_27,B_28] :
      ( r1_subset_1(A_27,B_28)
      | ~ r1_xboole_0(A_27,B_28)
      | v1_xboole_0(B_28)
      | v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_8261,plain,(
    ! [A_856] :
      ( r1_subset_1('#skF_4',A_856)
      | v1_xboole_0(A_856)
      | v1_xboole_0('#skF_4')
      | k7_relat_1('#skF_6',A_856) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8247,c_36])).

tff(c_8270,plain,(
    ! [A_856] :
      ( r1_subset_1('#skF_4',A_856)
      | v1_xboole_0(A_856)
      | k7_relat_1('#skF_6',A_856) != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_8261])).

tff(c_8192,plain,(
    ! [B_22] :
      ( k7_relat_1('#skF_5',B_22) = k1_xboole_0
      | ~ r1_xboole_0(B_22,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8184,c_24])).

tff(c_8443,plain,(
    ! [B_869] :
      ( k7_relat_1('#skF_5',B_869) = k1_xboole_0
      | ~ r1_xboole_0(B_869,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6487,c_8192])).

tff(c_8471,plain,(
    ! [A_27] :
      ( k7_relat_1('#skF_5',A_27) = k1_xboole_0
      | ~ r1_subset_1(A_27,'#skF_3')
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_27) ) ),
    inference(resolution,[status(thm)],[c_38,c_8443])).

tff(c_11031,plain,(
    ! [A_1061] :
      ( k7_relat_1('#skF_5',A_1061) = k1_xboole_0
      | ~ r1_subset_1(A_1061,'#skF_3')
      | v1_xboole_0(A_1061) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_8471])).

tff(c_11035,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | k7_relat_1('#skF_6','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8270,c_11031])).

tff(c_11038,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9983,c_11035])).

tff(c_11039,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_86,c_11038])).

tff(c_8201,plain,(
    ! [A_25] :
      ( r1_xboole_0('#skF_3',A_25)
      | k7_relat_1('#skF_5',A_25) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8184,c_34])).

tff(c_8414,plain,(
    ! [A_868] :
      ( r1_xboole_0('#skF_3',A_868)
      | k7_relat_1('#skF_5',A_868) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6487,c_8201])).

tff(c_11054,plain,(
    ! [A_1062] :
      ( k3_xboole_0('#skF_3',A_1062) = k1_xboole_0
      | k7_relat_1('#skF_5',A_1062) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8414,c_2])).

tff(c_11061,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_11039,c_11054])).

tff(c_6611,plain,(
    ! [A_727] :
      ( r1_xboole_0(k1_xboole_0,A_727)
      | k7_relat_1(k1_xboole_0,A_727) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_6607])).

tff(c_8494,plain,
    ( k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0
    | k7_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6611,c_8443])).

tff(c_8721,plain,(
    k7_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_8494])).

tff(c_8385,plain,(
    ! [A_867] :
      ( r1_xboole_0('#skF_3',A_867)
      | k9_relat_1('#skF_5',A_867) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6487,c_8189])).

tff(c_8408,plain,
    ( k7_relat_1(k1_xboole_0,'#skF_3') = k1_xboole_0
    | k9_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8385,c_6780])).

tff(c_9529,plain,(
    k9_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_8721,c_8408])).

tff(c_8772,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8716,c_8539])).

tff(c_8968,plain,(
    ! [A_916] :
      ( k3_xboole_0('#skF_4',A_916) = k1_xboole_0
      | k7_relat_1('#skF_6',A_916) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8247,c_2])).

tff(c_8972,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8772,c_8968])).

tff(c_7732,plain,(
    ! [A_13] :
      ( k9_relat_1('#skF_6',A_13) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_13)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7712,c_18])).

tff(c_8234,plain,(
    ! [A_855] :
      ( k9_relat_1('#skF_6',A_855) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_855) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6488,c_7732])).

tff(c_9167,plain,(
    ! [B_931] :
      ( k9_relat_1('#skF_6',B_931) = k1_xboole_0
      | k3_xboole_0('#skF_4',B_931) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_8234])).

tff(c_7739,plain,(
    ! [A_13] :
      ( r1_xboole_0('#skF_4',A_13)
      | k9_relat_1('#skF_6',A_13) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6488,c_7717])).

tff(c_8487,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | k9_relat_1('#skF_6','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7739,c_8443])).

tff(c_8873,plain,(
    k9_relat_1('#skF_6','#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_8487])).

tff(c_9176,plain,(
    k3_xboole_0('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_9167,c_8873])).

tff(c_9199,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8972,c_9176])).

tff(c_9200,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_8487])).

tff(c_8442,plain,(
    ! [A_868] :
      ( k3_xboole_0('#skF_3',A_868) = k1_xboole_0
      | k7_relat_1('#skF_5',A_868) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8414,c_2])).

tff(c_9221,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_9200,c_8442])).

tff(c_8195,plain,(
    ! [A_25] :
      ( k7_relat_1('#skF_5',A_25) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_25)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8184,c_32])).

tff(c_8285,plain,(
    ! [A_858] :
      ( k7_relat_1('#skF_5',A_858) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_858) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6487,c_8195])).

tff(c_9320,plain,(
    ! [B_947] :
      ( k7_relat_1('#skF_5',B_947) = k1_xboole_0
      | k3_xboole_0('#skF_3',B_947) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_8285])).

tff(c_9341,plain,(
    ! [B_947] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),B_947)
      | ~ v1_relat_1('#skF_5')
      | k3_xboole_0('#skF_3',B_947) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9320,c_30])).

tff(c_9361,plain,(
    ! [B_947] :
      ( r1_tarski(k1_xboole_0,B_947)
      | k3_xboole_0('#skF_3',B_947) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6487,c_28,c_9341])).

tff(c_9211,plain,(
    ! [B_18] :
      ( k9_relat_1(k1_xboole_0,B_18) = k9_relat_1('#skF_5',B_18)
      | ~ r1_tarski(B_18,'#skF_4')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9200,c_22])).

tff(c_9886,plain,(
    ! [B_982] :
      ( k9_relat_1(k1_xboole_0,B_982) = k9_relat_1('#skF_5',B_982)
      | ~ r1_tarski(B_982,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6487,c_9211])).

tff(c_9894,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1('#skF_5',k1_xboole_0)
    | k3_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9361,c_9886])).

tff(c_9923,plain,(
    k9_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9221,c_6523,c_9894])).

tff(c_9925,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9529,c_9923])).

tff(c_9926,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_8494])).

tff(c_8298,plain,(
    ! [A_859,B_860,C_861] :
      ( k9_subset_1(A_859,B_860,C_861) = k3_xboole_0(B_860,C_861)
      | ~ m1_subset_1(C_861,k1_zfmisc_1(A_859)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_8310,plain,(
    ! [B_860] : k9_subset_1('#skF_1',B_860,'#skF_4') = k3_xboole_0(B_860,'#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_8298])).

tff(c_11118,plain,(
    ! [C_1069,B_1064,E_1065,D_1066,A_1067,F_1068] :
      ( v1_funct_1(k1_tmap_1(A_1067,B_1064,C_1069,D_1066,E_1065,F_1068))
      | ~ m1_subset_1(F_1068,k1_zfmisc_1(k2_zfmisc_1(D_1066,B_1064)))
      | ~ v1_funct_2(F_1068,D_1066,B_1064)
      | ~ v1_funct_1(F_1068)
      | ~ m1_subset_1(E_1065,k1_zfmisc_1(k2_zfmisc_1(C_1069,B_1064)))
      | ~ v1_funct_2(E_1065,C_1069,B_1064)
      | ~ v1_funct_1(E_1065)
      | ~ m1_subset_1(D_1066,k1_zfmisc_1(A_1067))
      | v1_xboole_0(D_1066)
      | ~ m1_subset_1(C_1069,k1_zfmisc_1(A_1067))
      | v1_xboole_0(C_1069)
      | v1_xboole_0(B_1064)
      | v1_xboole_0(A_1067) ) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_11122,plain,(
    ! [A_1067,C_1069,E_1065] :
      ( v1_funct_1(k1_tmap_1(A_1067,'#skF_2',C_1069,'#skF_4',E_1065,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1065,k1_zfmisc_1(k2_zfmisc_1(C_1069,'#skF_2')))
      | ~ v1_funct_2(E_1065,C_1069,'#skF_2')
      | ~ v1_funct_1(E_1065)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1067))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1069,k1_zfmisc_1(A_1067))
      | v1_xboole_0(C_1069)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1067) ) ),
    inference(resolution,[status(thm)],[c_70,c_11118])).

tff(c_11129,plain,(
    ! [A_1067,C_1069,E_1065] :
      ( v1_funct_1(k1_tmap_1(A_1067,'#skF_2',C_1069,'#skF_4',E_1065,'#skF_6'))
      | ~ m1_subset_1(E_1065,k1_zfmisc_1(k2_zfmisc_1(C_1069,'#skF_2')))
      | ~ v1_funct_2(E_1065,C_1069,'#skF_2')
      | ~ v1_funct_1(E_1065)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1067))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1069,k1_zfmisc_1(A_1067))
      | v1_xboole_0(C_1069)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1067) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_11122])).

tff(c_12627,plain,(
    ! [A_1158,C_1159,E_1160] :
      ( v1_funct_1(k1_tmap_1(A_1158,'#skF_2',C_1159,'#skF_4',E_1160,'#skF_6'))
      | ~ m1_subset_1(E_1160,k1_zfmisc_1(k2_zfmisc_1(C_1159,'#skF_2')))
      | ~ v1_funct_2(E_1160,C_1159,'#skF_2')
      | ~ v1_funct_1(E_1160)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1158))
      | ~ m1_subset_1(C_1159,k1_zfmisc_1(A_1158))
      | v1_xboole_0(C_1159)
      | v1_xboole_0(A_1158) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_86,c_11129])).

tff(c_12632,plain,(
    ! [A_1158] :
      ( v1_funct_1(k1_tmap_1(A_1158,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1158))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1158))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1158) ) ),
    inference(resolution,[status(thm)],[c_76,c_12627])).

tff(c_12640,plain,(
    ! [A_1158] :
      ( v1_funct_1(k1_tmap_1(A_1158,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1158))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1158))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1158) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_12632])).

tff(c_13166,plain,(
    ! [A_1176] :
      ( v1_funct_1(k1_tmap_1(A_1176,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1176))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1176))
      | v1_xboole_0(A_1176) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_12640])).

tff(c_13169,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_88,c_13166])).

tff(c_13172,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_13169])).

tff(c_13173,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_13172])).

tff(c_8676,plain,(
    ! [A_879,B_880,C_881,D_882] :
      ( k2_partfun1(A_879,B_880,C_881,D_882) = k7_relat_1(C_881,D_882)
      | ~ m1_subset_1(C_881,k1_zfmisc_1(k2_zfmisc_1(A_879,B_880)))
      | ~ v1_funct_1(C_881) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_8678,plain,(
    ! [D_882] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_882) = k7_relat_1('#skF_5',D_882)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_76,c_8676])).

tff(c_8683,plain,(
    ! [D_882] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_882) = k7_relat_1('#skF_5',D_882) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_8678])).

tff(c_8680,plain,(
    ! [D_882] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_882) = k7_relat_1('#skF_6',D_882)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_70,c_8676])).

tff(c_8686,plain,(
    ! [D_882] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_882) = k7_relat_1('#skF_6',D_882) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_8680])).

tff(c_62,plain,(
    ! [F_177,D_175,A_172,C_174,E_176,B_173] :
      ( m1_subset_1(k1_tmap_1(A_172,B_173,C_174,D_175,E_176,F_177),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_172,C_174,D_175),B_173)))
      | ~ m1_subset_1(F_177,k1_zfmisc_1(k2_zfmisc_1(D_175,B_173)))
      | ~ v1_funct_2(F_177,D_175,B_173)
      | ~ v1_funct_1(F_177)
      | ~ m1_subset_1(E_176,k1_zfmisc_1(k2_zfmisc_1(C_174,B_173)))
      | ~ v1_funct_2(E_176,C_174,B_173)
      | ~ v1_funct_1(E_176)
      | ~ m1_subset_1(D_175,k1_zfmisc_1(A_172))
      | v1_xboole_0(D_175)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(A_172))
      | v1_xboole_0(C_174)
      | v1_xboole_0(B_173)
      | v1_xboole_0(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_11349,plain,(
    ! [F_1096,C_1094,A_1092,E_1093,B_1095,D_1091] :
      ( k2_partfun1(k4_subset_1(A_1092,C_1094,D_1091),B_1095,k1_tmap_1(A_1092,B_1095,C_1094,D_1091,E_1093,F_1096),D_1091) = F_1096
      | ~ m1_subset_1(k1_tmap_1(A_1092,B_1095,C_1094,D_1091,E_1093,F_1096),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1092,C_1094,D_1091),B_1095)))
      | ~ v1_funct_2(k1_tmap_1(A_1092,B_1095,C_1094,D_1091,E_1093,F_1096),k4_subset_1(A_1092,C_1094,D_1091),B_1095)
      | ~ v1_funct_1(k1_tmap_1(A_1092,B_1095,C_1094,D_1091,E_1093,F_1096))
      | k2_partfun1(D_1091,B_1095,F_1096,k9_subset_1(A_1092,C_1094,D_1091)) != k2_partfun1(C_1094,B_1095,E_1093,k9_subset_1(A_1092,C_1094,D_1091))
      | ~ m1_subset_1(F_1096,k1_zfmisc_1(k2_zfmisc_1(D_1091,B_1095)))
      | ~ v1_funct_2(F_1096,D_1091,B_1095)
      | ~ v1_funct_1(F_1096)
      | ~ m1_subset_1(E_1093,k1_zfmisc_1(k2_zfmisc_1(C_1094,B_1095)))
      | ~ v1_funct_2(E_1093,C_1094,B_1095)
      | ~ v1_funct_1(E_1093)
      | ~ m1_subset_1(D_1091,k1_zfmisc_1(A_1092))
      | v1_xboole_0(D_1091)
      | ~ m1_subset_1(C_1094,k1_zfmisc_1(A_1092))
      | v1_xboole_0(C_1094)
      | v1_xboole_0(B_1095)
      | v1_xboole_0(A_1092) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_19599,plain,(
    ! [C_1365,A_1363,D_1362,B_1360,F_1364,E_1361] :
      ( k2_partfun1(k4_subset_1(A_1363,C_1365,D_1362),B_1360,k1_tmap_1(A_1363,B_1360,C_1365,D_1362,E_1361,F_1364),D_1362) = F_1364
      | ~ v1_funct_2(k1_tmap_1(A_1363,B_1360,C_1365,D_1362,E_1361,F_1364),k4_subset_1(A_1363,C_1365,D_1362),B_1360)
      | ~ v1_funct_1(k1_tmap_1(A_1363,B_1360,C_1365,D_1362,E_1361,F_1364))
      | k2_partfun1(D_1362,B_1360,F_1364,k9_subset_1(A_1363,C_1365,D_1362)) != k2_partfun1(C_1365,B_1360,E_1361,k9_subset_1(A_1363,C_1365,D_1362))
      | ~ m1_subset_1(F_1364,k1_zfmisc_1(k2_zfmisc_1(D_1362,B_1360)))
      | ~ v1_funct_2(F_1364,D_1362,B_1360)
      | ~ v1_funct_1(F_1364)
      | ~ m1_subset_1(E_1361,k1_zfmisc_1(k2_zfmisc_1(C_1365,B_1360)))
      | ~ v1_funct_2(E_1361,C_1365,B_1360)
      | ~ v1_funct_1(E_1361)
      | ~ m1_subset_1(D_1362,k1_zfmisc_1(A_1363))
      | v1_xboole_0(D_1362)
      | ~ m1_subset_1(C_1365,k1_zfmisc_1(A_1363))
      | v1_xboole_0(C_1365)
      | v1_xboole_0(B_1360)
      | v1_xboole_0(A_1363) ) ),
    inference(resolution,[status(thm)],[c_62,c_11349])).

tff(c_25466,plain,(
    ! [E_1463,C_1467,A_1465,F_1466,D_1464,B_1462] :
      ( k2_partfun1(k4_subset_1(A_1465,C_1467,D_1464),B_1462,k1_tmap_1(A_1465,B_1462,C_1467,D_1464,E_1463,F_1466),D_1464) = F_1466
      | ~ v1_funct_1(k1_tmap_1(A_1465,B_1462,C_1467,D_1464,E_1463,F_1466))
      | k2_partfun1(D_1464,B_1462,F_1466,k9_subset_1(A_1465,C_1467,D_1464)) != k2_partfun1(C_1467,B_1462,E_1463,k9_subset_1(A_1465,C_1467,D_1464))
      | ~ m1_subset_1(F_1466,k1_zfmisc_1(k2_zfmisc_1(D_1464,B_1462)))
      | ~ v1_funct_2(F_1466,D_1464,B_1462)
      | ~ v1_funct_1(F_1466)
      | ~ m1_subset_1(E_1463,k1_zfmisc_1(k2_zfmisc_1(C_1467,B_1462)))
      | ~ v1_funct_2(E_1463,C_1467,B_1462)
      | ~ v1_funct_1(E_1463)
      | ~ m1_subset_1(D_1464,k1_zfmisc_1(A_1465))
      | v1_xboole_0(D_1464)
      | ~ m1_subset_1(C_1467,k1_zfmisc_1(A_1465))
      | v1_xboole_0(C_1467)
      | v1_xboole_0(B_1462)
      | v1_xboole_0(A_1465) ) ),
    inference(resolution,[status(thm)],[c_64,c_19599])).

tff(c_25472,plain,(
    ! [A_1465,C_1467,E_1463] :
      ( k2_partfun1(k4_subset_1(A_1465,C_1467,'#skF_4'),'#skF_2',k1_tmap_1(A_1465,'#skF_2',C_1467,'#skF_4',E_1463,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1465,'#skF_2',C_1467,'#skF_4',E_1463,'#skF_6'))
      | k2_partfun1(C_1467,'#skF_2',E_1463,k9_subset_1(A_1465,C_1467,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_1465,C_1467,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1463,k1_zfmisc_1(k2_zfmisc_1(C_1467,'#skF_2')))
      | ~ v1_funct_2(E_1463,C_1467,'#skF_2')
      | ~ v1_funct_1(E_1463)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1465))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1467,k1_zfmisc_1(A_1465))
      | v1_xboole_0(C_1467)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1465) ) ),
    inference(resolution,[status(thm)],[c_70,c_25466])).

tff(c_25480,plain,(
    ! [A_1465,C_1467,E_1463] :
      ( k2_partfun1(k4_subset_1(A_1465,C_1467,'#skF_4'),'#skF_2',k1_tmap_1(A_1465,'#skF_2',C_1467,'#skF_4',E_1463,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1465,'#skF_2',C_1467,'#skF_4',E_1463,'#skF_6'))
      | k2_partfun1(C_1467,'#skF_2',E_1463,k9_subset_1(A_1465,C_1467,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1465,C_1467,'#skF_4'))
      | ~ m1_subset_1(E_1463,k1_zfmisc_1(k2_zfmisc_1(C_1467,'#skF_2')))
      | ~ v1_funct_2(E_1463,C_1467,'#skF_2')
      | ~ v1_funct_1(E_1463)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1465))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1467,k1_zfmisc_1(A_1465))
      | v1_xboole_0(C_1467)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1465) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_8686,c_25472])).

tff(c_30258,plain,(
    ! [A_1531,C_1532,E_1533] :
      ( k2_partfun1(k4_subset_1(A_1531,C_1532,'#skF_4'),'#skF_2',k1_tmap_1(A_1531,'#skF_2',C_1532,'#skF_4',E_1533,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1531,'#skF_2',C_1532,'#skF_4',E_1533,'#skF_6'))
      | k2_partfun1(C_1532,'#skF_2',E_1533,k9_subset_1(A_1531,C_1532,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1531,C_1532,'#skF_4'))
      | ~ m1_subset_1(E_1533,k1_zfmisc_1(k2_zfmisc_1(C_1532,'#skF_2')))
      | ~ v1_funct_2(E_1533,C_1532,'#skF_2')
      | ~ v1_funct_1(E_1533)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1531))
      | ~ m1_subset_1(C_1532,k1_zfmisc_1(A_1531))
      | v1_xboole_0(C_1532)
      | v1_xboole_0(A_1531) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_86,c_25480])).

tff(c_30263,plain,(
    ! [A_1531] :
      ( k2_partfun1(k4_subset_1(A_1531,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1531,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1531,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1531,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1531,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1531))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1531))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1531) ) ),
    inference(resolution,[status(thm)],[c_76,c_30258])).

tff(c_30271,plain,(
    ! [A_1531] :
      ( k2_partfun1(k4_subset_1(A_1531,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1531,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1531,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1531,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1531,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1531))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1531))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1531) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_8683,c_30263])).

tff(c_30807,plain,(
    ! [A_1538] :
      ( k2_partfun1(k4_subset_1(A_1538,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1538,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1538,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1538,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1538,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1538))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1538))
      | v1_xboole_0(A_1538) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_30271])).

tff(c_191,plain,(
    ! [B_256,A_257] :
      ( r1_xboole_0(k1_relat_1(B_256),A_257)
      | k7_relat_1(B_256,A_257) != k1_xboole_0
      | ~ v1_relat_1(B_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_197,plain,(
    ! [A_257] :
      ( r1_xboole_0(k1_xboole_0,A_257)
      | k7_relat_1(k1_xboole_0,A_257) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_191])).

tff(c_200,plain,(
    ! [A_257] :
      ( r1_xboole_0(k1_xboole_0,A_257)
      | k7_relat_1(k1_xboole_0,A_257) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_197])).

tff(c_393,plain,(
    ! [B_275,A_276] :
      ( k9_relat_1(B_275,A_276) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_275),A_276)
      | ~ v1_relat_1(B_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_406,plain,(
    ! [A_276] :
      ( k9_relat_1(k1_xboole_0,A_276) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_276)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_393])).

tff(c_412,plain,(
    ! [A_277] :
      ( k9_relat_1(k1_xboole_0,A_277) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_277) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_406])).

tff(c_424,plain,(
    ! [A_257] :
      ( k9_relat_1(k1_xboole_0,A_257) = k1_xboole_0
      | k7_relat_1(k1_xboole_0,A_257) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_200,c_412])).

tff(c_124,plain,(
    ! [C_242,A_243,B_244] :
      ( v1_relat_1(C_242)
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1(A_243,B_244))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_132,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_124])).

tff(c_173,plain,(
    ! [C_250,A_251,B_252] :
      ( v4_relat_1(C_250,A_251)
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(A_251,B_252))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_181,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_173])).

tff(c_675,plain,(
    ! [B_290,A_291] :
      ( k1_relat_1(B_290) = A_291
      | ~ v1_partfun1(B_290,A_291)
      | ~ v4_relat_1(B_290,A_291)
      | ~ v1_relat_1(B_290) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_678,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_181,c_675])).

tff(c_684,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_678])).

tff(c_688,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_684])).

tff(c_1299,plain,(
    ! [C_344,A_345,B_346] :
      ( v1_partfun1(C_344,A_345)
      | ~ v1_funct_2(C_344,A_345,B_346)
      | ~ v1_funct_1(C_344)
      | ~ m1_subset_1(C_344,k1_zfmisc_1(k2_zfmisc_1(A_345,B_346)))
      | v1_xboole_0(B_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1305,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_1299])).

tff(c_1312,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_1305])).

tff(c_1314,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_688,c_1312])).

tff(c_1315,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_684])).

tff(c_1336,plain,(
    ! [A_25] :
      ( r1_xboole_0('#skF_4',A_25)
      | k7_relat_1('#skF_6',A_25) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1315,c_34])).

tff(c_2024,plain,(
    ! [A_393] :
      ( r1_xboole_0('#skF_4',A_393)
      | k7_relat_1('#skF_6',A_393) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_1336])).

tff(c_214,plain,(
    ! [A_261,B_262] :
      ( k7_relat_1(A_261,B_262) = k1_xboole_0
      | ~ r1_xboole_0(B_262,k1_relat_1(A_261))
      | ~ v1_relat_1(A_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_229,plain,(
    ! [B_262] :
      ( k7_relat_1(k1_xboole_0,B_262) = k1_xboole_0
      | ~ r1_xboole_0(B_262,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_214])).

tff(c_234,plain,(
    ! [B_262] :
      ( k7_relat_1(k1_xboole_0,B_262) = k1_xboole_0
      | ~ r1_xboole_0(B_262,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_229])).

tff(c_2056,plain,
    ( k7_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0
    | k7_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2024,c_234])).

tff(c_4224,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2056])).

tff(c_285,plain,(
    ! [B_269,A_270] :
      ( r1_xboole_0(k1_relat_1(B_269),A_270)
      | k9_relat_1(B_269,A_270) != k1_xboole_0
      | ~ v1_relat_1(B_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_302,plain,(
    ! [A_270] :
      ( r1_xboole_0(k1_xboole_0,A_270)
      | k9_relat_1(k1_xboole_0,A_270) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_285])).

tff(c_308,plain,(
    ! [A_270] :
      ( r1_xboole_0(k1_xboole_0,A_270)
      | k9_relat_1(k1_xboole_0,A_270) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_302])).

tff(c_1330,plain,(
    ! [B_22] :
      ( k7_relat_1('#skF_6',B_22) = k1_xboole_0
      | ~ r1_xboole_0(B_22,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1315,c_24])).

tff(c_1842,plain,(
    ! [B_383] :
      ( k7_relat_1('#skF_6',B_383) = k1_xboole_0
      | ~ r1_xboole_0(B_383,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_1330])).

tff(c_1870,plain,
    ( k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0
    | k9_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_308,c_1842])).

tff(c_4252,plain,(
    k9_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_4224,c_1870])).

tff(c_4260,plain,(
    k7_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_424,c_4252])).

tff(c_1327,plain,(
    ! [A_13] :
      ( r1_xboole_0('#skF_4',A_13)
      | k9_relat_1('#skF_6',A_13) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1315,c_20])).

tff(c_1884,plain,(
    ! [A_385] :
      ( r1_xboole_0('#skF_4',A_385)
      | k9_relat_1('#skF_6',A_385) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_1327])).

tff(c_1909,plain,
    ( k7_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0
    | k9_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1884,c_234])).

tff(c_4387,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_4260,c_1909])).

tff(c_621,plain,(
    ! [B_286,A_287] :
      ( k9_relat_1(B_286,A_287) = k1_xboole_0
      | k7_relat_1(B_286,A_287) != k1_xboole_0
      | ~ v1_relat_1(B_286) ) ),
    inference(resolution,[status(thm)],[c_34,c_393])).

tff(c_628,plain,(
    ! [A_287] :
      ( k9_relat_1('#skF_6',A_287) = k1_xboole_0
      | k7_relat_1('#skF_6',A_287) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_132,c_621])).

tff(c_1347,plain,(
    ! [A_13] :
      ( r1_xboole_0('#skF_4',A_13)
      | k9_relat_1('#skF_6',A_13) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_1327])).

tff(c_131,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_124])).

tff(c_180,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_173])).

tff(c_681,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_180,c_675])).

tff(c_687,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_681])).

tff(c_1358,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_687])).

tff(c_1733,plain,(
    ! [C_375,A_376,B_377] :
      ( v1_partfun1(C_375,A_376)
      | ~ v1_funct_2(C_375,A_376,B_377)
      | ~ v1_funct_1(C_375)
      | ~ m1_subset_1(C_375,k1_zfmisc_1(k2_zfmisc_1(A_376,B_377)))
      | v1_xboole_0(B_377) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1736,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_1733])).

tff(c_1742,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_1736])).

tff(c_1744,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1358,c_1742])).

tff(c_1745,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_687])).

tff(c_1760,plain,(
    ! [B_22] :
      ( k7_relat_1('#skF_5',B_22) = k1_xboole_0
      | ~ r1_xboole_0(B_22,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1745,c_24])).

tff(c_2059,plain,(
    ! [B_394] :
      ( k7_relat_1('#skF_5',B_394) = k1_xboole_0
      | ~ r1_xboole_0(B_394,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_1760])).

tff(c_2100,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | k9_relat_1('#skF_6','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1347,c_2059])).

tff(c_2175,plain,(
    k9_relat_1('#skF_6','#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2100])).

tff(c_2179,plain,(
    k7_relat_1('#skF_6','#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_628,c_2175])).

tff(c_1754,plain,(
    ! [A_25] :
      ( k7_relat_1('#skF_5',A_25) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_25)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1745,c_32])).

tff(c_2154,plain,(
    ! [A_397] :
      ( k7_relat_1('#skF_5',A_397) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_397) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_1754])).

tff(c_2164,plain,(
    ! [B_28] :
      ( k7_relat_1('#skF_5',B_28) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_28)
      | v1_xboole_0(B_28)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_2154])).

tff(c_2273,plain,(
    ! [B_410] :
      ( k7_relat_1('#skF_5',B_410) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_410)
      | v1_xboole_0(B_410) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_2164])).

tff(c_2276,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_2273])).

tff(c_2279,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_2276])).

tff(c_1766,plain,(
    ! [A_25] :
      ( r1_xboole_0('#skF_3',A_25)
      | k7_relat_1('#skF_5',A_25) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1745,c_34])).

tff(c_2118,plain,(
    ! [A_396] :
      ( r1_xboole_0('#skF_3',A_396)
      | k7_relat_1('#skF_5',A_396) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_1766])).

tff(c_2132,plain,(
    ! [A_396] :
      ( r1_subset_1('#skF_3',A_396)
      | v1_xboole_0(A_396)
      | v1_xboole_0('#skF_3')
      | k7_relat_1('#skF_5',A_396) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2118,c_36])).

tff(c_2150,plain,(
    ! [A_396] :
      ( r1_subset_1('#skF_3',A_396)
      | v1_xboole_0(A_396)
      | k7_relat_1('#skF_5',A_396) != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_2132])).

tff(c_1846,plain,(
    ! [A_27] :
      ( k7_relat_1('#skF_6',A_27) = k1_xboole_0
      | ~ r1_subset_1(A_27,'#skF_4')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_27) ) ),
    inference(resolution,[status(thm)],[c_38,c_1842])).

tff(c_2458,plain,(
    ! [A_430] :
      ( k7_relat_1('#skF_6',A_430) = k1_xboole_0
      | ~ r1_subset_1(A_430,'#skF_4')
      | v1_xboole_0(A_430) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1846])).

tff(c_2462,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_4')
    | k7_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2150,c_2458])).

tff(c_2468,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2279,c_2462])).

tff(c_2470,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_90,c_2179,c_2468])).

tff(c_2471,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2100])).

tff(c_4122,plain,(
    ! [A_561] :
      ( k3_xboole_0('#skF_3',A_561) = k1_xboole_0
      | k7_relat_1('#skF_5',A_561) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2118,c_2])).

tff(c_4134,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2471,c_4122])).

tff(c_155,plain,(
    ! [A_249] :
      ( k9_relat_1(A_249,k1_relat_1(A_249)) = k2_relat_1(A_249)
      | ~ v1_relat_1(A_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_164,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_155])).

tff(c_168,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_26,c_164])).

tff(c_4457,plain,(
    ! [A_590] :
      ( k7_relat_1('#skF_6',A_590) = k1_xboole_0
      | k3_xboole_0(A_590,'#skF_4') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_1842])).

tff(c_4481,plain,(
    ! [A_590] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),A_590)
      | ~ v1_relat_1('#skF_6')
      | k3_xboole_0(A_590,'#skF_4') != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4457,c_30])).

tff(c_4502,plain,(
    ! [A_590] :
      ( r1_tarski(k1_xboole_0,A_590)
      | k3_xboole_0(A_590,'#skF_4') != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_28,c_4481])).

tff(c_1349,plain,(
    ! [B_22] :
      ( k7_relat_1('#skF_6',B_22) = k1_xboole_0
      | ~ r1_xboole_0(B_22,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_1330])).

tff(c_2147,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | k7_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2118,c_1349])).

tff(c_4082,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2471,c_2147])).

tff(c_4086,plain,(
    ! [B_18] :
      ( k9_relat_1(k1_xboole_0,B_18) = k9_relat_1('#skF_6',B_18)
      | ~ r1_tarski(B_18,'#skF_3')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4082,c_22])).

tff(c_4754,plain,(
    ! [B_614] :
      ( k9_relat_1(k1_xboole_0,B_614) = k9_relat_1('#skF_6',B_614)
      | ~ r1_tarski(B_614,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_4086])).

tff(c_4758,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1('#skF_6',k1_xboole_0)
    | k3_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4502,c_4754])).

tff(c_4788,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4134,c_168,c_4758])).

tff(c_4790,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4387,c_4788])).

tff(c_4792,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2056])).

tff(c_2104,plain,
    ( k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0
    | k9_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_308,c_2059])).

tff(c_2499,plain,(
    k9_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2104])).

tff(c_2507,plain,(
    k7_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_424,c_2499])).

tff(c_1757,plain,(
    ! [A_13] :
      ( r1_xboole_0('#skF_3',A_13)
      | k9_relat_1('#skF_5',A_13) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1745,c_20])).

tff(c_1942,plain,(
    ! [A_388] :
      ( r1_xboole_0('#skF_3',A_388)
      | k9_relat_1('#skF_5',A_388) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_1757])).

tff(c_1969,plain,
    ( k7_relat_1(k1_xboole_0,'#skF_3') = k1_xboole_0
    | k9_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1942,c_234])).

tff(c_3495,plain,(
    k9_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_2507,c_1969])).

tff(c_2631,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2471,c_2147])).

tff(c_3303,plain,(
    ! [A_499] :
      ( k3_xboole_0('#skF_4',A_499) = k1_xboole_0
      | k7_relat_1('#skF_6',A_499) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2024,c_2])).

tff(c_3311,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2631,c_3303])).

tff(c_3325,plain,(
    ! [A_506] :
      ( k7_relat_1('#skF_5',A_506) = k1_xboole_0
      | k3_xboole_0(A_506,'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_2059])).

tff(c_3349,plain,(
    ! [A_506] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),A_506)
      | ~ v1_relat_1('#skF_5')
      | k3_xboole_0(A_506,'#skF_3') != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3325,c_30])).

tff(c_3370,plain,(
    ! [A_506] :
      ( r1_tarski(k1_xboole_0,A_506)
      | k3_xboole_0(A_506,'#skF_3') != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_28,c_3349])).

tff(c_2476,plain,(
    ! [B_18] :
      ( k9_relat_1(k1_xboole_0,B_18) = k9_relat_1('#skF_5',B_18)
      | ~ r1_tarski(B_18,'#skF_4')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2471,c_22])).

tff(c_3793,plain,(
    ! [B_542] :
      ( k9_relat_1(k1_xboole_0,B_542) = k9_relat_1('#skF_5',B_542)
      | ~ r1_tarski(B_542,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_2476])).

tff(c_3805,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1('#skF_5',k1_xboole_0)
    | k3_xboole_0('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3370,c_3793])).

tff(c_3833,plain,(
    k9_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3311,c_168,c_3805])).

tff(c_3835,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3495,c_3833])).

tff(c_3836,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2104])).

tff(c_3921,plain,(
    ! [A_544,B_545,C_546,D_547] :
      ( k2_partfun1(A_544,B_545,C_546,D_547) = k7_relat_1(C_546,D_547)
      | ~ m1_subset_1(C_546,k1_zfmisc_1(k2_zfmisc_1(A_544,B_545)))
      | ~ v1_funct_1(C_546) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_3923,plain,(
    ! [D_547] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_547) = k7_relat_1('#skF_5',D_547)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_76,c_3921])).

tff(c_3928,plain,(
    ! [D_547] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_547) = k7_relat_1('#skF_5',D_547) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_3923])).

tff(c_3925,plain,(
    ! [D_547] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_547) = k7_relat_1('#skF_6',D_547)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_70,c_3921])).

tff(c_3931,plain,(
    ! [D_547] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_547) = k7_relat_1('#skF_6',D_547) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3925])).

tff(c_1810,plain,(
    ! [A_378,B_379,C_380] :
      ( k9_subset_1(A_378,B_379,C_380) = k3_xboole_0(B_379,C_380)
      | ~ m1_subset_1(C_380,k1_zfmisc_1(A_378)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1822,plain,(
    ! [B_379] : k9_subset_1('#skF_1',B_379,'#skF_4') = k3_xboole_0(B_379,'#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_1810])).

tff(c_68,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_117,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_1832,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1822,c_1822,c_117])).

tff(c_6471,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4792,c_3836,c_3928,c_3931,c_4134,c_4134,c_1832])).

tff(c_6472,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_6597,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_6472])).

tff(c_30818,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_30807,c_6597])).

tff(c_30832,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_84,c_10932,c_11061,c_9926,c_11061,c_8310,c_8310,c_13173,c_30818])).

tff(c_30834,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_30832])).

tff(c_30835,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_6472])).

tff(c_30837,plain,(
    ! [B_1539,A_1540] :
      ( r1_xboole_0(k1_relat_1(B_1539),A_1540)
      | k7_relat_1(B_1539,A_1540) != k1_xboole_0
      | ~ v1_relat_1(B_1539) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_30846,plain,(
    ! [A_1540] :
      ( r1_xboole_0(k1_xboole_0,A_1540)
      | k7_relat_1(k1_xboole_0,A_1540) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_30837])).

tff(c_30850,plain,(
    ! [A_1540] :
      ( r1_xboole_0(k1_xboole_0,A_1540)
      | k7_relat_1(k1_xboole_0,A_1540) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_30846])).

tff(c_31315,plain,(
    ! [B_1576,A_1577] :
      ( k1_relat_1(B_1576) = A_1577
      | ~ v1_partfun1(B_1576,A_1577)
      | ~ v4_relat_1(B_1576,A_1577)
      | ~ v1_relat_1(B_1576) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_31318,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_6541,c_31315])).

tff(c_31324,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6488,c_31318])).

tff(c_31328,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_31324])).

tff(c_31770,plain,(
    ! [C_1614,A_1615,B_1616] :
      ( v1_partfun1(C_1614,A_1615)
      | ~ v1_funct_2(C_1614,A_1615,B_1616)
      | ~ v1_funct_1(C_1614)
      | ~ m1_subset_1(C_1614,k1_zfmisc_1(k2_zfmisc_1(A_1615,B_1616)))
      | v1_xboole_0(B_1616) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_31776,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_31770])).

tff(c_31783,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_31776])).

tff(c_31785,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_31328,c_31783])).

tff(c_31786,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_31324])).

tff(c_31797,plain,(
    ! [B_22] :
      ( k7_relat_1('#skF_6',B_22) = k1_xboole_0
      | ~ r1_xboole_0(B_22,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31786,c_24])).

tff(c_32235,plain,(
    ! [B_1643] :
      ( k7_relat_1('#skF_6',B_1643) = k1_xboole_0
      | ~ r1_xboole_0(B_1643,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6488,c_31797])).

tff(c_32281,plain,
    ( k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0
    | k7_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30850,c_32235])).

tff(c_33732,plain,(
    k7_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32281])).

tff(c_31794,plain,(
    ! [A_13] :
      ( r1_xboole_0('#skF_4',A_13)
      | k9_relat_1('#skF_6',A_13) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31786,c_20])).

tff(c_32284,plain,(
    ! [A_1644] :
      ( r1_xboole_0('#skF_4',A_1644)
      | k9_relat_1('#skF_6',A_1644) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6488,c_31794])).

tff(c_30973,plain,(
    ! [A_1551,B_1552] :
      ( k7_relat_1(A_1551,B_1552) = k1_xboole_0
      | ~ r1_xboole_0(B_1552,k1_relat_1(A_1551))
      | ~ v1_relat_1(A_1551) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_30992,plain,(
    ! [B_1552] :
      ( k7_relat_1(k1_xboole_0,B_1552) = k1_xboole_0
      | ~ r1_xboole_0(B_1552,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_30973])).

tff(c_30998,plain,(
    ! [B_1552] :
      ( k7_relat_1(k1_xboole_0,B_1552) = k1_xboole_0
      | ~ r1_xboole_0(B_1552,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_30992])).

tff(c_32313,plain,
    ( k7_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0
    | k9_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32284,c_30998])).

tff(c_33826,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_33732,c_32313])).

tff(c_31321,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_6540,c_31315])).

tff(c_31327,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6487,c_31321])).

tff(c_31842,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_31327])).

tff(c_32055,plain,(
    ! [C_1633,A_1634,B_1635] :
      ( v1_partfun1(C_1633,A_1634)
      | ~ v1_funct_2(C_1633,A_1634,B_1635)
      | ~ v1_funct_1(C_1633)
      | ~ m1_subset_1(C_1633,k1_zfmisc_1(k2_zfmisc_1(A_1634,B_1635)))
      | v1_xboole_0(B_1635) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_32058,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_32055])).

tff(c_32064,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_32058])).

tff(c_32066,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_31842,c_32064])).

tff(c_32067,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_31327])).

tff(c_32087,plain,(
    ! [A_13] :
      ( k9_relat_1('#skF_5',A_13) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_13)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32067,c_18])).

tff(c_32338,plain,(
    ! [A_1647] :
      ( k9_relat_1('#skF_5',A_1647) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_1647) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6487,c_32087])).

tff(c_32348,plain,(
    ! [B_28] :
      ( k9_relat_1('#skF_5',B_28) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_28)
      | v1_xboole_0(B_28)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_32338])).

tff(c_33741,plain,(
    ! [B_1770] :
      ( k9_relat_1('#skF_5',B_1770) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_1770)
      | v1_xboole_0(B_1770) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_32348])).

tff(c_33744,plain,
    ( k9_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_33741])).

tff(c_33747,plain,(
    k9_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_33744])).

tff(c_32075,plain,(
    ! [A_13] :
      ( r1_xboole_0('#skF_3',A_13)
      | k9_relat_1('#skF_5',A_13) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32067,c_20])).

tff(c_32162,plain,(
    ! [A_1638] :
      ( r1_xboole_0('#skF_3',A_1638)
      | k9_relat_1('#skF_5',A_1638) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6487,c_32075])).

tff(c_33959,plain,(
    ! [A_1789] :
      ( k3_xboole_0('#skF_3',A_1789) = k1_xboole_0
      | k9_relat_1('#skF_5',A_1789) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32162,c_2])).

tff(c_33976,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_33747,c_33959])).

tff(c_34003,plain,(
    ! [A_1791] :
      ( k7_relat_1('#skF_6',A_1791) = k1_xboole_0
      | k3_xboole_0(A_1791,'#skF_4') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_32235])).

tff(c_34024,plain,(
    ! [A_1791] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),A_1791)
      | ~ v1_relat_1('#skF_6')
      | k3_xboole_0(A_1791,'#skF_4') != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34003,c_30])).

tff(c_34044,plain,(
    ! [A_1791] :
      ( r1_tarski(k1_xboole_0,A_1791)
      | k3_xboole_0(A_1791,'#skF_4') != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6488,c_28,c_34024])).

tff(c_31803,plain,(
    ! [A_25] :
      ( r1_xboole_0('#skF_4',A_25)
      | k7_relat_1('#skF_6',A_25) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31786,c_34])).

tff(c_31821,plain,(
    ! [A_25] :
      ( r1_xboole_0('#skF_4',A_25)
      | k7_relat_1('#skF_6',A_25) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6488,c_31803])).

tff(c_32078,plain,(
    ! [B_22] :
      ( k7_relat_1('#skF_5',B_22) = k1_xboole_0
      | ~ r1_xboole_0(B_22,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32067,c_24])).

tff(c_32380,plain,(
    ! [B_1649] :
      ( k7_relat_1('#skF_5',B_1649) = k1_xboole_0
      | ~ r1_xboole_0(B_1649,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6487,c_32078])).

tff(c_32424,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | k7_relat_1('#skF_6','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_31821,c_32380])).

tff(c_33618,plain,(
    k7_relat_1('#skF_6','#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32424])).

tff(c_32259,plain,(
    ! [A_27] :
      ( k7_relat_1('#skF_6',A_27) = k1_xboole_0
      | ~ r1_subset_1(A_27,'#skF_4')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_27) ) ),
    inference(resolution,[status(thm)],[c_38,c_32235])).

tff(c_33619,plain,(
    ! [A_1761] :
      ( k7_relat_1('#skF_6',A_1761) = k1_xboole_0
      | ~ r1_subset_1(A_1761,'#skF_4')
      | v1_xboole_0(A_1761) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_32259])).

tff(c_33630,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_33619])).

tff(c_33639,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_33618,c_33630])).

tff(c_33641,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32424])).

tff(c_33659,plain,(
    ! [B_18] :
      ( k9_relat_1(k1_xboole_0,B_18) = k9_relat_1('#skF_6',B_18)
      | ~ r1_tarski(B_18,'#skF_3')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33641,c_22])).

tff(c_34464,plain,(
    ! [B_1815] :
      ( k9_relat_1(k1_xboole_0,B_1815) = k9_relat_1('#skF_6',B_1815)
      | ~ r1_tarski(B_1815,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6488,c_33659])).

tff(c_34468,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1('#skF_6',k1_xboole_0)
    | k3_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34044,c_34464])).

tff(c_34498,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_33976,c_6523,c_34468])).

tff(c_34500,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33826,c_34498])).

tff(c_34501,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32281])).

tff(c_33640,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32424])).

tff(c_32084,plain,(
    ! [A_25] :
      ( r1_xboole_0('#skF_3',A_25)
      | k7_relat_1('#skF_5',A_25) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32067,c_34])).

tff(c_32120,plain,(
    ! [A_1636] :
      ( r1_xboole_0('#skF_3',A_1636)
      | k7_relat_1('#skF_5',A_1636) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6487,c_32084])).

tff(c_34708,plain,(
    ! [A_1835] :
      ( k3_xboole_0('#skF_3',A_1835) = k1_xboole_0
      | k7_relat_1('#skF_5',A_1835) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32120,c_2])).

tff(c_34719,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_33640,c_34708])).

tff(c_31212,plain,(
    ! [A_1565,B_1566,C_1567] :
      ( k9_subset_1(A_1565,B_1566,C_1567) = k3_xboole_0(B_1566,C_1567)
      | ~ m1_subset_1(C_1567,k1_zfmisc_1(A_1565)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_31224,plain,(
    ! [B_1566] : k9_subset_1('#skF_1',B_1566,'#skF_4') = k3_xboole_0(B_1566,'#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_31212])).

tff(c_30851,plain,(
    ! [A_1541] :
      ( r1_xboole_0(k1_xboole_0,A_1541)
      | k7_relat_1(k1_xboole_0,A_1541) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_30846])).

tff(c_30858,plain,(
    ! [A_1541] :
      ( k9_relat_1(k1_xboole_0,A_1541) = k1_xboole_0
      | k7_relat_1(k1_xboole_0,A_1541) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30851,c_6561])).

tff(c_31049,plain,(
    ! [B_1557,A_1558] :
      ( r1_xboole_0(k1_relat_1(B_1557),A_1558)
      | k9_relat_1(B_1557,A_1558) != k1_xboole_0
      | ~ v1_relat_1(B_1557) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_31069,plain,(
    ! [A_1558] :
      ( r1_xboole_0(k1_xboole_0,A_1558)
      | k9_relat_1(k1_xboole_0,A_1558) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_31049])).

tff(c_31076,plain,(
    ! [A_1558] :
      ( r1_xboole_0(k1_xboole_0,A_1558)
      | k9_relat_1(k1_xboole_0,A_1558) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_31069])).

tff(c_32426,plain,
    ( k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0
    | k9_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_31076,c_32380])).

tff(c_32500,plain,(
    k9_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32426])).

tff(c_32507,plain,(
    k7_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_30858,c_32500])).

tff(c_32180,plain,
    ( k7_relat_1(k1_xboole_0,'#skF_3') = k1_xboole_0
    | k9_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32162,c_30998])).

tff(c_33169,plain,(
    k9_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_32507,c_32180])).

tff(c_32571,plain,(
    k7_relat_1('#skF_6','#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32424])).

tff(c_32700,plain,(
    ! [A_1687] :
      ( k7_relat_1('#skF_6',A_1687) = k1_xboole_0
      | ~ r1_subset_1(A_1687,'#skF_4')
      | v1_xboole_0(A_1687) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_32259])).

tff(c_32715,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_32700])).

tff(c_32727,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_32571,c_32715])).

tff(c_32729,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32424])).

tff(c_32141,plain,(
    ! [A_1637] :
      ( r1_xboole_0('#skF_4',A_1637)
      | k7_relat_1('#skF_6',A_1637) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6488,c_31803])).

tff(c_32933,plain,(
    ! [A_1705] :
      ( k3_xboole_0('#skF_4',A_1705) = k1_xboole_0
      | k7_relat_1('#skF_6',A_1705) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32141,c_2])).

tff(c_32937,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_32729,c_32933])).

tff(c_32968,plain,(
    ! [A_1713] :
      ( k7_relat_1('#skF_5',A_1713) = k1_xboole_0
      | k3_xboole_0(A_1713,'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_32380])).

tff(c_32989,plain,(
    ! [A_1713] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),A_1713)
      | ~ v1_relat_1('#skF_5')
      | k3_xboole_0(A_1713,'#skF_3') != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32968,c_30])).

tff(c_33009,plain,(
    ! [A_1713] :
      ( r1_tarski(k1_xboole_0,A_1713)
      | k3_xboole_0(A_1713,'#skF_3') != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6487,c_28,c_32989])).

tff(c_32728,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32424])).

tff(c_32733,plain,(
    ! [B_18] :
      ( k9_relat_1(k1_xboole_0,B_18) = k9_relat_1('#skF_5',B_18)
      | ~ r1_tarski(B_18,'#skF_4')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32728,c_22])).

tff(c_33393,plain,(
    ! [B_1744] :
      ( k9_relat_1(k1_xboole_0,B_1744) = k9_relat_1('#skF_5',B_1744)
      | ~ r1_tarski(B_1744,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6487,c_32733])).

tff(c_33405,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1('#skF_5',k1_xboole_0)
    | k3_xboole_0('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_33009,c_33393])).

tff(c_33433,plain,(
    k9_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32937,c_6523,c_33405])).

tff(c_33435,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33169,c_33433])).

tff(c_33436,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32426])).

tff(c_32434,plain,(
    ! [A_1650,B_1651,C_1652,D_1653] :
      ( k2_partfun1(A_1650,B_1651,C_1652,D_1653) = k7_relat_1(C_1652,D_1653)
      | ~ m1_subset_1(C_1652,k1_zfmisc_1(k2_zfmisc_1(A_1650,B_1651)))
      | ~ v1_funct_1(C_1652) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_32436,plain,(
    ! [D_1653] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_1653) = k7_relat_1('#skF_5',D_1653)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_76,c_32434])).

tff(c_32441,plain,(
    ! [D_1653] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_1653) = k7_relat_1('#skF_5',D_1653) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_32436])).

tff(c_32438,plain,(
    ! [D_1653] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_1653) = k7_relat_1('#skF_6',D_1653)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_70,c_32434])).

tff(c_32444,plain,(
    ! [D_1653] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_1653) = k7_relat_1('#skF_6',D_1653) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_32438])).

tff(c_33515,plain,(
    ! [F_1749,E_1746,A_1748,B_1745,D_1747,C_1750] :
      ( v1_funct_1(k1_tmap_1(A_1748,B_1745,C_1750,D_1747,E_1746,F_1749))
      | ~ m1_subset_1(F_1749,k1_zfmisc_1(k2_zfmisc_1(D_1747,B_1745)))
      | ~ v1_funct_2(F_1749,D_1747,B_1745)
      | ~ v1_funct_1(F_1749)
      | ~ m1_subset_1(E_1746,k1_zfmisc_1(k2_zfmisc_1(C_1750,B_1745)))
      | ~ v1_funct_2(E_1746,C_1750,B_1745)
      | ~ v1_funct_1(E_1746)
      | ~ m1_subset_1(D_1747,k1_zfmisc_1(A_1748))
      | v1_xboole_0(D_1747)
      | ~ m1_subset_1(C_1750,k1_zfmisc_1(A_1748))
      | v1_xboole_0(C_1750)
      | v1_xboole_0(B_1745)
      | v1_xboole_0(A_1748) ) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_33519,plain,(
    ! [A_1748,C_1750,E_1746] :
      ( v1_funct_1(k1_tmap_1(A_1748,'#skF_2',C_1750,'#skF_4',E_1746,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1746,k1_zfmisc_1(k2_zfmisc_1(C_1750,'#skF_2')))
      | ~ v1_funct_2(E_1746,C_1750,'#skF_2')
      | ~ v1_funct_1(E_1746)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1748))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1750,k1_zfmisc_1(A_1748))
      | v1_xboole_0(C_1750)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1748) ) ),
    inference(resolution,[status(thm)],[c_70,c_33515])).

tff(c_33526,plain,(
    ! [A_1748,C_1750,E_1746] :
      ( v1_funct_1(k1_tmap_1(A_1748,'#skF_2',C_1750,'#skF_4',E_1746,'#skF_6'))
      | ~ m1_subset_1(E_1746,k1_zfmisc_1(k2_zfmisc_1(C_1750,'#skF_2')))
      | ~ v1_funct_2(E_1746,C_1750,'#skF_2')
      | ~ v1_funct_1(E_1746)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1748))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1750,k1_zfmisc_1(A_1748))
      | v1_xboole_0(C_1750)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1748) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_33519])).

tff(c_35845,plain,(
    ! [A_1882,C_1883,E_1884] :
      ( v1_funct_1(k1_tmap_1(A_1882,'#skF_2',C_1883,'#skF_4',E_1884,'#skF_6'))
      | ~ m1_subset_1(E_1884,k1_zfmisc_1(k2_zfmisc_1(C_1883,'#skF_2')))
      | ~ v1_funct_2(E_1884,C_1883,'#skF_2')
      | ~ v1_funct_1(E_1884)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1882))
      | ~ m1_subset_1(C_1883,k1_zfmisc_1(A_1882))
      | v1_xboole_0(C_1883)
      | v1_xboole_0(A_1882) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_86,c_33526])).

tff(c_35850,plain,(
    ! [A_1882] :
      ( v1_funct_1(k1_tmap_1(A_1882,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1882))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1882))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1882) ) ),
    inference(resolution,[status(thm)],[c_76,c_35845])).

tff(c_35858,plain,(
    ! [A_1882] :
      ( v1_funct_1(k1_tmap_1(A_1882,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1882))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1882))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1882) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_35850])).

tff(c_36460,plain,(
    ! [A_1903] :
      ( v1_funct_1(k1_tmap_1(A_1903,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1903))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1903))
      | v1_xboole_0(A_1903) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_35858])).

tff(c_36463,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_88,c_36460])).

tff(c_36466,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_36463])).

tff(c_36467,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_36466])).

tff(c_34566,plain,(
    ! [B_1820,E_1818,D_1816,C_1819,F_1821,A_1817] :
      ( k2_partfun1(k4_subset_1(A_1817,C_1819,D_1816),B_1820,k1_tmap_1(A_1817,B_1820,C_1819,D_1816,E_1818,F_1821),C_1819) = E_1818
      | ~ m1_subset_1(k1_tmap_1(A_1817,B_1820,C_1819,D_1816,E_1818,F_1821),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1817,C_1819,D_1816),B_1820)))
      | ~ v1_funct_2(k1_tmap_1(A_1817,B_1820,C_1819,D_1816,E_1818,F_1821),k4_subset_1(A_1817,C_1819,D_1816),B_1820)
      | ~ v1_funct_1(k1_tmap_1(A_1817,B_1820,C_1819,D_1816,E_1818,F_1821))
      | k2_partfun1(D_1816,B_1820,F_1821,k9_subset_1(A_1817,C_1819,D_1816)) != k2_partfun1(C_1819,B_1820,E_1818,k9_subset_1(A_1817,C_1819,D_1816))
      | ~ m1_subset_1(F_1821,k1_zfmisc_1(k2_zfmisc_1(D_1816,B_1820)))
      | ~ v1_funct_2(F_1821,D_1816,B_1820)
      | ~ v1_funct_1(F_1821)
      | ~ m1_subset_1(E_1818,k1_zfmisc_1(k2_zfmisc_1(C_1819,B_1820)))
      | ~ v1_funct_2(E_1818,C_1819,B_1820)
      | ~ v1_funct_1(E_1818)
      | ~ m1_subset_1(D_1816,k1_zfmisc_1(A_1817))
      | v1_xboole_0(D_1816)
      | ~ m1_subset_1(C_1819,k1_zfmisc_1(A_1817))
      | v1_xboole_0(C_1819)
      | v1_xboole_0(B_1820)
      | v1_xboole_0(A_1817) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_42141,plain,(
    ! [D_2075,B_2073,E_2074,A_2076,C_2078,F_2077] :
      ( k2_partfun1(k4_subset_1(A_2076,C_2078,D_2075),B_2073,k1_tmap_1(A_2076,B_2073,C_2078,D_2075,E_2074,F_2077),C_2078) = E_2074
      | ~ v1_funct_2(k1_tmap_1(A_2076,B_2073,C_2078,D_2075,E_2074,F_2077),k4_subset_1(A_2076,C_2078,D_2075),B_2073)
      | ~ v1_funct_1(k1_tmap_1(A_2076,B_2073,C_2078,D_2075,E_2074,F_2077))
      | k2_partfun1(D_2075,B_2073,F_2077,k9_subset_1(A_2076,C_2078,D_2075)) != k2_partfun1(C_2078,B_2073,E_2074,k9_subset_1(A_2076,C_2078,D_2075))
      | ~ m1_subset_1(F_2077,k1_zfmisc_1(k2_zfmisc_1(D_2075,B_2073)))
      | ~ v1_funct_2(F_2077,D_2075,B_2073)
      | ~ v1_funct_1(F_2077)
      | ~ m1_subset_1(E_2074,k1_zfmisc_1(k2_zfmisc_1(C_2078,B_2073)))
      | ~ v1_funct_2(E_2074,C_2078,B_2073)
      | ~ v1_funct_1(E_2074)
      | ~ m1_subset_1(D_2075,k1_zfmisc_1(A_2076))
      | v1_xboole_0(D_2075)
      | ~ m1_subset_1(C_2078,k1_zfmisc_1(A_2076))
      | v1_xboole_0(C_2078)
      | v1_xboole_0(B_2073)
      | v1_xboole_0(A_2076) ) ),
    inference(resolution,[status(thm)],[c_62,c_34566])).

tff(c_48401,plain,(
    ! [D_2194,B_2192,E_2193,F_2196,A_2195,C_2197] :
      ( k2_partfun1(k4_subset_1(A_2195,C_2197,D_2194),B_2192,k1_tmap_1(A_2195,B_2192,C_2197,D_2194,E_2193,F_2196),C_2197) = E_2193
      | ~ v1_funct_1(k1_tmap_1(A_2195,B_2192,C_2197,D_2194,E_2193,F_2196))
      | k2_partfun1(D_2194,B_2192,F_2196,k9_subset_1(A_2195,C_2197,D_2194)) != k2_partfun1(C_2197,B_2192,E_2193,k9_subset_1(A_2195,C_2197,D_2194))
      | ~ m1_subset_1(F_2196,k1_zfmisc_1(k2_zfmisc_1(D_2194,B_2192)))
      | ~ v1_funct_2(F_2196,D_2194,B_2192)
      | ~ v1_funct_1(F_2196)
      | ~ m1_subset_1(E_2193,k1_zfmisc_1(k2_zfmisc_1(C_2197,B_2192)))
      | ~ v1_funct_2(E_2193,C_2197,B_2192)
      | ~ v1_funct_1(E_2193)
      | ~ m1_subset_1(D_2194,k1_zfmisc_1(A_2195))
      | v1_xboole_0(D_2194)
      | ~ m1_subset_1(C_2197,k1_zfmisc_1(A_2195))
      | v1_xboole_0(C_2197)
      | v1_xboole_0(B_2192)
      | v1_xboole_0(A_2195) ) ),
    inference(resolution,[status(thm)],[c_64,c_42141])).

tff(c_48407,plain,(
    ! [A_2195,C_2197,E_2193] :
      ( k2_partfun1(k4_subset_1(A_2195,C_2197,'#skF_4'),'#skF_2',k1_tmap_1(A_2195,'#skF_2',C_2197,'#skF_4',E_2193,'#skF_6'),C_2197) = E_2193
      | ~ v1_funct_1(k1_tmap_1(A_2195,'#skF_2',C_2197,'#skF_4',E_2193,'#skF_6'))
      | k2_partfun1(C_2197,'#skF_2',E_2193,k9_subset_1(A_2195,C_2197,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_2195,C_2197,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_2193,k1_zfmisc_1(k2_zfmisc_1(C_2197,'#skF_2')))
      | ~ v1_funct_2(E_2193,C_2197,'#skF_2')
      | ~ v1_funct_1(E_2193)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2195))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_2197,k1_zfmisc_1(A_2195))
      | v1_xboole_0(C_2197)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_2195) ) ),
    inference(resolution,[status(thm)],[c_70,c_48401])).

tff(c_48415,plain,(
    ! [A_2195,C_2197,E_2193] :
      ( k2_partfun1(k4_subset_1(A_2195,C_2197,'#skF_4'),'#skF_2',k1_tmap_1(A_2195,'#skF_2',C_2197,'#skF_4',E_2193,'#skF_6'),C_2197) = E_2193
      | ~ v1_funct_1(k1_tmap_1(A_2195,'#skF_2',C_2197,'#skF_4',E_2193,'#skF_6'))
      | k2_partfun1(C_2197,'#skF_2',E_2193,k9_subset_1(A_2195,C_2197,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2195,C_2197,'#skF_4'))
      | ~ m1_subset_1(E_2193,k1_zfmisc_1(k2_zfmisc_1(C_2197,'#skF_2')))
      | ~ v1_funct_2(E_2193,C_2197,'#skF_2')
      | ~ v1_funct_1(E_2193)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2195))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_2197,k1_zfmisc_1(A_2195))
      | v1_xboole_0(C_2197)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_2195) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_32444,c_48407])).

tff(c_52774,plain,(
    ! [A_2261,C_2262,E_2263] :
      ( k2_partfun1(k4_subset_1(A_2261,C_2262,'#skF_4'),'#skF_2',k1_tmap_1(A_2261,'#skF_2',C_2262,'#skF_4',E_2263,'#skF_6'),C_2262) = E_2263
      | ~ v1_funct_1(k1_tmap_1(A_2261,'#skF_2',C_2262,'#skF_4',E_2263,'#skF_6'))
      | k2_partfun1(C_2262,'#skF_2',E_2263,k9_subset_1(A_2261,C_2262,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2261,C_2262,'#skF_4'))
      | ~ m1_subset_1(E_2263,k1_zfmisc_1(k2_zfmisc_1(C_2262,'#skF_2')))
      | ~ v1_funct_2(E_2263,C_2262,'#skF_2')
      | ~ v1_funct_1(E_2263)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2261))
      | ~ m1_subset_1(C_2262,k1_zfmisc_1(A_2261))
      | v1_xboole_0(C_2262)
      | v1_xboole_0(A_2261) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_86,c_48415])).

tff(c_52779,plain,(
    ! [A_2261] :
      ( k2_partfun1(k4_subset_1(A_2261,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_2261,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_2261,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_2261,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2261,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2261))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_2261))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2261) ) ),
    inference(resolution,[status(thm)],[c_76,c_52774])).

tff(c_52787,plain,(
    ! [A_2261] :
      ( k2_partfun1(k4_subset_1(A_2261,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_2261,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_2261,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_2261,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2261,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2261))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_2261))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2261) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_32441,c_52779])).

tff(c_53907,plain,(
    ! [A_2270] :
      ( k2_partfun1(k4_subset_1(A_2270,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_2270,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_2270,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_2270,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2270,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2270))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_2270))
      | v1_xboole_0(A_2270) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_52787])).

tff(c_30836,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_6472])).

tff(c_34863,plain,(
    ! [C_1842,A_1841,B_1843,D_1840,G_1839] :
      ( k1_tmap_1(A_1841,B_1843,C_1842,D_1840,k2_partfun1(k4_subset_1(A_1841,C_1842,D_1840),B_1843,G_1839,C_1842),k2_partfun1(k4_subset_1(A_1841,C_1842,D_1840),B_1843,G_1839,D_1840)) = G_1839
      | ~ m1_subset_1(G_1839,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1841,C_1842,D_1840),B_1843)))
      | ~ v1_funct_2(G_1839,k4_subset_1(A_1841,C_1842,D_1840),B_1843)
      | ~ v1_funct_1(G_1839)
      | k2_partfun1(D_1840,B_1843,k2_partfun1(k4_subset_1(A_1841,C_1842,D_1840),B_1843,G_1839,D_1840),k9_subset_1(A_1841,C_1842,D_1840)) != k2_partfun1(C_1842,B_1843,k2_partfun1(k4_subset_1(A_1841,C_1842,D_1840),B_1843,G_1839,C_1842),k9_subset_1(A_1841,C_1842,D_1840))
      | ~ m1_subset_1(k2_partfun1(k4_subset_1(A_1841,C_1842,D_1840),B_1843,G_1839,D_1840),k1_zfmisc_1(k2_zfmisc_1(D_1840,B_1843)))
      | ~ v1_funct_2(k2_partfun1(k4_subset_1(A_1841,C_1842,D_1840),B_1843,G_1839,D_1840),D_1840,B_1843)
      | ~ v1_funct_1(k2_partfun1(k4_subset_1(A_1841,C_1842,D_1840),B_1843,G_1839,D_1840))
      | ~ m1_subset_1(k2_partfun1(k4_subset_1(A_1841,C_1842,D_1840),B_1843,G_1839,C_1842),k1_zfmisc_1(k2_zfmisc_1(C_1842,B_1843)))
      | ~ v1_funct_2(k2_partfun1(k4_subset_1(A_1841,C_1842,D_1840),B_1843,G_1839,C_1842),C_1842,B_1843)
      | ~ v1_funct_1(k2_partfun1(k4_subset_1(A_1841,C_1842,D_1840),B_1843,G_1839,C_1842))
      | ~ m1_subset_1(D_1840,k1_zfmisc_1(A_1841))
      | v1_xboole_0(D_1840)
      | ~ m1_subset_1(C_1842,k1_zfmisc_1(A_1841))
      | v1_xboole_0(C_1842)
      | v1_xboole_0(B_1843)
      | v1_xboole_0(A_1841) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_34865,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_30836,c_34863])).

tff(c_34867,plain,
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
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_84,c_74,c_30836,c_72,c_30836,c_70,c_34501,c_34719,c_34719,c_32444,c_30836,c_31224,c_31224,c_30836,c_34865])).

tff(c_34868,plain,
    ( k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_6') = k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')))
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k2_partfun1('#skF_3','#skF_2',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_xboole_0) != k1_xboole_0
    | ~ m1_subset_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_92,c_90,c_86,c_34867])).

tff(c_37379,plain,
    ( k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_6') = k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')))
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | k2_partfun1('#skF_3','#skF_2',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_xboole_0) != k1_xboole_0
    | ~ m1_subset_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36467,c_34868])).

tff(c_37380,plain,(
    ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_37379])).

tff(c_53916,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_53907,c_37380])).

tff(c_53929,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_84,c_34501,c_34719,c_33436,c_34719,c_31224,c_31224,c_36467,c_80,c_53916])).

tff(c_53931,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_53929])).

tff(c_53932,plain,
    ( ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | k2_partfun1('#skF_3','#skF_2',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_xboole_0) != k1_xboole_0
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')))
    | k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_6') = k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_37379])).

tff(c_54364,plain,(
    ~ m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_53932])).

tff(c_54367,plain,
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
    inference(resolution,[status(thm)],[c_62,c_54364])).

tff(c_54370,plain,
    ( v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_84,c_80,c_78,c_76,c_74,c_72,c_70,c_54367])).

tff(c_54372,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_92,c_90,c_86,c_54370])).

tff(c_54374,plain,(
    m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_53932])).

tff(c_60,plain,(
    ! [E_165,D_157,A_45,C_141,B_109,F_169] :
      ( k2_partfun1(k4_subset_1(A_45,C_141,D_157),B_109,k1_tmap_1(A_45,B_109,C_141,D_157,E_165,F_169),C_141) = E_165
      | ~ m1_subset_1(k1_tmap_1(A_45,B_109,C_141,D_157,E_165,F_169),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_45,C_141,D_157),B_109)))
      | ~ v1_funct_2(k1_tmap_1(A_45,B_109,C_141,D_157,E_165,F_169),k4_subset_1(A_45,C_141,D_157),B_109)
      | ~ v1_funct_1(k1_tmap_1(A_45,B_109,C_141,D_157,E_165,F_169))
      | k2_partfun1(D_157,B_109,F_169,k9_subset_1(A_45,C_141,D_157)) != k2_partfun1(C_141,B_109,E_165,k9_subset_1(A_45,C_141,D_157))
      | ~ m1_subset_1(F_169,k1_zfmisc_1(k2_zfmisc_1(D_157,B_109)))
      | ~ v1_funct_2(F_169,D_157,B_109)
      | ~ v1_funct_1(F_169)
      | ~ m1_subset_1(E_165,k1_zfmisc_1(k2_zfmisc_1(C_141,B_109)))
      | ~ v1_funct_2(E_165,C_141,B_109)
      | ~ v1_funct_1(E_165)
      | ~ m1_subset_1(D_157,k1_zfmisc_1(A_45))
      | v1_xboole_0(D_157)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(A_45))
      | v1_xboole_0(C_141)
      | v1_xboole_0(B_109)
      | v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_54382,plain,
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
    inference(resolution,[status(thm)],[c_54374,c_60])).

tff(c_54416,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_84,c_80,c_78,c_76,c_74,c_72,c_70,c_34501,c_34719,c_31224,c_33436,c_34719,c_31224,c_32441,c_32444,c_36467,c_54382])).

tff(c_54417,plain,(
    ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_92,c_90,c_86,c_30835,c_54416])).

tff(c_54528,plain,
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
    inference(resolution,[status(thm)],[c_64,c_54417])).

tff(c_54531,plain,
    ( v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_84,c_80,c_78,c_76,c_74,c_72,c_70,c_54528])).

tff(c_54533,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_92,c_90,c_86,c_54531])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:29:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.58/8.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.86/8.30  
% 15.86/8.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.86/8.31  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 15.86/8.31  
% 15.86/8.31  %Foreground sorts:
% 15.86/8.31  
% 15.86/8.31  
% 15.86/8.31  %Background operators:
% 15.86/8.31  
% 15.86/8.31  
% 15.86/8.31  %Foreground operators:
% 15.86/8.31  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 15.86/8.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 15.86/8.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.86/8.31  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 15.86/8.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.86/8.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.86/8.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 15.86/8.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 15.86/8.31  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 15.86/8.31  tff('#skF_5', type, '#skF_5': $i).
% 15.86/8.31  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 15.86/8.31  tff('#skF_6', type, '#skF_6': $i).
% 15.86/8.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 15.86/8.31  tff('#skF_2', type, '#skF_2': $i).
% 15.86/8.31  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 15.86/8.31  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 15.86/8.31  tff('#skF_3', type, '#skF_3': $i).
% 15.86/8.31  tff('#skF_1', type, '#skF_1': $i).
% 15.86/8.31  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 15.86/8.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.86/8.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.86/8.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 15.86/8.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 15.86/8.31  tff('#skF_4', type, '#skF_4': $i).
% 15.86/8.31  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 15.86/8.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.86/8.31  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 15.86/8.31  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 15.86/8.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.86/8.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 15.86/8.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 15.86/8.31  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 15.86/8.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.86/8.31  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 15.86/8.31  
% 16.24/8.36  tff(f_256, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 16.24/8.36  tff(f_214, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 16.24/8.36  tff(f_30, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 16.24/8.36  tff(f_47, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 16.24/8.36  tff(f_74, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 16.24/8.36  tff(f_84, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 16.24/8.36  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 16.24/8.36  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 16.24/8.36  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 16.24/8.36  tff(f_126, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 16.24/8.36  tff(f_118, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 16.24/8.36  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 16.24/8.36  tff(f_94, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 16.24/8.36  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 16.24/8.36  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 16.24/8.36  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 16.24/8.36  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 16.24/8.36  tff(f_34, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 16.24/8.36  tff(f_132, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 16.24/8.36  tff(f_180, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 16.24/8.36  tff(c_94, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_256])).
% 16.24/8.36  tff(c_92, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_256])).
% 16.24/8.36  tff(c_90, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_256])).
% 16.24/8.36  tff(c_86, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_256])).
% 16.24/8.36  tff(c_88, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_256])).
% 16.24/8.36  tff(c_84, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_256])).
% 16.24/8.36  tff(c_80, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_256])).
% 16.24/8.36  tff(c_78, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_256])).
% 16.24/8.36  tff(c_76, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_256])).
% 16.24/8.36  tff(c_74, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_256])).
% 16.24/8.36  tff(c_72, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_256])).
% 16.24/8.36  tff(c_70, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_256])).
% 16.24/8.36  tff(c_64, plain, (![F_177, D_175, A_172, C_174, E_176, B_173]: (v1_funct_2(k1_tmap_1(A_172, B_173, C_174, D_175, E_176, F_177), k4_subset_1(A_172, C_174, D_175), B_173) | ~m1_subset_1(F_177, k1_zfmisc_1(k2_zfmisc_1(D_175, B_173))) | ~v1_funct_2(F_177, D_175, B_173) | ~v1_funct_1(F_177) | ~m1_subset_1(E_176, k1_zfmisc_1(k2_zfmisc_1(C_174, B_173))) | ~v1_funct_2(E_176, C_174, B_173) | ~v1_funct_1(E_176) | ~m1_subset_1(D_175, k1_zfmisc_1(A_172)) | v1_xboole_0(D_175) | ~m1_subset_1(C_174, k1_zfmisc_1(A_172)) | v1_xboole_0(C_174) | v1_xboole_0(B_173) | v1_xboole_0(A_172))), inference(cnfTransformation, [status(thm)], [f_214])).
% 16.24/8.36  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 16.24/8.36  tff(c_103, plain, (![A_235]: (v1_relat_1(A_235) | ~v1_xboole_0(A_235))), inference(cnfTransformation, [status(thm)], [f_47])).
% 16.24/8.36  tff(c_107, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_103])).
% 16.24/8.36  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 16.24/8.36  tff(c_6598, plain, (![B_726, A_727]: (r1_xboole_0(k1_relat_1(B_726), A_727) | k7_relat_1(B_726, A_727)!=k1_xboole_0 | ~v1_relat_1(B_726))), inference(cnfTransformation, [status(thm)], [f_84])).
% 16.24/8.36  tff(c_6607, plain, (![A_727]: (r1_xboole_0(k1_xboole_0, A_727) | k7_relat_1(k1_xboole_0, A_727)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_6598])).
% 16.24/8.36  tff(c_6612, plain, (![A_728]: (r1_xboole_0(k1_xboole_0, A_728) | k7_relat_1(k1_xboole_0, A_728)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_107, c_6607])).
% 16.24/8.36  tff(c_6551, plain, (![B_722, A_723]: (k9_relat_1(B_722, A_723)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_722), A_723) | ~v1_relat_1(B_722))), inference(cnfTransformation, [status(thm)], [f_57])).
% 16.24/8.36  tff(c_6558, plain, (![A_723]: (k9_relat_1(k1_xboole_0, A_723)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_723) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_6551])).
% 16.24/8.36  tff(c_6561, plain, (![A_723]: (k9_relat_1(k1_xboole_0, A_723)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_723))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_6558])).
% 16.24/8.36  tff(c_6619, plain, (![A_728]: (k9_relat_1(k1_xboole_0, A_728)=k1_xboole_0 | k7_relat_1(k1_xboole_0, A_728)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6612, c_6561])).
% 16.24/8.36  tff(c_6781, plain, (![B_743, A_744]: (r1_xboole_0(k1_relat_1(B_743), A_744) | k9_relat_1(B_743, A_744)!=k1_xboole_0 | ~v1_relat_1(B_743))), inference(cnfTransformation, [status(thm)], [f_57])).
% 16.24/8.36  tff(c_6800, plain, (![A_744]: (r1_xboole_0(k1_xboole_0, A_744) | k9_relat_1(k1_xboole_0, A_744)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_6781])).
% 16.24/8.36  tff(c_6807, plain, (![A_744]: (r1_xboole_0(k1_xboole_0, A_744) | k9_relat_1(k1_xboole_0, A_744)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_107, c_6800])).
% 16.24/8.36  tff(c_6480, plain, (![C_708, A_709, B_710]: (v1_relat_1(C_708) | ~m1_subset_1(C_708, k1_zfmisc_1(k2_zfmisc_1(A_709, B_710))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 16.24/8.36  tff(c_6488, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_70, c_6480])).
% 16.24/8.36  tff(c_6533, plain, (![C_716, A_717, B_718]: (v4_relat_1(C_716, A_717) | ~m1_subset_1(C_716, k1_zfmisc_1(k2_zfmisc_1(A_717, B_718))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 16.24/8.36  tff(c_6541, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_70, c_6533])).
% 16.24/8.36  tff(c_6886, plain, (![B_747, A_748]: (k1_relat_1(B_747)=A_748 | ~v1_partfun1(B_747, A_748) | ~v4_relat_1(B_747, A_748) | ~v1_relat_1(B_747))), inference(cnfTransformation, [status(thm)], [f_126])).
% 16.24/8.36  tff(c_6889, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_6541, c_6886])).
% 16.24/8.36  tff(c_6895, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6488, c_6889])).
% 16.24/8.36  tff(c_6903, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_6895])).
% 16.24/8.36  tff(c_7696, plain, (![C_816, A_817, B_818]: (v1_partfun1(C_816, A_817) | ~v1_funct_2(C_816, A_817, B_818) | ~v1_funct_1(C_816) | ~m1_subset_1(C_816, k1_zfmisc_1(k2_zfmisc_1(A_817, B_818))) | v1_xboole_0(B_818))), inference(cnfTransformation, [status(thm)], [f_118])).
% 16.24/8.36  tff(c_7702, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_70, c_7696])).
% 16.24/8.36  tff(c_7709, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_7702])).
% 16.24/8.36  tff(c_7711, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_6903, c_7709])).
% 16.24/8.36  tff(c_7712, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_6895])).
% 16.24/8.36  tff(c_24, plain, (![A_20, B_22]: (k7_relat_1(A_20, B_22)=k1_xboole_0 | ~r1_xboole_0(B_22, k1_relat_1(A_20)) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_71])).
% 16.24/8.36  tff(c_7720, plain, (![B_22]: (k7_relat_1('#skF_6', B_22)=k1_xboole_0 | ~r1_xboole_0(B_22, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_7712, c_24])).
% 16.24/8.36  tff(c_8497, plain, (![B_870]: (k7_relat_1('#skF_6', B_870)=k1_xboole_0 | ~r1_xboole_0(B_870, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6488, c_7720])).
% 16.24/8.36  tff(c_8543, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0 | k9_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6807, c_8497])).
% 16.24/8.36  tff(c_9998, plain, (k9_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_8543])).
% 16.24/8.36  tff(c_10005, plain, (k7_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6619, c_9998])).
% 16.24/8.36  tff(c_20, plain, (![B_14, A_13]: (r1_xboole_0(k1_relat_1(B_14), A_13) | k9_relat_1(B_14, A_13)!=k1_xboole_0 | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 16.24/8.36  tff(c_7717, plain, (![A_13]: (r1_xboole_0('#skF_4', A_13) | k9_relat_1('#skF_6', A_13)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_7712, c_20])).
% 16.24/8.36  tff(c_8330, plain, (![A_864]: (r1_xboole_0('#skF_4', A_864) | k9_relat_1('#skF_6', A_864)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6488, c_7717])).
% 16.24/8.36  tff(c_6755, plain, (![A_741, B_742]: (k7_relat_1(A_741, B_742)=k1_xboole_0 | ~r1_xboole_0(B_742, k1_relat_1(A_741)) | ~v1_relat_1(A_741))), inference(cnfTransformation, [status(thm)], [f_71])).
% 16.24/8.36  tff(c_6774, plain, (![B_742]: (k7_relat_1(k1_xboole_0, B_742)=k1_xboole_0 | ~r1_xboole_0(B_742, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_6755])).
% 16.24/8.36  tff(c_6780, plain, (![B_742]: (k7_relat_1(k1_xboole_0, B_742)=k1_xboole_0 | ~r1_xboole_0(B_742, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_6774])).
% 16.24/8.36  tff(c_8349, plain, (k7_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0 | k9_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_8330, c_6780])).
% 16.24/8.36  tff(c_10109, plain, (k9_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_10005, c_8349])).
% 16.24/8.36  tff(c_82, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_256])).
% 16.24/8.36  tff(c_38, plain, (![A_27, B_28]: (r1_xboole_0(A_27, B_28) | ~r1_subset_1(A_27, B_28) | v1_xboole_0(B_28) | v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_94])).
% 16.24/8.36  tff(c_6487, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_76, c_6480])).
% 16.24/8.36  tff(c_6540, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_76, c_6533])).
% 16.24/8.36  tff(c_6892, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_6540, c_6886])).
% 16.24/8.36  tff(c_6898, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6487, c_6892])).
% 16.24/8.36  tff(c_7754, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_6898])).
% 16.24/8.36  tff(c_8172, plain, (![C_852, A_853, B_854]: (v1_partfun1(C_852, A_853) | ~v1_funct_2(C_852, A_853, B_854) | ~v1_funct_1(C_852) | ~m1_subset_1(C_852, k1_zfmisc_1(k2_zfmisc_1(A_853, B_854))) | v1_xboole_0(B_854))), inference(cnfTransformation, [status(thm)], [f_118])).
% 16.24/8.36  tff(c_8175, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_76, c_8172])).
% 16.24/8.36  tff(c_8181, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_8175])).
% 16.24/8.36  tff(c_8183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_7754, c_8181])).
% 16.24/8.36  tff(c_8184, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_6898])).
% 16.24/8.36  tff(c_18, plain, (![B_14, A_13]: (k9_relat_1(B_14, A_13)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_14), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 16.24/8.36  tff(c_8204, plain, (![A_13]: (k9_relat_1('#skF_5', A_13)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_13) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_8184, c_18])).
% 16.24/8.36  tff(c_8272, plain, (![A_857]: (k9_relat_1('#skF_5', A_857)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_857))), inference(demodulation, [status(thm), theory('equality')], [c_6487, c_8204])).
% 16.24/8.36  tff(c_8276, plain, (![B_28]: (k9_relat_1('#skF_5', B_28)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_28) | v1_xboole_0(B_28) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_8272])).
% 16.24/8.36  tff(c_8710, plain, (![B_886]: (k9_relat_1('#skF_5', B_886)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_886) | v1_xboole_0(B_886))), inference(negUnitSimplification, [status(thm)], [c_90, c_8276])).
% 16.24/8.36  tff(c_8713, plain, (k9_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_82, c_8710])).
% 16.24/8.36  tff(c_8716, plain, (k9_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_86, c_8713])).
% 16.24/8.36  tff(c_8189, plain, (![A_13]: (r1_xboole_0('#skF_3', A_13) | k9_relat_1('#skF_5', A_13)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_8184, c_20])).
% 16.24/8.36  tff(c_8211, plain, (![A_13]: (r1_xboole_0('#skF_3', A_13) | k9_relat_1('#skF_5', A_13)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6487, c_8189])).
% 16.24/8.36  tff(c_8539, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | k9_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_8211, c_8497])).
% 16.24/8.36  tff(c_9983, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8716, c_8539])).
% 16.24/8.36  tff(c_34, plain, (![B_26, A_25]: (r1_xboole_0(k1_relat_1(B_26), A_25) | k7_relat_1(B_26, A_25)!=k1_xboole_0 | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_84])).
% 16.24/8.36  tff(c_7729, plain, (![A_25]: (r1_xboole_0('#skF_4', A_25) | k7_relat_1('#skF_6', A_25)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_7712, c_34])).
% 16.24/8.36  tff(c_8247, plain, (![A_856]: (r1_xboole_0('#skF_4', A_856) | k7_relat_1('#skF_6', A_856)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6488, c_7729])).
% 16.24/8.36  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 16.24/8.36  tff(c_10433, plain, (![A_1027]: (k3_xboole_0('#skF_4', A_1027)=k1_xboole_0 | k7_relat_1('#skF_6', A_1027)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8247, c_2])).
% 16.24/8.36  tff(c_10445, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_9983, c_10433])).
% 16.24/8.36  tff(c_26, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 16.24/8.36  tff(c_6510, plain, (![A_715]: (k9_relat_1(A_715, k1_relat_1(A_715))=k2_relat_1(A_715) | ~v1_relat_1(A_715))), inference(cnfTransformation, [status(thm)], [f_51])).
% 16.24/8.36  tff(c_6519, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_6510])).
% 16.24/8.36  tff(c_6523, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_107, c_26, c_6519])).
% 16.24/8.36  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 16.24/8.36  tff(c_32, plain, (![B_26, A_25]: (k7_relat_1(B_26, A_25)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_26), A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_84])).
% 16.24/8.36  tff(c_7723, plain, (![A_25]: (k7_relat_1('#skF_6', A_25)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_25) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_7712, c_32])).
% 16.24/8.36  tff(c_8364, plain, (![A_866]: (k7_relat_1('#skF_6', A_866)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_866))), inference(demodulation, [status(thm), theory('equality')], [c_6488, c_7723])).
% 16.24/8.36  tff(c_10309, plain, (![B_1017]: (k7_relat_1('#skF_6', B_1017)=k1_xboole_0 | k3_xboole_0('#skF_4', B_1017)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_8364])).
% 16.24/8.36  tff(c_30, plain, (![B_24, A_23]: (r1_tarski(k1_relat_1(k7_relat_1(B_24, A_23)), A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_78])).
% 16.24/8.36  tff(c_10324, plain, (![B_1017]: (r1_tarski(k1_relat_1(k1_xboole_0), B_1017) | ~v1_relat_1('#skF_6') | k3_xboole_0('#skF_4', B_1017)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10309, c_30])).
% 16.24/8.36  tff(c_10340, plain, (![B_1017]: (r1_tarski(k1_xboole_0, B_1017) | k3_xboole_0('#skF_4', B_1017)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6488, c_28, c_10324])).
% 16.24/8.36  tff(c_22, plain, (![A_15, C_19, B_18]: (k9_relat_1(k7_relat_1(A_15, C_19), B_18)=k9_relat_1(A_15, B_18) | ~r1_tarski(B_18, C_19) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_64])).
% 16.24/8.36  tff(c_9987, plain, (![B_18]: (k9_relat_1(k1_xboole_0, B_18)=k9_relat_1('#skF_6', B_18) | ~r1_tarski(B_18, '#skF_3') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_9983, c_22])).
% 16.24/8.36  tff(c_10892, plain, (![B_1057]: (k9_relat_1(k1_xboole_0, B_1057)=k9_relat_1('#skF_6', B_1057) | ~r1_tarski(B_1057, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6488, c_9987])).
% 16.24/8.36  tff(c_10900, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k9_relat_1('#skF_6', k1_xboole_0) | k3_xboole_0('#skF_4', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_10340, c_10892])).
% 16.24/8.36  tff(c_10929, plain, (k9_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10445, c_6523, c_10900])).
% 16.24/8.36  tff(c_10931, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10109, c_10929])).
% 16.24/8.36  tff(c_10932, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_8543])).
% 16.24/8.36  tff(c_36, plain, (![A_27, B_28]: (r1_subset_1(A_27, B_28) | ~r1_xboole_0(A_27, B_28) | v1_xboole_0(B_28) | v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_94])).
% 16.24/8.36  tff(c_8261, plain, (![A_856]: (r1_subset_1('#skF_4', A_856) | v1_xboole_0(A_856) | v1_xboole_0('#skF_4') | k7_relat_1('#skF_6', A_856)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8247, c_36])).
% 16.24/8.36  tff(c_8270, plain, (![A_856]: (r1_subset_1('#skF_4', A_856) | v1_xboole_0(A_856) | k7_relat_1('#skF_6', A_856)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_86, c_8261])).
% 16.24/8.36  tff(c_8192, plain, (![B_22]: (k7_relat_1('#skF_5', B_22)=k1_xboole_0 | ~r1_xboole_0(B_22, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_8184, c_24])).
% 16.24/8.36  tff(c_8443, plain, (![B_869]: (k7_relat_1('#skF_5', B_869)=k1_xboole_0 | ~r1_xboole_0(B_869, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6487, c_8192])).
% 16.24/8.36  tff(c_8471, plain, (![A_27]: (k7_relat_1('#skF_5', A_27)=k1_xboole_0 | ~r1_subset_1(A_27, '#skF_3') | v1_xboole_0('#skF_3') | v1_xboole_0(A_27))), inference(resolution, [status(thm)], [c_38, c_8443])).
% 16.24/8.36  tff(c_11031, plain, (![A_1061]: (k7_relat_1('#skF_5', A_1061)=k1_xboole_0 | ~r1_subset_1(A_1061, '#skF_3') | v1_xboole_0(A_1061))), inference(negUnitSimplification, [status(thm)], [c_90, c_8471])).
% 16.24/8.36  tff(c_11035, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | k7_relat_1('#skF_6', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_8270, c_11031])).
% 16.24/8.36  tff(c_11038, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9983, c_11035])).
% 16.24/8.36  tff(c_11039, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_90, c_86, c_11038])).
% 16.24/8.36  tff(c_8201, plain, (![A_25]: (r1_xboole_0('#skF_3', A_25) | k7_relat_1('#skF_5', A_25)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_8184, c_34])).
% 16.24/8.36  tff(c_8414, plain, (![A_868]: (r1_xboole_0('#skF_3', A_868) | k7_relat_1('#skF_5', A_868)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6487, c_8201])).
% 16.24/8.36  tff(c_11054, plain, (![A_1062]: (k3_xboole_0('#skF_3', A_1062)=k1_xboole_0 | k7_relat_1('#skF_5', A_1062)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8414, c_2])).
% 16.24/8.36  tff(c_11061, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_11039, c_11054])).
% 16.24/8.36  tff(c_6611, plain, (![A_727]: (r1_xboole_0(k1_xboole_0, A_727) | k7_relat_1(k1_xboole_0, A_727)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_107, c_6607])).
% 16.24/8.36  tff(c_8494, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0 | k7_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6611, c_8443])).
% 16.24/8.36  tff(c_8721, plain, (k7_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_8494])).
% 16.24/8.36  tff(c_8385, plain, (![A_867]: (r1_xboole_0('#skF_3', A_867) | k9_relat_1('#skF_5', A_867)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6487, c_8189])).
% 16.24/8.36  tff(c_8408, plain, (k7_relat_1(k1_xboole_0, '#skF_3')=k1_xboole_0 | k9_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_8385, c_6780])).
% 16.24/8.36  tff(c_9529, plain, (k9_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_8721, c_8408])).
% 16.24/8.36  tff(c_8772, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8716, c_8539])).
% 16.24/8.36  tff(c_8968, plain, (![A_916]: (k3_xboole_0('#skF_4', A_916)=k1_xboole_0 | k7_relat_1('#skF_6', A_916)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8247, c_2])).
% 16.24/8.36  tff(c_8972, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_8772, c_8968])).
% 16.24/8.36  tff(c_7732, plain, (![A_13]: (k9_relat_1('#skF_6', A_13)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_13) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_7712, c_18])).
% 16.24/8.36  tff(c_8234, plain, (![A_855]: (k9_relat_1('#skF_6', A_855)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_855))), inference(demodulation, [status(thm), theory('equality')], [c_6488, c_7732])).
% 16.24/8.36  tff(c_9167, plain, (![B_931]: (k9_relat_1('#skF_6', B_931)=k1_xboole_0 | k3_xboole_0('#skF_4', B_931)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_8234])).
% 16.24/8.36  tff(c_7739, plain, (![A_13]: (r1_xboole_0('#skF_4', A_13) | k9_relat_1('#skF_6', A_13)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6488, c_7717])).
% 16.24/8.36  tff(c_8487, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | k9_relat_1('#skF_6', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_7739, c_8443])).
% 16.24/8.36  tff(c_8873, plain, (k9_relat_1('#skF_6', '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_8487])).
% 16.24/8.36  tff(c_9176, plain, (k3_xboole_0('#skF_4', '#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_9167, c_8873])).
% 16.24/8.36  tff(c_9199, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8972, c_9176])).
% 16.24/8.36  tff(c_9200, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_8487])).
% 16.24/8.36  tff(c_8442, plain, (![A_868]: (k3_xboole_0('#skF_3', A_868)=k1_xboole_0 | k7_relat_1('#skF_5', A_868)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8414, c_2])).
% 16.24/8.36  tff(c_9221, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_9200, c_8442])).
% 16.24/8.36  tff(c_8195, plain, (![A_25]: (k7_relat_1('#skF_5', A_25)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_25) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_8184, c_32])).
% 16.24/8.36  tff(c_8285, plain, (![A_858]: (k7_relat_1('#skF_5', A_858)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_858))), inference(demodulation, [status(thm), theory('equality')], [c_6487, c_8195])).
% 16.24/8.36  tff(c_9320, plain, (![B_947]: (k7_relat_1('#skF_5', B_947)=k1_xboole_0 | k3_xboole_0('#skF_3', B_947)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_8285])).
% 16.24/8.36  tff(c_9341, plain, (![B_947]: (r1_tarski(k1_relat_1(k1_xboole_0), B_947) | ~v1_relat_1('#skF_5') | k3_xboole_0('#skF_3', B_947)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_9320, c_30])).
% 16.24/8.36  tff(c_9361, plain, (![B_947]: (r1_tarski(k1_xboole_0, B_947) | k3_xboole_0('#skF_3', B_947)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6487, c_28, c_9341])).
% 16.24/8.36  tff(c_9211, plain, (![B_18]: (k9_relat_1(k1_xboole_0, B_18)=k9_relat_1('#skF_5', B_18) | ~r1_tarski(B_18, '#skF_4') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_9200, c_22])).
% 16.24/8.36  tff(c_9886, plain, (![B_982]: (k9_relat_1(k1_xboole_0, B_982)=k9_relat_1('#skF_5', B_982) | ~r1_tarski(B_982, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6487, c_9211])).
% 16.24/8.36  tff(c_9894, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k9_relat_1('#skF_5', k1_xboole_0) | k3_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_9361, c_9886])).
% 16.24/8.36  tff(c_9923, plain, (k9_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_9221, c_6523, c_9894])).
% 16.24/8.36  tff(c_9925, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9529, c_9923])).
% 16.24/8.36  tff(c_9926, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_8494])).
% 16.24/8.36  tff(c_8298, plain, (![A_859, B_860, C_861]: (k9_subset_1(A_859, B_860, C_861)=k3_xboole_0(B_860, C_861) | ~m1_subset_1(C_861, k1_zfmisc_1(A_859)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 16.24/8.36  tff(c_8310, plain, (![B_860]: (k9_subset_1('#skF_1', B_860, '#skF_4')=k3_xboole_0(B_860, '#skF_4'))), inference(resolution, [status(thm)], [c_84, c_8298])).
% 16.24/8.36  tff(c_11118, plain, (![C_1069, B_1064, E_1065, D_1066, A_1067, F_1068]: (v1_funct_1(k1_tmap_1(A_1067, B_1064, C_1069, D_1066, E_1065, F_1068)) | ~m1_subset_1(F_1068, k1_zfmisc_1(k2_zfmisc_1(D_1066, B_1064))) | ~v1_funct_2(F_1068, D_1066, B_1064) | ~v1_funct_1(F_1068) | ~m1_subset_1(E_1065, k1_zfmisc_1(k2_zfmisc_1(C_1069, B_1064))) | ~v1_funct_2(E_1065, C_1069, B_1064) | ~v1_funct_1(E_1065) | ~m1_subset_1(D_1066, k1_zfmisc_1(A_1067)) | v1_xboole_0(D_1066) | ~m1_subset_1(C_1069, k1_zfmisc_1(A_1067)) | v1_xboole_0(C_1069) | v1_xboole_0(B_1064) | v1_xboole_0(A_1067))), inference(cnfTransformation, [status(thm)], [f_214])).
% 16.24/8.36  tff(c_11122, plain, (![A_1067, C_1069, E_1065]: (v1_funct_1(k1_tmap_1(A_1067, '#skF_2', C_1069, '#skF_4', E_1065, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1065, k1_zfmisc_1(k2_zfmisc_1(C_1069, '#skF_2'))) | ~v1_funct_2(E_1065, C_1069, '#skF_2') | ~v1_funct_1(E_1065) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1067)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1069, k1_zfmisc_1(A_1067)) | v1_xboole_0(C_1069) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1067))), inference(resolution, [status(thm)], [c_70, c_11118])).
% 16.24/8.36  tff(c_11129, plain, (![A_1067, C_1069, E_1065]: (v1_funct_1(k1_tmap_1(A_1067, '#skF_2', C_1069, '#skF_4', E_1065, '#skF_6')) | ~m1_subset_1(E_1065, k1_zfmisc_1(k2_zfmisc_1(C_1069, '#skF_2'))) | ~v1_funct_2(E_1065, C_1069, '#skF_2') | ~v1_funct_1(E_1065) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1067)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1069, k1_zfmisc_1(A_1067)) | v1_xboole_0(C_1069) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1067))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_11122])).
% 16.24/8.36  tff(c_12627, plain, (![A_1158, C_1159, E_1160]: (v1_funct_1(k1_tmap_1(A_1158, '#skF_2', C_1159, '#skF_4', E_1160, '#skF_6')) | ~m1_subset_1(E_1160, k1_zfmisc_1(k2_zfmisc_1(C_1159, '#skF_2'))) | ~v1_funct_2(E_1160, C_1159, '#skF_2') | ~v1_funct_1(E_1160) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1158)) | ~m1_subset_1(C_1159, k1_zfmisc_1(A_1158)) | v1_xboole_0(C_1159) | v1_xboole_0(A_1158))), inference(negUnitSimplification, [status(thm)], [c_92, c_86, c_11129])).
% 16.24/8.36  tff(c_12632, plain, (![A_1158]: (v1_funct_1(k1_tmap_1(A_1158, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1158)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1158)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1158))), inference(resolution, [status(thm)], [c_76, c_12627])).
% 16.24/8.36  tff(c_12640, plain, (![A_1158]: (v1_funct_1(k1_tmap_1(A_1158, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1158)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1158)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1158))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_12632])).
% 16.24/8.36  tff(c_13166, plain, (![A_1176]: (v1_funct_1(k1_tmap_1(A_1176, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1176)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1176)) | v1_xboole_0(A_1176))), inference(negUnitSimplification, [status(thm)], [c_90, c_12640])).
% 16.24/8.36  tff(c_13169, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_88, c_13166])).
% 16.24/8.36  tff(c_13172, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_13169])).
% 16.24/8.36  tff(c_13173, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_94, c_13172])).
% 16.24/8.36  tff(c_8676, plain, (![A_879, B_880, C_881, D_882]: (k2_partfun1(A_879, B_880, C_881, D_882)=k7_relat_1(C_881, D_882) | ~m1_subset_1(C_881, k1_zfmisc_1(k2_zfmisc_1(A_879, B_880))) | ~v1_funct_1(C_881))), inference(cnfTransformation, [status(thm)], [f_132])).
% 16.24/8.36  tff(c_8678, plain, (![D_882]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_882)=k7_relat_1('#skF_5', D_882) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_76, c_8676])).
% 16.24/8.36  tff(c_8683, plain, (![D_882]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_882)=k7_relat_1('#skF_5', D_882))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_8678])).
% 16.24/8.36  tff(c_8680, plain, (![D_882]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_882)=k7_relat_1('#skF_6', D_882) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_70, c_8676])).
% 16.24/8.36  tff(c_8686, plain, (![D_882]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_882)=k7_relat_1('#skF_6', D_882))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_8680])).
% 16.24/8.36  tff(c_62, plain, (![F_177, D_175, A_172, C_174, E_176, B_173]: (m1_subset_1(k1_tmap_1(A_172, B_173, C_174, D_175, E_176, F_177), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_172, C_174, D_175), B_173))) | ~m1_subset_1(F_177, k1_zfmisc_1(k2_zfmisc_1(D_175, B_173))) | ~v1_funct_2(F_177, D_175, B_173) | ~v1_funct_1(F_177) | ~m1_subset_1(E_176, k1_zfmisc_1(k2_zfmisc_1(C_174, B_173))) | ~v1_funct_2(E_176, C_174, B_173) | ~v1_funct_1(E_176) | ~m1_subset_1(D_175, k1_zfmisc_1(A_172)) | v1_xboole_0(D_175) | ~m1_subset_1(C_174, k1_zfmisc_1(A_172)) | v1_xboole_0(C_174) | v1_xboole_0(B_173) | v1_xboole_0(A_172))), inference(cnfTransformation, [status(thm)], [f_214])).
% 16.24/8.36  tff(c_11349, plain, (![F_1096, C_1094, A_1092, E_1093, B_1095, D_1091]: (k2_partfun1(k4_subset_1(A_1092, C_1094, D_1091), B_1095, k1_tmap_1(A_1092, B_1095, C_1094, D_1091, E_1093, F_1096), D_1091)=F_1096 | ~m1_subset_1(k1_tmap_1(A_1092, B_1095, C_1094, D_1091, E_1093, F_1096), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1092, C_1094, D_1091), B_1095))) | ~v1_funct_2(k1_tmap_1(A_1092, B_1095, C_1094, D_1091, E_1093, F_1096), k4_subset_1(A_1092, C_1094, D_1091), B_1095) | ~v1_funct_1(k1_tmap_1(A_1092, B_1095, C_1094, D_1091, E_1093, F_1096)) | k2_partfun1(D_1091, B_1095, F_1096, k9_subset_1(A_1092, C_1094, D_1091))!=k2_partfun1(C_1094, B_1095, E_1093, k9_subset_1(A_1092, C_1094, D_1091)) | ~m1_subset_1(F_1096, k1_zfmisc_1(k2_zfmisc_1(D_1091, B_1095))) | ~v1_funct_2(F_1096, D_1091, B_1095) | ~v1_funct_1(F_1096) | ~m1_subset_1(E_1093, k1_zfmisc_1(k2_zfmisc_1(C_1094, B_1095))) | ~v1_funct_2(E_1093, C_1094, B_1095) | ~v1_funct_1(E_1093) | ~m1_subset_1(D_1091, k1_zfmisc_1(A_1092)) | v1_xboole_0(D_1091) | ~m1_subset_1(C_1094, k1_zfmisc_1(A_1092)) | v1_xboole_0(C_1094) | v1_xboole_0(B_1095) | v1_xboole_0(A_1092))), inference(cnfTransformation, [status(thm)], [f_180])).
% 16.24/8.36  tff(c_19599, plain, (![C_1365, A_1363, D_1362, B_1360, F_1364, E_1361]: (k2_partfun1(k4_subset_1(A_1363, C_1365, D_1362), B_1360, k1_tmap_1(A_1363, B_1360, C_1365, D_1362, E_1361, F_1364), D_1362)=F_1364 | ~v1_funct_2(k1_tmap_1(A_1363, B_1360, C_1365, D_1362, E_1361, F_1364), k4_subset_1(A_1363, C_1365, D_1362), B_1360) | ~v1_funct_1(k1_tmap_1(A_1363, B_1360, C_1365, D_1362, E_1361, F_1364)) | k2_partfun1(D_1362, B_1360, F_1364, k9_subset_1(A_1363, C_1365, D_1362))!=k2_partfun1(C_1365, B_1360, E_1361, k9_subset_1(A_1363, C_1365, D_1362)) | ~m1_subset_1(F_1364, k1_zfmisc_1(k2_zfmisc_1(D_1362, B_1360))) | ~v1_funct_2(F_1364, D_1362, B_1360) | ~v1_funct_1(F_1364) | ~m1_subset_1(E_1361, k1_zfmisc_1(k2_zfmisc_1(C_1365, B_1360))) | ~v1_funct_2(E_1361, C_1365, B_1360) | ~v1_funct_1(E_1361) | ~m1_subset_1(D_1362, k1_zfmisc_1(A_1363)) | v1_xboole_0(D_1362) | ~m1_subset_1(C_1365, k1_zfmisc_1(A_1363)) | v1_xboole_0(C_1365) | v1_xboole_0(B_1360) | v1_xboole_0(A_1363))), inference(resolution, [status(thm)], [c_62, c_11349])).
% 16.24/8.36  tff(c_25466, plain, (![E_1463, C_1467, A_1465, F_1466, D_1464, B_1462]: (k2_partfun1(k4_subset_1(A_1465, C_1467, D_1464), B_1462, k1_tmap_1(A_1465, B_1462, C_1467, D_1464, E_1463, F_1466), D_1464)=F_1466 | ~v1_funct_1(k1_tmap_1(A_1465, B_1462, C_1467, D_1464, E_1463, F_1466)) | k2_partfun1(D_1464, B_1462, F_1466, k9_subset_1(A_1465, C_1467, D_1464))!=k2_partfun1(C_1467, B_1462, E_1463, k9_subset_1(A_1465, C_1467, D_1464)) | ~m1_subset_1(F_1466, k1_zfmisc_1(k2_zfmisc_1(D_1464, B_1462))) | ~v1_funct_2(F_1466, D_1464, B_1462) | ~v1_funct_1(F_1466) | ~m1_subset_1(E_1463, k1_zfmisc_1(k2_zfmisc_1(C_1467, B_1462))) | ~v1_funct_2(E_1463, C_1467, B_1462) | ~v1_funct_1(E_1463) | ~m1_subset_1(D_1464, k1_zfmisc_1(A_1465)) | v1_xboole_0(D_1464) | ~m1_subset_1(C_1467, k1_zfmisc_1(A_1465)) | v1_xboole_0(C_1467) | v1_xboole_0(B_1462) | v1_xboole_0(A_1465))), inference(resolution, [status(thm)], [c_64, c_19599])).
% 16.24/8.36  tff(c_25472, plain, (![A_1465, C_1467, E_1463]: (k2_partfun1(k4_subset_1(A_1465, C_1467, '#skF_4'), '#skF_2', k1_tmap_1(A_1465, '#skF_2', C_1467, '#skF_4', E_1463, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1465, '#skF_2', C_1467, '#skF_4', E_1463, '#skF_6')) | k2_partfun1(C_1467, '#skF_2', E_1463, k9_subset_1(A_1465, C_1467, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_1465, C_1467, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1463, k1_zfmisc_1(k2_zfmisc_1(C_1467, '#skF_2'))) | ~v1_funct_2(E_1463, C_1467, '#skF_2') | ~v1_funct_1(E_1463) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1465)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1467, k1_zfmisc_1(A_1465)) | v1_xboole_0(C_1467) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1465))), inference(resolution, [status(thm)], [c_70, c_25466])).
% 16.24/8.36  tff(c_25480, plain, (![A_1465, C_1467, E_1463]: (k2_partfun1(k4_subset_1(A_1465, C_1467, '#skF_4'), '#skF_2', k1_tmap_1(A_1465, '#skF_2', C_1467, '#skF_4', E_1463, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1465, '#skF_2', C_1467, '#skF_4', E_1463, '#skF_6')) | k2_partfun1(C_1467, '#skF_2', E_1463, k9_subset_1(A_1465, C_1467, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1465, C_1467, '#skF_4')) | ~m1_subset_1(E_1463, k1_zfmisc_1(k2_zfmisc_1(C_1467, '#skF_2'))) | ~v1_funct_2(E_1463, C_1467, '#skF_2') | ~v1_funct_1(E_1463) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1465)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1467, k1_zfmisc_1(A_1465)) | v1_xboole_0(C_1467) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1465))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_8686, c_25472])).
% 16.24/8.36  tff(c_30258, plain, (![A_1531, C_1532, E_1533]: (k2_partfun1(k4_subset_1(A_1531, C_1532, '#skF_4'), '#skF_2', k1_tmap_1(A_1531, '#skF_2', C_1532, '#skF_4', E_1533, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1531, '#skF_2', C_1532, '#skF_4', E_1533, '#skF_6')) | k2_partfun1(C_1532, '#skF_2', E_1533, k9_subset_1(A_1531, C_1532, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1531, C_1532, '#skF_4')) | ~m1_subset_1(E_1533, k1_zfmisc_1(k2_zfmisc_1(C_1532, '#skF_2'))) | ~v1_funct_2(E_1533, C_1532, '#skF_2') | ~v1_funct_1(E_1533) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1531)) | ~m1_subset_1(C_1532, k1_zfmisc_1(A_1531)) | v1_xboole_0(C_1532) | v1_xboole_0(A_1531))), inference(negUnitSimplification, [status(thm)], [c_92, c_86, c_25480])).
% 16.24/8.36  tff(c_30263, plain, (![A_1531]: (k2_partfun1(k4_subset_1(A_1531, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1531, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1531, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_1531, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1531, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1531)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1531)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1531))), inference(resolution, [status(thm)], [c_76, c_30258])).
% 16.24/8.36  tff(c_30271, plain, (![A_1531]: (k2_partfun1(k4_subset_1(A_1531, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1531, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1531, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1531, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1531, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1531)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1531)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1531))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_8683, c_30263])).
% 16.24/8.36  tff(c_30807, plain, (![A_1538]: (k2_partfun1(k4_subset_1(A_1538, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1538, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1538, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1538, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1538, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1538)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1538)) | v1_xboole_0(A_1538))), inference(negUnitSimplification, [status(thm)], [c_90, c_30271])).
% 16.24/8.36  tff(c_191, plain, (![B_256, A_257]: (r1_xboole_0(k1_relat_1(B_256), A_257) | k7_relat_1(B_256, A_257)!=k1_xboole_0 | ~v1_relat_1(B_256))), inference(cnfTransformation, [status(thm)], [f_84])).
% 16.24/8.36  tff(c_197, plain, (![A_257]: (r1_xboole_0(k1_xboole_0, A_257) | k7_relat_1(k1_xboole_0, A_257)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_191])).
% 16.24/8.36  tff(c_200, plain, (![A_257]: (r1_xboole_0(k1_xboole_0, A_257) | k7_relat_1(k1_xboole_0, A_257)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_107, c_197])).
% 16.24/8.36  tff(c_393, plain, (![B_275, A_276]: (k9_relat_1(B_275, A_276)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_275), A_276) | ~v1_relat_1(B_275))), inference(cnfTransformation, [status(thm)], [f_57])).
% 16.24/8.36  tff(c_406, plain, (![A_276]: (k9_relat_1(k1_xboole_0, A_276)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_276) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_393])).
% 16.24/8.36  tff(c_412, plain, (![A_277]: (k9_relat_1(k1_xboole_0, A_277)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_277))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_406])).
% 16.24/8.36  tff(c_424, plain, (![A_257]: (k9_relat_1(k1_xboole_0, A_257)=k1_xboole_0 | k7_relat_1(k1_xboole_0, A_257)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_200, c_412])).
% 16.24/8.36  tff(c_124, plain, (![C_242, A_243, B_244]: (v1_relat_1(C_242) | ~m1_subset_1(C_242, k1_zfmisc_1(k2_zfmisc_1(A_243, B_244))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 16.24/8.36  tff(c_132, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_70, c_124])).
% 16.24/8.36  tff(c_173, plain, (![C_250, A_251, B_252]: (v4_relat_1(C_250, A_251) | ~m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(A_251, B_252))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 16.24/8.36  tff(c_181, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_70, c_173])).
% 16.24/8.36  tff(c_675, plain, (![B_290, A_291]: (k1_relat_1(B_290)=A_291 | ~v1_partfun1(B_290, A_291) | ~v4_relat_1(B_290, A_291) | ~v1_relat_1(B_290))), inference(cnfTransformation, [status(thm)], [f_126])).
% 16.24/8.36  tff(c_678, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_181, c_675])).
% 16.24/8.36  tff(c_684, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_678])).
% 16.24/8.36  tff(c_688, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_684])).
% 16.24/8.36  tff(c_1299, plain, (![C_344, A_345, B_346]: (v1_partfun1(C_344, A_345) | ~v1_funct_2(C_344, A_345, B_346) | ~v1_funct_1(C_344) | ~m1_subset_1(C_344, k1_zfmisc_1(k2_zfmisc_1(A_345, B_346))) | v1_xboole_0(B_346))), inference(cnfTransformation, [status(thm)], [f_118])).
% 16.24/8.36  tff(c_1305, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_70, c_1299])).
% 16.24/8.36  tff(c_1312, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_1305])).
% 16.24/8.36  tff(c_1314, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_688, c_1312])).
% 16.24/8.36  tff(c_1315, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_684])).
% 16.24/8.36  tff(c_1336, plain, (![A_25]: (r1_xboole_0('#skF_4', A_25) | k7_relat_1('#skF_6', A_25)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1315, c_34])).
% 16.24/8.36  tff(c_2024, plain, (![A_393]: (r1_xboole_0('#skF_4', A_393) | k7_relat_1('#skF_6', A_393)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_132, c_1336])).
% 16.24/8.36  tff(c_214, plain, (![A_261, B_262]: (k7_relat_1(A_261, B_262)=k1_xboole_0 | ~r1_xboole_0(B_262, k1_relat_1(A_261)) | ~v1_relat_1(A_261))), inference(cnfTransformation, [status(thm)], [f_71])).
% 16.24/8.36  tff(c_229, plain, (![B_262]: (k7_relat_1(k1_xboole_0, B_262)=k1_xboole_0 | ~r1_xboole_0(B_262, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_214])).
% 16.24/8.36  tff(c_234, plain, (![B_262]: (k7_relat_1(k1_xboole_0, B_262)=k1_xboole_0 | ~r1_xboole_0(B_262, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_229])).
% 16.24/8.36  tff(c_2056, plain, (k7_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0 | k7_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_2024, c_234])).
% 16.24/8.36  tff(c_4224, plain, (k7_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2056])).
% 16.24/8.36  tff(c_285, plain, (![B_269, A_270]: (r1_xboole_0(k1_relat_1(B_269), A_270) | k9_relat_1(B_269, A_270)!=k1_xboole_0 | ~v1_relat_1(B_269))), inference(cnfTransformation, [status(thm)], [f_57])).
% 16.24/8.36  tff(c_302, plain, (![A_270]: (r1_xboole_0(k1_xboole_0, A_270) | k9_relat_1(k1_xboole_0, A_270)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_285])).
% 16.24/8.36  tff(c_308, plain, (![A_270]: (r1_xboole_0(k1_xboole_0, A_270) | k9_relat_1(k1_xboole_0, A_270)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_107, c_302])).
% 16.24/8.36  tff(c_1330, plain, (![B_22]: (k7_relat_1('#skF_6', B_22)=k1_xboole_0 | ~r1_xboole_0(B_22, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1315, c_24])).
% 16.24/8.36  tff(c_1842, plain, (![B_383]: (k7_relat_1('#skF_6', B_383)=k1_xboole_0 | ~r1_xboole_0(B_383, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_1330])).
% 16.24/8.36  tff(c_1870, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0 | k9_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_308, c_1842])).
% 16.24/8.36  tff(c_4252, plain, (k9_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_4224, c_1870])).
% 16.24/8.36  tff(c_4260, plain, (k7_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_424, c_4252])).
% 16.24/8.36  tff(c_1327, plain, (![A_13]: (r1_xboole_0('#skF_4', A_13) | k9_relat_1('#skF_6', A_13)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1315, c_20])).
% 16.24/8.36  tff(c_1884, plain, (![A_385]: (r1_xboole_0('#skF_4', A_385) | k9_relat_1('#skF_6', A_385)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_132, c_1327])).
% 16.24/8.36  tff(c_1909, plain, (k7_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0 | k9_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_1884, c_234])).
% 16.24/8.36  tff(c_4387, plain, (k9_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_4260, c_1909])).
% 16.24/8.36  tff(c_621, plain, (![B_286, A_287]: (k9_relat_1(B_286, A_287)=k1_xboole_0 | k7_relat_1(B_286, A_287)!=k1_xboole_0 | ~v1_relat_1(B_286))), inference(resolution, [status(thm)], [c_34, c_393])).
% 16.24/8.36  tff(c_628, plain, (![A_287]: (k9_relat_1('#skF_6', A_287)=k1_xboole_0 | k7_relat_1('#skF_6', A_287)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_132, c_621])).
% 16.24/8.36  tff(c_1347, plain, (![A_13]: (r1_xboole_0('#skF_4', A_13) | k9_relat_1('#skF_6', A_13)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_132, c_1327])).
% 16.24/8.36  tff(c_131, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_76, c_124])).
% 16.24/8.36  tff(c_180, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_76, c_173])).
% 16.24/8.36  tff(c_681, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_180, c_675])).
% 16.24/8.36  tff(c_687, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_681])).
% 16.24/8.36  tff(c_1358, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_687])).
% 16.24/8.36  tff(c_1733, plain, (![C_375, A_376, B_377]: (v1_partfun1(C_375, A_376) | ~v1_funct_2(C_375, A_376, B_377) | ~v1_funct_1(C_375) | ~m1_subset_1(C_375, k1_zfmisc_1(k2_zfmisc_1(A_376, B_377))) | v1_xboole_0(B_377))), inference(cnfTransformation, [status(thm)], [f_118])).
% 16.24/8.36  tff(c_1736, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_76, c_1733])).
% 16.24/8.36  tff(c_1742, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_1736])).
% 16.24/8.36  tff(c_1744, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_1358, c_1742])).
% 16.24/8.36  tff(c_1745, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_687])).
% 16.24/8.36  tff(c_1760, plain, (![B_22]: (k7_relat_1('#skF_5', B_22)=k1_xboole_0 | ~r1_xboole_0(B_22, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1745, c_24])).
% 16.24/8.36  tff(c_2059, plain, (![B_394]: (k7_relat_1('#skF_5', B_394)=k1_xboole_0 | ~r1_xboole_0(B_394, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_1760])).
% 16.24/8.36  tff(c_2100, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | k9_relat_1('#skF_6', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_1347, c_2059])).
% 16.24/8.36  tff(c_2175, plain, (k9_relat_1('#skF_6', '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2100])).
% 16.24/8.36  tff(c_2179, plain, (k7_relat_1('#skF_6', '#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_628, c_2175])).
% 16.24/8.36  tff(c_1754, plain, (![A_25]: (k7_relat_1('#skF_5', A_25)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_25) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1745, c_32])).
% 16.24/8.36  tff(c_2154, plain, (![A_397]: (k7_relat_1('#skF_5', A_397)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_397))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_1754])).
% 16.24/8.36  tff(c_2164, plain, (![B_28]: (k7_relat_1('#skF_5', B_28)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_28) | v1_xboole_0(B_28) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_2154])).
% 16.24/8.36  tff(c_2273, plain, (![B_410]: (k7_relat_1('#skF_5', B_410)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_410) | v1_xboole_0(B_410))), inference(negUnitSimplification, [status(thm)], [c_90, c_2164])).
% 16.24/8.36  tff(c_2276, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_82, c_2273])).
% 16.24/8.36  tff(c_2279, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_86, c_2276])).
% 16.24/8.36  tff(c_1766, plain, (![A_25]: (r1_xboole_0('#skF_3', A_25) | k7_relat_1('#skF_5', A_25)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1745, c_34])).
% 16.24/8.36  tff(c_2118, plain, (![A_396]: (r1_xboole_0('#skF_3', A_396) | k7_relat_1('#skF_5', A_396)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_131, c_1766])).
% 16.24/8.36  tff(c_2132, plain, (![A_396]: (r1_subset_1('#skF_3', A_396) | v1_xboole_0(A_396) | v1_xboole_0('#skF_3') | k7_relat_1('#skF_5', A_396)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2118, c_36])).
% 16.24/8.36  tff(c_2150, plain, (![A_396]: (r1_subset_1('#skF_3', A_396) | v1_xboole_0(A_396) | k7_relat_1('#skF_5', A_396)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_90, c_2132])).
% 16.24/8.36  tff(c_1846, plain, (![A_27]: (k7_relat_1('#skF_6', A_27)=k1_xboole_0 | ~r1_subset_1(A_27, '#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(A_27))), inference(resolution, [status(thm)], [c_38, c_1842])).
% 16.24/8.36  tff(c_2458, plain, (![A_430]: (k7_relat_1('#skF_6', A_430)=k1_xboole_0 | ~r1_subset_1(A_430, '#skF_4') | v1_xboole_0(A_430))), inference(negUnitSimplification, [status(thm)], [c_86, c_1846])).
% 16.24/8.36  tff(c_2462, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_4') | k7_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_2150, c_2458])).
% 16.24/8.36  tff(c_2468, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2279, c_2462])).
% 16.24/8.36  tff(c_2470, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_90, c_2179, c_2468])).
% 16.24/8.36  tff(c_2471, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2100])).
% 16.24/8.36  tff(c_4122, plain, (![A_561]: (k3_xboole_0('#skF_3', A_561)=k1_xboole_0 | k7_relat_1('#skF_5', A_561)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2118, c_2])).
% 16.24/8.36  tff(c_4134, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2471, c_4122])).
% 16.24/8.36  tff(c_155, plain, (![A_249]: (k9_relat_1(A_249, k1_relat_1(A_249))=k2_relat_1(A_249) | ~v1_relat_1(A_249))), inference(cnfTransformation, [status(thm)], [f_51])).
% 16.24/8.36  tff(c_164, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_155])).
% 16.24/8.36  tff(c_168, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_107, c_26, c_164])).
% 16.24/8.36  tff(c_4457, plain, (![A_590]: (k7_relat_1('#skF_6', A_590)=k1_xboole_0 | k3_xboole_0(A_590, '#skF_4')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_1842])).
% 16.24/8.36  tff(c_4481, plain, (![A_590]: (r1_tarski(k1_relat_1(k1_xboole_0), A_590) | ~v1_relat_1('#skF_6') | k3_xboole_0(A_590, '#skF_4')!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4457, c_30])).
% 16.24/8.36  tff(c_4502, plain, (![A_590]: (r1_tarski(k1_xboole_0, A_590) | k3_xboole_0(A_590, '#skF_4')!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_132, c_28, c_4481])).
% 16.24/8.36  tff(c_1349, plain, (![B_22]: (k7_relat_1('#skF_6', B_22)=k1_xboole_0 | ~r1_xboole_0(B_22, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_1330])).
% 16.24/8.36  tff(c_2147, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | k7_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_2118, c_1349])).
% 16.24/8.36  tff(c_4082, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2471, c_2147])).
% 16.24/8.36  tff(c_4086, plain, (![B_18]: (k9_relat_1(k1_xboole_0, B_18)=k9_relat_1('#skF_6', B_18) | ~r1_tarski(B_18, '#skF_3') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_4082, c_22])).
% 16.24/8.36  tff(c_4754, plain, (![B_614]: (k9_relat_1(k1_xboole_0, B_614)=k9_relat_1('#skF_6', B_614) | ~r1_tarski(B_614, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_4086])).
% 16.24/8.36  tff(c_4758, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k9_relat_1('#skF_6', k1_xboole_0) | k3_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_4502, c_4754])).
% 16.24/8.36  tff(c_4788, plain, (k9_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4134, c_168, c_4758])).
% 16.24/8.36  tff(c_4790, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4387, c_4788])).
% 16.24/8.36  tff(c_4792, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_2056])).
% 16.24/8.36  tff(c_2104, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0 | k9_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_308, c_2059])).
% 16.24/8.36  tff(c_2499, plain, (k9_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2104])).
% 16.24/8.36  tff(c_2507, plain, (k7_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_424, c_2499])).
% 16.24/8.36  tff(c_1757, plain, (![A_13]: (r1_xboole_0('#skF_3', A_13) | k9_relat_1('#skF_5', A_13)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1745, c_20])).
% 16.24/8.36  tff(c_1942, plain, (![A_388]: (r1_xboole_0('#skF_3', A_388) | k9_relat_1('#skF_5', A_388)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_131, c_1757])).
% 16.24/8.36  tff(c_1969, plain, (k7_relat_1(k1_xboole_0, '#skF_3')=k1_xboole_0 | k9_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_1942, c_234])).
% 16.24/8.36  tff(c_3495, plain, (k9_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_2507, c_1969])).
% 16.24/8.36  tff(c_2631, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2471, c_2147])).
% 16.24/8.36  tff(c_3303, plain, (![A_499]: (k3_xboole_0('#skF_4', A_499)=k1_xboole_0 | k7_relat_1('#skF_6', A_499)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2024, c_2])).
% 16.24/8.36  tff(c_3311, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2631, c_3303])).
% 16.24/8.36  tff(c_3325, plain, (![A_506]: (k7_relat_1('#skF_5', A_506)=k1_xboole_0 | k3_xboole_0(A_506, '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_2059])).
% 16.24/8.36  tff(c_3349, plain, (![A_506]: (r1_tarski(k1_relat_1(k1_xboole_0), A_506) | ~v1_relat_1('#skF_5') | k3_xboole_0(A_506, '#skF_3')!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3325, c_30])).
% 16.24/8.36  tff(c_3370, plain, (![A_506]: (r1_tarski(k1_xboole_0, A_506) | k3_xboole_0(A_506, '#skF_3')!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_131, c_28, c_3349])).
% 16.24/8.36  tff(c_2476, plain, (![B_18]: (k9_relat_1(k1_xboole_0, B_18)=k9_relat_1('#skF_5', B_18) | ~r1_tarski(B_18, '#skF_4') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2471, c_22])).
% 16.24/8.36  tff(c_3793, plain, (![B_542]: (k9_relat_1(k1_xboole_0, B_542)=k9_relat_1('#skF_5', B_542) | ~r1_tarski(B_542, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_2476])).
% 16.24/8.36  tff(c_3805, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k9_relat_1('#skF_5', k1_xboole_0) | k3_xboole_0('#skF_4', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_3370, c_3793])).
% 16.24/8.36  tff(c_3833, plain, (k9_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3311, c_168, c_3805])).
% 16.24/8.36  tff(c_3835, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3495, c_3833])).
% 16.24/8.36  tff(c_3836, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_2104])).
% 16.24/8.36  tff(c_3921, plain, (![A_544, B_545, C_546, D_547]: (k2_partfun1(A_544, B_545, C_546, D_547)=k7_relat_1(C_546, D_547) | ~m1_subset_1(C_546, k1_zfmisc_1(k2_zfmisc_1(A_544, B_545))) | ~v1_funct_1(C_546))), inference(cnfTransformation, [status(thm)], [f_132])).
% 16.24/8.36  tff(c_3923, plain, (![D_547]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_547)=k7_relat_1('#skF_5', D_547) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_76, c_3921])).
% 16.24/8.36  tff(c_3928, plain, (![D_547]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_547)=k7_relat_1('#skF_5', D_547))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_3923])).
% 16.24/8.36  tff(c_3925, plain, (![D_547]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_547)=k7_relat_1('#skF_6', D_547) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_70, c_3921])).
% 16.24/8.36  tff(c_3931, plain, (![D_547]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_547)=k7_relat_1('#skF_6', D_547))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_3925])).
% 16.24/8.36  tff(c_1810, plain, (![A_378, B_379, C_380]: (k9_subset_1(A_378, B_379, C_380)=k3_xboole_0(B_379, C_380) | ~m1_subset_1(C_380, k1_zfmisc_1(A_378)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 16.24/8.36  tff(c_1822, plain, (![B_379]: (k9_subset_1('#skF_1', B_379, '#skF_4')=k3_xboole_0(B_379, '#skF_4'))), inference(resolution, [status(thm)], [c_84, c_1810])).
% 16.24/8.36  tff(c_68, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_256])).
% 16.24/8.36  tff(c_117, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_68])).
% 16.24/8.36  tff(c_1832, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1822, c_1822, c_117])).
% 16.24/8.36  tff(c_6471, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4792, c_3836, c_3928, c_3931, c_4134, c_4134, c_1832])).
% 16.24/8.36  tff(c_6472, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_68])).
% 16.24/8.36  tff(c_6597, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_6472])).
% 16.24/8.36  tff(c_30818, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_30807, c_6597])).
% 16.24/8.36  tff(c_30832, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_84, c_10932, c_11061, c_9926, c_11061, c_8310, c_8310, c_13173, c_30818])).
% 16.24/8.36  tff(c_30834, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_30832])).
% 16.24/8.36  tff(c_30835, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_6472])).
% 16.24/8.36  tff(c_30837, plain, (![B_1539, A_1540]: (r1_xboole_0(k1_relat_1(B_1539), A_1540) | k7_relat_1(B_1539, A_1540)!=k1_xboole_0 | ~v1_relat_1(B_1539))), inference(cnfTransformation, [status(thm)], [f_84])).
% 16.24/8.36  tff(c_30846, plain, (![A_1540]: (r1_xboole_0(k1_xboole_0, A_1540) | k7_relat_1(k1_xboole_0, A_1540)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_30837])).
% 16.24/8.36  tff(c_30850, plain, (![A_1540]: (r1_xboole_0(k1_xboole_0, A_1540) | k7_relat_1(k1_xboole_0, A_1540)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_107, c_30846])).
% 16.24/8.36  tff(c_31315, plain, (![B_1576, A_1577]: (k1_relat_1(B_1576)=A_1577 | ~v1_partfun1(B_1576, A_1577) | ~v4_relat_1(B_1576, A_1577) | ~v1_relat_1(B_1576))), inference(cnfTransformation, [status(thm)], [f_126])).
% 16.24/8.36  tff(c_31318, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_6541, c_31315])).
% 16.24/8.36  tff(c_31324, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6488, c_31318])).
% 16.24/8.36  tff(c_31328, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_31324])).
% 16.24/8.36  tff(c_31770, plain, (![C_1614, A_1615, B_1616]: (v1_partfun1(C_1614, A_1615) | ~v1_funct_2(C_1614, A_1615, B_1616) | ~v1_funct_1(C_1614) | ~m1_subset_1(C_1614, k1_zfmisc_1(k2_zfmisc_1(A_1615, B_1616))) | v1_xboole_0(B_1616))), inference(cnfTransformation, [status(thm)], [f_118])).
% 16.24/8.36  tff(c_31776, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_70, c_31770])).
% 16.24/8.36  tff(c_31783, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_31776])).
% 16.24/8.36  tff(c_31785, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_31328, c_31783])).
% 16.24/8.36  tff(c_31786, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_31324])).
% 16.24/8.36  tff(c_31797, plain, (![B_22]: (k7_relat_1('#skF_6', B_22)=k1_xboole_0 | ~r1_xboole_0(B_22, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_31786, c_24])).
% 16.24/8.36  tff(c_32235, plain, (![B_1643]: (k7_relat_1('#skF_6', B_1643)=k1_xboole_0 | ~r1_xboole_0(B_1643, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6488, c_31797])).
% 16.24/8.36  tff(c_32281, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0 | k7_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_30850, c_32235])).
% 16.24/8.36  tff(c_33732, plain, (k7_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32281])).
% 16.24/8.36  tff(c_31794, plain, (![A_13]: (r1_xboole_0('#skF_4', A_13) | k9_relat_1('#skF_6', A_13)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_31786, c_20])).
% 16.24/8.36  tff(c_32284, plain, (![A_1644]: (r1_xboole_0('#skF_4', A_1644) | k9_relat_1('#skF_6', A_1644)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6488, c_31794])).
% 16.24/8.36  tff(c_30973, plain, (![A_1551, B_1552]: (k7_relat_1(A_1551, B_1552)=k1_xboole_0 | ~r1_xboole_0(B_1552, k1_relat_1(A_1551)) | ~v1_relat_1(A_1551))), inference(cnfTransformation, [status(thm)], [f_71])).
% 16.24/8.36  tff(c_30992, plain, (![B_1552]: (k7_relat_1(k1_xboole_0, B_1552)=k1_xboole_0 | ~r1_xboole_0(B_1552, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_30973])).
% 16.24/8.36  tff(c_30998, plain, (![B_1552]: (k7_relat_1(k1_xboole_0, B_1552)=k1_xboole_0 | ~r1_xboole_0(B_1552, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_30992])).
% 16.24/8.36  tff(c_32313, plain, (k7_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0 | k9_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_32284, c_30998])).
% 16.24/8.36  tff(c_33826, plain, (k9_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_33732, c_32313])).
% 16.24/8.36  tff(c_31321, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_6540, c_31315])).
% 16.24/8.36  tff(c_31327, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6487, c_31321])).
% 16.24/8.36  tff(c_31842, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_31327])).
% 16.24/8.36  tff(c_32055, plain, (![C_1633, A_1634, B_1635]: (v1_partfun1(C_1633, A_1634) | ~v1_funct_2(C_1633, A_1634, B_1635) | ~v1_funct_1(C_1633) | ~m1_subset_1(C_1633, k1_zfmisc_1(k2_zfmisc_1(A_1634, B_1635))) | v1_xboole_0(B_1635))), inference(cnfTransformation, [status(thm)], [f_118])).
% 16.24/8.36  tff(c_32058, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_76, c_32055])).
% 16.24/8.36  tff(c_32064, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_32058])).
% 16.24/8.36  tff(c_32066, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_31842, c_32064])).
% 16.24/8.36  tff(c_32067, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_31327])).
% 16.24/8.36  tff(c_32087, plain, (![A_13]: (k9_relat_1('#skF_5', A_13)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_13) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_32067, c_18])).
% 16.24/8.36  tff(c_32338, plain, (![A_1647]: (k9_relat_1('#skF_5', A_1647)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_1647))), inference(demodulation, [status(thm), theory('equality')], [c_6487, c_32087])).
% 16.24/8.36  tff(c_32348, plain, (![B_28]: (k9_relat_1('#skF_5', B_28)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_28) | v1_xboole_0(B_28) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_32338])).
% 16.24/8.36  tff(c_33741, plain, (![B_1770]: (k9_relat_1('#skF_5', B_1770)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_1770) | v1_xboole_0(B_1770))), inference(negUnitSimplification, [status(thm)], [c_90, c_32348])).
% 16.24/8.36  tff(c_33744, plain, (k9_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_82, c_33741])).
% 16.24/8.36  tff(c_33747, plain, (k9_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_86, c_33744])).
% 16.24/8.36  tff(c_32075, plain, (![A_13]: (r1_xboole_0('#skF_3', A_13) | k9_relat_1('#skF_5', A_13)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_32067, c_20])).
% 16.24/8.36  tff(c_32162, plain, (![A_1638]: (r1_xboole_0('#skF_3', A_1638) | k9_relat_1('#skF_5', A_1638)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6487, c_32075])).
% 16.24/8.36  tff(c_33959, plain, (![A_1789]: (k3_xboole_0('#skF_3', A_1789)=k1_xboole_0 | k9_relat_1('#skF_5', A_1789)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_32162, c_2])).
% 16.24/8.36  tff(c_33976, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_33747, c_33959])).
% 16.24/8.36  tff(c_34003, plain, (![A_1791]: (k7_relat_1('#skF_6', A_1791)=k1_xboole_0 | k3_xboole_0(A_1791, '#skF_4')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_32235])).
% 16.24/8.36  tff(c_34024, plain, (![A_1791]: (r1_tarski(k1_relat_1(k1_xboole_0), A_1791) | ~v1_relat_1('#skF_6') | k3_xboole_0(A_1791, '#skF_4')!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_34003, c_30])).
% 16.24/8.36  tff(c_34044, plain, (![A_1791]: (r1_tarski(k1_xboole_0, A_1791) | k3_xboole_0(A_1791, '#skF_4')!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6488, c_28, c_34024])).
% 16.24/8.36  tff(c_31803, plain, (![A_25]: (r1_xboole_0('#skF_4', A_25) | k7_relat_1('#skF_6', A_25)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_31786, c_34])).
% 16.24/8.36  tff(c_31821, plain, (![A_25]: (r1_xboole_0('#skF_4', A_25) | k7_relat_1('#skF_6', A_25)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6488, c_31803])).
% 16.24/8.36  tff(c_32078, plain, (![B_22]: (k7_relat_1('#skF_5', B_22)=k1_xboole_0 | ~r1_xboole_0(B_22, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_32067, c_24])).
% 16.24/8.36  tff(c_32380, plain, (![B_1649]: (k7_relat_1('#skF_5', B_1649)=k1_xboole_0 | ~r1_xboole_0(B_1649, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6487, c_32078])).
% 16.24/8.36  tff(c_32424, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | k7_relat_1('#skF_6', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_31821, c_32380])).
% 16.24/8.36  tff(c_33618, plain, (k7_relat_1('#skF_6', '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32424])).
% 16.24/8.36  tff(c_32259, plain, (![A_27]: (k7_relat_1('#skF_6', A_27)=k1_xboole_0 | ~r1_subset_1(A_27, '#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(A_27))), inference(resolution, [status(thm)], [c_38, c_32235])).
% 16.24/8.36  tff(c_33619, plain, (![A_1761]: (k7_relat_1('#skF_6', A_1761)=k1_xboole_0 | ~r1_subset_1(A_1761, '#skF_4') | v1_xboole_0(A_1761))), inference(negUnitSimplification, [status(thm)], [c_86, c_32259])).
% 16.24/8.36  tff(c_33630, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_82, c_33619])).
% 16.24/8.36  tff(c_33639, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_33618, c_33630])).
% 16.24/8.36  tff(c_33641, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_32424])).
% 16.24/8.36  tff(c_33659, plain, (![B_18]: (k9_relat_1(k1_xboole_0, B_18)=k9_relat_1('#skF_6', B_18) | ~r1_tarski(B_18, '#skF_3') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_33641, c_22])).
% 16.24/8.36  tff(c_34464, plain, (![B_1815]: (k9_relat_1(k1_xboole_0, B_1815)=k9_relat_1('#skF_6', B_1815) | ~r1_tarski(B_1815, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6488, c_33659])).
% 16.24/8.36  tff(c_34468, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k9_relat_1('#skF_6', k1_xboole_0) | k3_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_34044, c_34464])).
% 16.24/8.36  tff(c_34498, plain, (k9_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_33976, c_6523, c_34468])).
% 16.24/8.36  tff(c_34500, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33826, c_34498])).
% 16.24/8.36  tff(c_34501, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_32281])).
% 16.24/8.36  tff(c_33640, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_32424])).
% 16.24/8.36  tff(c_32084, plain, (![A_25]: (r1_xboole_0('#skF_3', A_25) | k7_relat_1('#skF_5', A_25)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_32067, c_34])).
% 16.24/8.36  tff(c_32120, plain, (![A_1636]: (r1_xboole_0('#skF_3', A_1636) | k7_relat_1('#skF_5', A_1636)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6487, c_32084])).
% 16.24/8.36  tff(c_34708, plain, (![A_1835]: (k3_xboole_0('#skF_3', A_1835)=k1_xboole_0 | k7_relat_1('#skF_5', A_1835)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_32120, c_2])).
% 16.24/8.36  tff(c_34719, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_33640, c_34708])).
% 16.24/8.36  tff(c_31212, plain, (![A_1565, B_1566, C_1567]: (k9_subset_1(A_1565, B_1566, C_1567)=k3_xboole_0(B_1566, C_1567) | ~m1_subset_1(C_1567, k1_zfmisc_1(A_1565)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 16.24/8.36  tff(c_31224, plain, (![B_1566]: (k9_subset_1('#skF_1', B_1566, '#skF_4')=k3_xboole_0(B_1566, '#skF_4'))), inference(resolution, [status(thm)], [c_84, c_31212])).
% 16.24/8.36  tff(c_30851, plain, (![A_1541]: (r1_xboole_0(k1_xboole_0, A_1541) | k7_relat_1(k1_xboole_0, A_1541)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_107, c_30846])).
% 16.24/8.36  tff(c_30858, plain, (![A_1541]: (k9_relat_1(k1_xboole_0, A_1541)=k1_xboole_0 | k7_relat_1(k1_xboole_0, A_1541)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_30851, c_6561])).
% 16.24/8.36  tff(c_31049, plain, (![B_1557, A_1558]: (r1_xboole_0(k1_relat_1(B_1557), A_1558) | k9_relat_1(B_1557, A_1558)!=k1_xboole_0 | ~v1_relat_1(B_1557))), inference(cnfTransformation, [status(thm)], [f_57])).
% 16.24/8.36  tff(c_31069, plain, (![A_1558]: (r1_xboole_0(k1_xboole_0, A_1558) | k9_relat_1(k1_xboole_0, A_1558)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_31049])).
% 16.24/8.36  tff(c_31076, plain, (![A_1558]: (r1_xboole_0(k1_xboole_0, A_1558) | k9_relat_1(k1_xboole_0, A_1558)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_107, c_31069])).
% 16.24/8.36  tff(c_32426, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0 | k9_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_31076, c_32380])).
% 16.24/8.36  tff(c_32500, plain, (k9_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32426])).
% 16.24/8.36  tff(c_32507, plain, (k7_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_30858, c_32500])).
% 16.24/8.36  tff(c_32180, plain, (k7_relat_1(k1_xboole_0, '#skF_3')=k1_xboole_0 | k9_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_32162, c_30998])).
% 16.24/8.36  tff(c_33169, plain, (k9_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_32507, c_32180])).
% 16.24/8.36  tff(c_32571, plain, (k7_relat_1('#skF_6', '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32424])).
% 16.24/8.36  tff(c_32700, plain, (![A_1687]: (k7_relat_1('#skF_6', A_1687)=k1_xboole_0 | ~r1_subset_1(A_1687, '#skF_4') | v1_xboole_0(A_1687))), inference(negUnitSimplification, [status(thm)], [c_86, c_32259])).
% 16.24/8.36  tff(c_32715, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_82, c_32700])).
% 16.24/8.36  tff(c_32727, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_32571, c_32715])).
% 16.24/8.36  tff(c_32729, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_32424])).
% 16.24/8.36  tff(c_32141, plain, (![A_1637]: (r1_xboole_0('#skF_4', A_1637) | k7_relat_1('#skF_6', A_1637)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6488, c_31803])).
% 16.24/8.36  tff(c_32933, plain, (![A_1705]: (k3_xboole_0('#skF_4', A_1705)=k1_xboole_0 | k7_relat_1('#skF_6', A_1705)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_32141, c_2])).
% 16.24/8.36  tff(c_32937, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_32729, c_32933])).
% 16.24/8.36  tff(c_32968, plain, (![A_1713]: (k7_relat_1('#skF_5', A_1713)=k1_xboole_0 | k3_xboole_0(A_1713, '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_32380])).
% 16.24/8.36  tff(c_32989, plain, (![A_1713]: (r1_tarski(k1_relat_1(k1_xboole_0), A_1713) | ~v1_relat_1('#skF_5') | k3_xboole_0(A_1713, '#skF_3')!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32968, c_30])).
% 16.24/8.36  tff(c_33009, plain, (![A_1713]: (r1_tarski(k1_xboole_0, A_1713) | k3_xboole_0(A_1713, '#skF_3')!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6487, c_28, c_32989])).
% 16.24/8.36  tff(c_32728, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_32424])).
% 16.24/8.36  tff(c_32733, plain, (![B_18]: (k9_relat_1(k1_xboole_0, B_18)=k9_relat_1('#skF_5', B_18) | ~r1_tarski(B_18, '#skF_4') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_32728, c_22])).
% 16.24/8.36  tff(c_33393, plain, (![B_1744]: (k9_relat_1(k1_xboole_0, B_1744)=k9_relat_1('#skF_5', B_1744) | ~r1_tarski(B_1744, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6487, c_32733])).
% 16.24/8.36  tff(c_33405, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k9_relat_1('#skF_5', k1_xboole_0) | k3_xboole_0('#skF_4', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_33009, c_33393])).
% 16.24/8.36  tff(c_33433, plain, (k9_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32937, c_6523, c_33405])).
% 16.24/8.36  tff(c_33435, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33169, c_33433])).
% 16.24/8.36  tff(c_33436, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_32426])).
% 16.24/8.36  tff(c_32434, plain, (![A_1650, B_1651, C_1652, D_1653]: (k2_partfun1(A_1650, B_1651, C_1652, D_1653)=k7_relat_1(C_1652, D_1653) | ~m1_subset_1(C_1652, k1_zfmisc_1(k2_zfmisc_1(A_1650, B_1651))) | ~v1_funct_1(C_1652))), inference(cnfTransformation, [status(thm)], [f_132])).
% 16.24/8.36  tff(c_32436, plain, (![D_1653]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_1653)=k7_relat_1('#skF_5', D_1653) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_76, c_32434])).
% 16.24/8.36  tff(c_32441, plain, (![D_1653]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_1653)=k7_relat_1('#skF_5', D_1653))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_32436])).
% 16.24/8.36  tff(c_32438, plain, (![D_1653]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_1653)=k7_relat_1('#skF_6', D_1653) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_70, c_32434])).
% 16.24/8.36  tff(c_32444, plain, (![D_1653]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_1653)=k7_relat_1('#skF_6', D_1653))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_32438])).
% 16.24/8.36  tff(c_33515, plain, (![F_1749, E_1746, A_1748, B_1745, D_1747, C_1750]: (v1_funct_1(k1_tmap_1(A_1748, B_1745, C_1750, D_1747, E_1746, F_1749)) | ~m1_subset_1(F_1749, k1_zfmisc_1(k2_zfmisc_1(D_1747, B_1745))) | ~v1_funct_2(F_1749, D_1747, B_1745) | ~v1_funct_1(F_1749) | ~m1_subset_1(E_1746, k1_zfmisc_1(k2_zfmisc_1(C_1750, B_1745))) | ~v1_funct_2(E_1746, C_1750, B_1745) | ~v1_funct_1(E_1746) | ~m1_subset_1(D_1747, k1_zfmisc_1(A_1748)) | v1_xboole_0(D_1747) | ~m1_subset_1(C_1750, k1_zfmisc_1(A_1748)) | v1_xboole_0(C_1750) | v1_xboole_0(B_1745) | v1_xboole_0(A_1748))), inference(cnfTransformation, [status(thm)], [f_214])).
% 16.24/8.36  tff(c_33519, plain, (![A_1748, C_1750, E_1746]: (v1_funct_1(k1_tmap_1(A_1748, '#skF_2', C_1750, '#skF_4', E_1746, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1746, k1_zfmisc_1(k2_zfmisc_1(C_1750, '#skF_2'))) | ~v1_funct_2(E_1746, C_1750, '#skF_2') | ~v1_funct_1(E_1746) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1748)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1750, k1_zfmisc_1(A_1748)) | v1_xboole_0(C_1750) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1748))), inference(resolution, [status(thm)], [c_70, c_33515])).
% 16.24/8.36  tff(c_33526, plain, (![A_1748, C_1750, E_1746]: (v1_funct_1(k1_tmap_1(A_1748, '#skF_2', C_1750, '#skF_4', E_1746, '#skF_6')) | ~m1_subset_1(E_1746, k1_zfmisc_1(k2_zfmisc_1(C_1750, '#skF_2'))) | ~v1_funct_2(E_1746, C_1750, '#skF_2') | ~v1_funct_1(E_1746) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1748)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1750, k1_zfmisc_1(A_1748)) | v1_xboole_0(C_1750) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1748))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_33519])).
% 16.24/8.36  tff(c_35845, plain, (![A_1882, C_1883, E_1884]: (v1_funct_1(k1_tmap_1(A_1882, '#skF_2', C_1883, '#skF_4', E_1884, '#skF_6')) | ~m1_subset_1(E_1884, k1_zfmisc_1(k2_zfmisc_1(C_1883, '#skF_2'))) | ~v1_funct_2(E_1884, C_1883, '#skF_2') | ~v1_funct_1(E_1884) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1882)) | ~m1_subset_1(C_1883, k1_zfmisc_1(A_1882)) | v1_xboole_0(C_1883) | v1_xboole_0(A_1882))), inference(negUnitSimplification, [status(thm)], [c_92, c_86, c_33526])).
% 16.24/8.36  tff(c_35850, plain, (![A_1882]: (v1_funct_1(k1_tmap_1(A_1882, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1882)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1882)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1882))), inference(resolution, [status(thm)], [c_76, c_35845])).
% 16.24/8.36  tff(c_35858, plain, (![A_1882]: (v1_funct_1(k1_tmap_1(A_1882, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1882)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1882)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1882))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_35850])).
% 16.24/8.36  tff(c_36460, plain, (![A_1903]: (v1_funct_1(k1_tmap_1(A_1903, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1903)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1903)) | v1_xboole_0(A_1903))), inference(negUnitSimplification, [status(thm)], [c_90, c_35858])).
% 16.24/8.36  tff(c_36463, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_88, c_36460])).
% 16.24/8.36  tff(c_36466, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_36463])).
% 16.24/8.36  tff(c_36467, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_94, c_36466])).
% 16.24/8.36  tff(c_34566, plain, (![B_1820, E_1818, D_1816, C_1819, F_1821, A_1817]: (k2_partfun1(k4_subset_1(A_1817, C_1819, D_1816), B_1820, k1_tmap_1(A_1817, B_1820, C_1819, D_1816, E_1818, F_1821), C_1819)=E_1818 | ~m1_subset_1(k1_tmap_1(A_1817, B_1820, C_1819, D_1816, E_1818, F_1821), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1817, C_1819, D_1816), B_1820))) | ~v1_funct_2(k1_tmap_1(A_1817, B_1820, C_1819, D_1816, E_1818, F_1821), k4_subset_1(A_1817, C_1819, D_1816), B_1820) | ~v1_funct_1(k1_tmap_1(A_1817, B_1820, C_1819, D_1816, E_1818, F_1821)) | k2_partfun1(D_1816, B_1820, F_1821, k9_subset_1(A_1817, C_1819, D_1816))!=k2_partfun1(C_1819, B_1820, E_1818, k9_subset_1(A_1817, C_1819, D_1816)) | ~m1_subset_1(F_1821, k1_zfmisc_1(k2_zfmisc_1(D_1816, B_1820))) | ~v1_funct_2(F_1821, D_1816, B_1820) | ~v1_funct_1(F_1821) | ~m1_subset_1(E_1818, k1_zfmisc_1(k2_zfmisc_1(C_1819, B_1820))) | ~v1_funct_2(E_1818, C_1819, B_1820) | ~v1_funct_1(E_1818) | ~m1_subset_1(D_1816, k1_zfmisc_1(A_1817)) | v1_xboole_0(D_1816) | ~m1_subset_1(C_1819, k1_zfmisc_1(A_1817)) | v1_xboole_0(C_1819) | v1_xboole_0(B_1820) | v1_xboole_0(A_1817))), inference(cnfTransformation, [status(thm)], [f_180])).
% 16.24/8.36  tff(c_42141, plain, (![D_2075, B_2073, E_2074, A_2076, C_2078, F_2077]: (k2_partfun1(k4_subset_1(A_2076, C_2078, D_2075), B_2073, k1_tmap_1(A_2076, B_2073, C_2078, D_2075, E_2074, F_2077), C_2078)=E_2074 | ~v1_funct_2(k1_tmap_1(A_2076, B_2073, C_2078, D_2075, E_2074, F_2077), k4_subset_1(A_2076, C_2078, D_2075), B_2073) | ~v1_funct_1(k1_tmap_1(A_2076, B_2073, C_2078, D_2075, E_2074, F_2077)) | k2_partfun1(D_2075, B_2073, F_2077, k9_subset_1(A_2076, C_2078, D_2075))!=k2_partfun1(C_2078, B_2073, E_2074, k9_subset_1(A_2076, C_2078, D_2075)) | ~m1_subset_1(F_2077, k1_zfmisc_1(k2_zfmisc_1(D_2075, B_2073))) | ~v1_funct_2(F_2077, D_2075, B_2073) | ~v1_funct_1(F_2077) | ~m1_subset_1(E_2074, k1_zfmisc_1(k2_zfmisc_1(C_2078, B_2073))) | ~v1_funct_2(E_2074, C_2078, B_2073) | ~v1_funct_1(E_2074) | ~m1_subset_1(D_2075, k1_zfmisc_1(A_2076)) | v1_xboole_0(D_2075) | ~m1_subset_1(C_2078, k1_zfmisc_1(A_2076)) | v1_xboole_0(C_2078) | v1_xboole_0(B_2073) | v1_xboole_0(A_2076))), inference(resolution, [status(thm)], [c_62, c_34566])).
% 16.24/8.36  tff(c_48401, plain, (![D_2194, B_2192, E_2193, F_2196, A_2195, C_2197]: (k2_partfun1(k4_subset_1(A_2195, C_2197, D_2194), B_2192, k1_tmap_1(A_2195, B_2192, C_2197, D_2194, E_2193, F_2196), C_2197)=E_2193 | ~v1_funct_1(k1_tmap_1(A_2195, B_2192, C_2197, D_2194, E_2193, F_2196)) | k2_partfun1(D_2194, B_2192, F_2196, k9_subset_1(A_2195, C_2197, D_2194))!=k2_partfun1(C_2197, B_2192, E_2193, k9_subset_1(A_2195, C_2197, D_2194)) | ~m1_subset_1(F_2196, k1_zfmisc_1(k2_zfmisc_1(D_2194, B_2192))) | ~v1_funct_2(F_2196, D_2194, B_2192) | ~v1_funct_1(F_2196) | ~m1_subset_1(E_2193, k1_zfmisc_1(k2_zfmisc_1(C_2197, B_2192))) | ~v1_funct_2(E_2193, C_2197, B_2192) | ~v1_funct_1(E_2193) | ~m1_subset_1(D_2194, k1_zfmisc_1(A_2195)) | v1_xboole_0(D_2194) | ~m1_subset_1(C_2197, k1_zfmisc_1(A_2195)) | v1_xboole_0(C_2197) | v1_xboole_0(B_2192) | v1_xboole_0(A_2195))), inference(resolution, [status(thm)], [c_64, c_42141])).
% 16.24/8.36  tff(c_48407, plain, (![A_2195, C_2197, E_2193]: (k2_partfun1(k4_subset_1(A_2195, C_2197, '#skF_4'), '#skF_2', k1_tmap_1(A_2195, '#skF_2', C_2197, '#skF_4', E_2193, '#skF_6'), C_2197)=E_2193 | ~v1_funct_1(k1_tmap_1(A_2195, '#skF_2', C_2197, '#skF_4', E_2193, '#skF_6')) | k2_partfun1(C_2197, '#skF_2', E_2193, k9_subset_1(A_2195, C_2197, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_2195, C_2197, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_2193, k1_zfmisc_1(k2_zfmisc_1(C_2197, '#skF_2'))) | ~v1_funct_2(E_2193, C_2197, '#skF_2') | ~v1_funct_1(E_2193) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2195)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_2197, k1_zfmisc_1(A_2195)) | v1_xboole_0(C_2197) | v1_xboole_0('#skF_2') | v1_xboole_0(A_2195))), inference(resolution, [status(thm)], [c_70, c_48401])).
% 16.24/8.36  tff(c_48415, plain, (![A_2195, C_2197, E_2193]: (k2_partfun1(k4_subset_1(A_2195, C_2197, '#skF_4'), '#skF_2', k1_tmap_1(A_2195, '#skF_2', C_2197, '#skF_4', E_2193, '#skF_6'), C_2197)=E_2193 | ~v1_funct_1(k1_tmap_1(A_2195, '#skF_2', C_2197, '#skF_4', E_2193, '#skF_6')) | k2_partfun1(C_2197, '#skF_2', E_2193, k9_subset_1(A_2195, C_2197, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2195, C_2197, '#skF_4')) | ~m1_subset_1(E_2193, k1_zfmisc_1(k2_zfmisc_1(C_2197, '#skF_2'))) | ~v1_funct_2(E_2193, C_2197, '#skF_2') | ~v1_funct_1(E_2193) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2195)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_2197, k1_zfmisc_1(A_2195)) | v1_xboole_0(C_2197) | v1_xboole_0('#skF_2') | v1_xboole_0(A_2195))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_32444, c_48407])).
% 16.24/8.36  tff(c_52774, plain, (![A_2261, C_2262, E_2263]: (k2_partfun1(k4_subset_1(A_2261, C_2262, '#skF_4'), '#skF_2', k1_tmap_1(A_2261, '#skF_2', C_2262, '#skF_4', E_2263, '#skF_6'), C_2262)=E_2263 | ~v1_funct_1(k1_tmap_1(A_2261, '#skF_2', C_2262, '#skF_4', E_2263, '#skF_6')) | k2_partfun1(C_2262, '#skF_2', E_2263, k9_subset_1(A_2261, C_2262, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2261, C_2262, '#skF_4')) | ~m1_subset_1(E_2263, k1_zfmisc_1(k2_zfmisc_1(C_2262, '#skF_2'))) | ~v1_funct_2(E_2263, C_2262, '#skF_2') | ~v1_funct_1(E_2263) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2261)) | ~m1_subset_1(C_2262, k1_zfmisc_1(A_2261)) | v1_xboole_0(C_2262) | v1_xboole_0(A_2261))), inference(negUnitSimplification, [status(thm)], [c_92, c_86, c_48415])).
% 16.24/8.36  tff(c_52779, plain, (![A_2261]: (k2_partfun1(k4_subset_1(A_2261, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_2261, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_2261, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_2261, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2261, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2261)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_2261)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2261))), inference(resolution, [status(thm)], [c_76, c_52774])).
% 16.24/8.36  tff(c_52787, plain, (![A_2261]: (k2_partfun1(k4_subset_1(A_2261, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_2261, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_2261, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_2261, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2261, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2261)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_2261)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2261))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_32441, c_52779])).
% 16.24/8.36  tff(c_53907, plain, (![A_2270]: (k2_partfun1(k4_subset_1(A_2270, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_2270, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_2270, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_2270, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2270, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2270)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_2270)) | v1_xboole_0(A_2270))), inference(negUnitSimplification, [status(thm)], [c_90, c_52787])).
% 16.24/8.36  tff(c_30836, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6'), inference(splitRight, [status(thm)], [c_6472])).
% 16.24/8.36  tff(c_34863, plain, (![C_1842, A_1841, B_1843, D_1840, G_1839]: (k1_tmap_1(A_1841, B_1843, C_1842, D_1840, k2_partfun1(k4_subset_1(A_1841, C_1842, D_1840), B_1843, G_1839, C_1842), k2_partfun1(k4_subset_1(A_1841, C_1842, D_1840), B_1843, G_1839, D_1840))=G_1839 | ~m1_subset_1(G_1839, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1841, C_1842, D_1840), B_1843))) | ~v1_funct_2(G_1839, k4_subset_1(A_1841, C_1842, D_1840), B_1843) | ~v1_funct_1(G_1839) | k2_partfun1(D_1840, B_1843, k2_partfun1(k4_subset_1(A_1841, C_1842, D_1840), B_1843, G_1839, D_1840), k9_subset_1(A_1841, C_1842, D_1840))!=k2_partfun1(C_1842, B_1843, k2_partfun1(k4_subset_1(A_1841, C_1842, D_1840), B_1843, G_1839, C_1842), k9_subset_1(A_1841, C_1842, D_1840)) | ~m1_subset_1(k2_partfun1(k4_subset_1(A_1841, C_1842, D_1840), B_1843, G_1839, D_1840), k1_zfmisc_1(k2_zfmisc_1(D_1840, B_1843))) | ~v1_funct_2(k2_partfun1(k4_subset_1(A_1841, C_1842, D_1840), B_1843, G_1839, D_1840), D_1840, B_1843) | ~v1_funct_1(k2_partfun1(k4_subset_1(A_1841, C_1842, D_1840), B_1843, G_1839, D_1840)) | ~m1_subset_1(k2_partfun1(k4_subset_1(A_1841, C_1842, D_1840), B_1843, G_1839, C_1842), k1_zfmisc_1(k2_zfmisc_1(C_1842, B_1843))) | ~v1_funct_2(k2_partfun1(k4_subset_1(A_1841, C_1842, D_1840), B_1843, G_1839, C_1842), C_1842, B_1843) | ~v1_funct_1(k2_partfun1(k4_subset_1(A_1841, C_1842, D_1840), B_1843, G_1839, C_1842)) | ~m1_subset_1(D_1840, k1_zfmisc_1(A_1841)) | v1_xboole_0(D_1840) | ~m1_subset_1(C_1842, k1_zfmisc_1(A_1841)) | v1_xboole_0(C_1842) | v1_xboole_0(B_1843) | v1_xboole_0(A_1841))), inference(cnfTransformation, [status(thm)], [f_180])).
% 16.24/8.36  tff(c_34865, plain, (k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4'))=k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6') | ~m1_subset_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2'))) | ~v1_funct_2(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4'), k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_2(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')) | ~m1_subset_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_30836, c_34863])).
% 16.24/8.36  tff(c_34867, plain, (k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_6')=k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6') | ~m1_subset_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2'))) | ~v1_funct_2(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k1_xboole_0)!=k1_xboole_0 | ~m1_subset_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')) | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_84, c_74, c_30836, c_72, c_30836, c_70, c_34501, c_34719, c_34719, c_32444, c_30836, c_31224, c_31224, c_30836, c_34865])).
% 16.24/8.36  tff(c_34868, plain, (k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_6')=k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6') | ~m1_subset_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2'))) | ~v1_funct_2(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k1_xboole_0)!=k1_xboole_0 | ~m1_subset_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_94, c_92, c_90, c_86, c_34867])).
% 16.24/8.36  tff(c_37379, plain, (k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_6')=k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6') | ~m1_subset_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2'))) | ~v1_funct_2(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | k2_partfun1('#skF_3', '#skF_2', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k1_xboole_0)!=k1_xboole_0 | ~m1_subset_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36467, c_34868])).
% 16.24/8.36  tff(c_37380, plain, (~v1_funct_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_37379])).
% 16.24/8.36  tff(c_53916, plain, (~v1_funct_1('#skF_5') | ~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_53907, c_37380])).
% 16.24/8.36  tff(c_53929, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_84, c_34501, c_34719, c_33436, c_34719, c_31224, c_31224, c_36467, c_80, c_53916])).
% 16.24/8.36  tff(c_53931, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_53929])).
% 16.24/8.36  tff(c_53932, plain, (~v1_funct_2(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | k2_partfun1('#skF_3', '#skF_2', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k1_xboole_0)!=k1_xboole_0 | ~v1_funct_2(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2'))) | k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_6')=k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_37379])).
% 16.24/8.36  tff(c_54364, plain, (~m1_subset_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2')))), inference(splitLeft, [status(thm)], [c_53932])).
% 16.24/8.36  tff(c_54367, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_62, c_54364])).
% 16.24/8.36  tff(c_54370, plain, (v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_84, c_80, c_78, c_76, c_74, c_72, c_70, c_54367])).
% 16.24/8.36  tff(c_54372, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_92, c_90, c_86, c_54370])).
% 16.24/8.36  tff(c_54374, plain, (m1_subset_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2')))), inference(splitRight, [status(thm)], [c_53932])).
% 16.24/8.36  tff(c_60, plain, (![E_165, D_157, A_45, C_141, B_109, F_169]: (k2_partfun1(k4_subset_1(A_45, C_141, D_157), B_109, k1_tmap_1(A_45, B_109, C_141, D_157, E_165, F_169), C_141)=E_165 | ~m1_subset_1(k1_tmap_1(A_45, B_109, C_141, D_157, E_165, F_169), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_45, C_141, D_157), B_109))) | ~v1_funct_2(k1_tmap_1(A_45, B_109, C_141, D_157, E_165, F_169), k4_subset_1(A_45, C_141, D_157), B_109) | ~v1_funct_1(k1_tmap_1(A_45, B_109, C_141, D_157, E_165, F_169)) | k2_partfun1(D_157, B_109, F_169, k9_subset_1(A_45, C_141, D_157))!=k2_partfun1(C_141, B_109, E_165, k9_subset_1(A_45, C_141, D_157)) | ~m1_subset_1(F_169, k1_zfmisc_1(k2_zfmisc_1(D_157, B_109))) | ~v1_funct_2(F_169, D_157, B_109) | ~v1_funct_1(F_169) | ~m1_subset_1(E_165, k1_zfmisc_1(k2_zfmisc_1(C_141, B_109))) | ~v1_funct_2(E_165, C_141, B_109) | ~v1_funct_1(E_165) | ~m1_subset_1(D_157, k1_zfmisc_1(A_45)) | v1_xboole_0(D_157) | ~m1_subset_1(C_141, k1_zfmisc_1(A_45)) | v1_xboole_0(C_141) | v1_xboole_0(B_109) | v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_180])).
% 16.24/8.36  tff(c_54382, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_2(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_54374, c_60])).
% 16.24/8.36  tff(c_54416, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_2(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_84, c_80, c_78, c_76, c_74, c_72, c_70, c_34501, c_34719, c_31224, c_33436, c_34719, c_31224, c_32441, c_32444, c_36467, c_54382])).
% 16.24/8.36  tff(c_54417, plain, (~v1_funct_2(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_94, c_92, c_90, c_86, c_30835, c_54416])).
% 16.24/8.36  tff(c_54528, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_64, c_54417])).
% 16.24/8.36  tff(c_54531, plain, (v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_84, c_80, c_78, c_76, c_74, c_72, c_70, c_54528])).
% 16.24/8.36  tff(c_54533, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_92, c_90, c_86, c_54531])).
% 16.24/8.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.24/8.36  
% 16.24/8.36  Inference rules
% 16.24/8.36  ----------------------
% 16.24/8.36  #Ref     : 0
% 16.24/8.36  #Sup     : 10945
% 16.24/8.36  #Fact    : 0
% 16.24/8.36  #Define  : 0
% 16.24/8.36  #Split   : 59
% 16.24/8.36  #Chain   : 0
% 16.24/8.36  #Close   : 0
% 16.24/8.36  
% 16.24/8.36  Ordering : KBO
% 16.24/8.36  
% 16.24/8.36  Simplification rules
% 16.24/8.36  ----------------------
% 16.24/8.36  #Subsume      : 1670
% 16.24/8.36  #Demod        : 22061
% 16.24/8.36  #Tautology    : 6286
% 16.24/8.36  #SimpNegUnit  : 763
% 16.24/8.36  #BackRed      : 20
% 16.24/8.36  
% 16.24/8.36  #Partial instantiations: 0
% 16.24/8.36  #Strategies tried      : 1
% 16.24/8.36  
% 16.24/8.36  Timing (in seconds)
% 16.24/8.36  ----------------------
% 16.24/8.36  Preprocessing        : 0.43
% 16.24/8.36  Parsing              : 0.21
% 16.24/8.36  CNF conversion       : 0.06
% 16.24/8.36  Main loop            : 6.99
% 16.24/8.36  Inferencing          : 1.74
% 16.24/8.36  Reduction            : 2.68
% 16.24/8.36  Demodulation         : 2.05
% 16.24/8.37  BG Simplification    : 0.15
% 16.24/8.37  Subsumption          : 2.09
% 16.24/8.37  Abstraction          : 0.20
% 16.24/8.37  MUC search           : 0.00
% 16.24/8.37  Cooper               : 0.00
% 16.24/8.37  Total                : 7.59
% 16.24/8.37  Index Insertion      : 0.00
% 16.24/8.37  Index Deletion       : 0.00
% 16.24/8.37  Index Matching       : 0.00
% 16.24/8.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
