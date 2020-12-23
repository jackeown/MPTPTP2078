%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:09 EST 2020

% Result     : Theorem 19.00s
% Output     : CNFRefutation 19.21s
% Verified   : 
% Statistics : Number of formulae       :  248 ( 755 expanded)
%              Number of leaves         :   47 ( 289 expanded)
%              Depth                    :   12
%              Number of atoms          :  779 (3896 expanded)
%              Number of equality atoms :  149 ( 696 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_238,negated_conjecture,(
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

tff(f_37,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_76,axiom,(
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

tff(f_196,axiom,(
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

tff(f_114,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_162,axiom,(
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

tff(c_86,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_80,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_76,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_12,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_62,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_2224,plain,(
    ! [C_468,A_469,B_470] :
      ( v1_relat_1(C_468)
      | ~ m1_subset_1(C_468,k1_zfmisc_1(k2_zfmisc_1(A_469,B_470))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2236,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_2224])).

tff(c_84,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_2290,plain,(
    ! [C_484,A_485,B_486] :
      ( v4_relat_1(C_484,A_485)
      | ~ m1_subset_1(C_484,k1_zfmisc_1(k2_zfmisc_1(A_485,B_486))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2302,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_2290])).

tff(c_14235,plain,(
    ! [B_1730,A_1731] :
      ( k1_relat_1(B_1730) = A_1731
      | ~ v1_partfun1(B_1730,A_1731)
      | ~ v4_relat_1(B_1730,A_1731)
      | ~ v1_relat_1(B_1730) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_14244,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2302,c_14235])).

tff(c_14253,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2236,c_14244])).

tff(c_14957,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_14253])).

tff(c_66,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_64,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_15319,plain,(
    ! [C_1819,A_1820,B_1821] :
      ( v1_partfun1(C_1819,A_1820)
      | ~ v1_funct_2(C_1819,A_1820,B_1821)
      | ~ v1_funct_1(C_1819)
      | ~ m1_subset_1(C_1819,k1_zfmisc_1(k2_zfmisc_1(A_1820,B_1821)))
      | v1_xboole_0(B_1821) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_15326,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_15319])).

tff(c_15333,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_15326])).

tff(c_15335,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_14957,c_15333])).

tff(c_15336,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_14253])).

tff(c_10,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2304,plain,(
    ! [B_487,A_488] :
      ( k7_relat_1(B_487,A_488) = B_487
      | ~ r1_tarski(k1_relat_1(B_487),A_488)
      | ~ v1_relat_1(B_487) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2309,plain,(
    ! [B_487] :
      ( k7_relat_1(B_487,k1_relat_1(B_487)) = B_487
      | ~ v1_relat_1(B_487) ) ),
    inference(resolution,[status(thm)],[c_10,c_2304])).

tff(c_15344,plain,
    ( k7_relat_1('#skF_6','#skF_4') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_15336,c_2309])).

tff(c_15353,plain,(
    k7_relat_1('#skF_6','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2236,c_15344])).

tff(c_15393,plain,(
    ! [C_1826,A_1827,B_1828] :
      ( k7_relat_1(k7_relat_1(C_1826,A_1827),B_1828) = k1_xboole_0
      | ~ r1_xboole_0(A_1827,B_1828)
      | ~ v1_relat_1(C_1826) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_15418,plain,(
    ! [B_1828] :
      ( k7_relat_1('#skF_6',B_1828) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_1828)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15353,c_15393])).

tff(c_15439,plain,(
    ! [B_1829] :
      ( k7_relat_1('#skF_6',B_1829) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_1829) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2236,c_15418])).

tff(c_15456,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_15439])).

tff(c_68,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_2237,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_2224])).

tff(c_2303,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_2290])).

tff(c_14241,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2303,c_14235])).

tff(c_14250,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2237,c_14241])).

tff(c_14254,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_14250])).

tff(c_72,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_70,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_14910,plain,(
    ! [C_1793,A_1794,B_1795] :
      ( v1_partfun1(C_1793,A_1794)
      | ~ v1_funct_2(C_1793,A_1794,B_1795)
      | ~ v1_funct_1(C_1793)
      | ~ m1_subset_1(C_1793,k1_zfmisc_1(k2_zfmisc_1(A_1794,B_1795)))
      | v1_xboole_0(B_1795) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_14920,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_14910])).

tff(c_14928,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_14920])).

tff(c_14930,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_14254,c_14928])).

tff(c_14931,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_14250])).

tff(c_14939,plain,
    ( k7_relat_1('#skF_5','#skF_3') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_14931,c_2309])).

tff(c_14948,plain,(
    k7_relat_1('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2237,c_14939])).

tff(c_15421,plain,(
    ! [B_1828] :
      ( k7_relat_1('#skF_5',B_1828) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_1828)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14948,c_15393])).

tff(c_15466,plain,(
    ! [B_1830] :
      ( k7_relat_1('#skF_5',B_1830) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_1830) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2237,c_15421])).

tff(c_15483,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_15466])).

tff(c_82,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_78,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_74,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_14211,plain,(
    ! [A_1725,B_1726] :
      ( r1_xboole_0(A_1725,B_1726)
      | ~ r1_subset_1(A_1725,B_1726)
      | v1_xboole_0(B_1726)
      | v1_xboole_0(A_1725) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16119,plain,(
    ! [A_1888,B_1889] :
      ( k3_xboole_0(A_1888,B_1889) = k1_xboole_0
      | ~ r1_subset_1(A_1888,B_1889)
      | v1_xboole_0(B_1889)
      | v1_xboole_0(A_1888) ) ),
    inference(resolution,[status(thm)],[c_14211,c_2])).

tff(c_16122,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_16119])).

tff(c_16125,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_78,c_16122])).

tff(c_15556,plain,(
    ! [A_1835,B_1836,C_1837] :
      ( k9_subset_1(A_1835,B_1836,C_1837) = k3_xboole_0(B_1836,C_1837)
      | ~ m1_subset_1(C_1837,k1_zfmisc_1(A_1835)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_15571,plain,(
    ! [B_1836] : k9_subset_1('#skF_1',B_1836,'#skF_4') = k3_xboole_0(B_1836,'#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_15556])).

tff(c_15790,plain,(
    ! [E_1858,D_1856,B_1854,F_1855,A_1859,C_1857] :
      ( v1_funct_1(k1_tmap_1(A_1859,B_1854,C_1857,D_1856,E_1858,F_1855))
      | ~ m1_subset_1(F_1855,k1_zfmisc_1(k2_zfmisc_1(D_1856,B_1854)))
      | ~ v1_funct_2(F_1855,D_1856,B_1854)
      | ~ v1_funct_1(F_1855)
      | ~ m1_subset_1(E_1858,k1_zfmisc_1(k2_zfmisc_1(C_1857,B_1854)))
      | ~ v1_funct_2(E_1858,C_1857,B_1854)
      | ~ v1_funct_1(E_1858)
      | ~ m1_subset_1(D_1856,k1_zfmisc_1(A_1859))
      | v1_xboole_0(D_1856)
      | ~ m1_subset_1(C_1857,k1_zfmisc_1(A_1859))
      | v1_xboole_0(C_1857)
      | v1_xboole_0(B_1854)
      | v1_xboole_0(A_1859) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_15795,plain,(
    ! [A_1859,C_1857,E_1858] :
      ( v1_funct_1(k1_tmap_1(A_1859,'#skF_2',C_1857,'#skF_4',E_1858,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1858,k1_zfmisc_1(k2_zfmisc_1(C_1857,'#skF_2')))
      | ~ v1_funct_2(E_1858,C_1857,'#skF_2')
      | ~ v1_funct_1(E_1858)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1859))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1857,k1_zfmisc_1(A_1859))
      | v1_xboole_0(C_1857)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1859) ) ),
    inference(resolution,[status(thm)],[c_62,c_15790])).

tff(c_15801,plain,(
    ! [A_1859,C_1857,E_1858] :
      ( v1_funct_1(k1_tmap_1(A_1859,'#skF_2',C_1857,'#skF_4',E_1858,'#skF_6'))
      | ~ m1_subset_1(E_1858,k1_zfmisc_1(k2_zfmisc_1(C_1857,'#skF_2')))
      | ~ v1_funct_2(E_1858,C_1857,'#skF_2')
      | ~ v1_funct_1(E_1858)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1859))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1857,k1_zfmisc_1(A_1859))
      | v1_xboole_0(C_1857)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1859) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_15795])).

tff(c_16363,plain,(
    ! [A_1935,C_1936,E_1937] :
      ( v1_funct_1(k1_tmap_1(A_1935,'#skF_2',C_1936,'#skF_4',E_1937,'#skF_6'))
      | ~ m1_subset_1(E_1937,k1_zfmisc_1(k2_zfmisc_1(C_1936,'#skF_2')))
      | ~ v1_funct_2(E_1937,C_1936,'#skF_2')
      | ~ v1_funct_1(E_1937)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1935))
      | ~ m1_subset_1(C_1936,k1_zfmisc_1(A_1935))
      | v1_xboole_0(C_1936)
      | v1_xboole_0(A_1935) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_78,c_15801])).

tff(c_16373,plain,(
    ! [A_1935] :
      ( v1_funct_1(k1_tmap_1(A_1935,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1935))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1935))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1935) ) ),
    inference(resolution,[status(thm)],[c_68,c_16363])).

tff(c_16384,plain,(
    ! [A_1935] :
      ( v1_funct_1(k1_tmap_1(A_1935,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1935))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1935))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1935) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_16373])).

tff(c_16450,plain,(
    ! [A_1950] :
      ( v1_funct_1(k1_tmap_1(A_1950,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1950))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1950))
      | v1_xboole_0(A_1950) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_16384])).

tff(c_16457,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_80,c_16450])).

tff(c_16461,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_16457])).

tff(c_16462,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_16461])).

tff(c_15652,plain,(
    ! [A_1842,B_1843,C_1844,D_1845] :
      ( k2_partfun1(A_1842,B_1843,C_1844,D_1845) = k7_relat_1(C_1844,D_1845)
      | ~ m1_subset_1(C_1844,k1_zfmisc_1(k2_zfmisc_1(A_1842,B_1843)))
      | ~ v1_funct_1(C_1844) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_15659,plain,(
    ! [D_1845] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_1845) = k7_relat_1('#skF_5',D_1845)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_68,c_15652])).

tff(c_15666,plain,(
    ! [D_1845] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_1845) = k7_relat_1('#skF_5',D_1845) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_15659])).

tff(c_15657,plain,(
    ! [D_1845] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_1845) = k7_relat_1('#skF_6',D_1845)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_62,c_15652])).

tff(c_15663,plain,(
    ! [D_1845] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_1845) = k7_relat_1('#skF_6',D_1845) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_15657])).

tff(c_56,plain,(
    ! [D_169,E_170,A_166,B_167,C_168,F_171] :
      ( v1_funct_2(k1_tmap_1(A_166,B_167,C_168,D_169,E_170,F_171),k4_subset_1(A_166,C_168,D_169),B_167)
      | ~ m1_subset_1(F_171,k1_zfmisc_1(k2_zfmisc_1(D_169,B_167)))
      | ~ v1_funct_2(F_171,D_169,B_167)
      | ~ v1_funct_1(F_171)
      | ~ m1_subset_1(E_170,k1_zfmisc_1(k2_zfmisc_1(C_168,B_167)))
      | ~ v1_funct_2(E_170,C_168,B_167)
      | ~ v1_funct_1(E_170)
      | ~ m1_subset_1(D_169,k1_zfmisc_1(A_166))
      | v1_xboole_0(D_169)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(A_166))
      | v1_xboole_0(C_168)
      | v1_xboole_0(B_167)
      | v1_xboole_0(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_54,plain,(
    ! [D_169,E_170,A_166,B_167,C_168,F_171] :
      ( m1_subset_1(k1_tmap_1(A_166,B_167,C_168,D_169,E_170,F_171),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_166,C_168,D_169),B_167)))
      | ~ m1_subset_1(F_171,k1_zfmisc_1(k2_zfmisc_1(D_169,B_167)))
      | ~ v1_funct_2(F_171,D_169,B_167)
      | ~ v1_funct_1(F_171)
      | ~ m1_subset_1(E_170,k1_zfmisc_1(k2_zfmisc_1(C_168,B_167)))
      | ~ v1_funct_2(E_170,C_168,B_167)
      | ~ v1_funct_1(E_170)
      | ~ m1_subset_1(D_169,k1_zfmisc_1(A_166))
      | v1_xboole_0(D_169)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(A_166))
      | v1_xboole_0(C_168)
      | v1_xboole_0(B_167)
      | v1_xboole_0(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_16165,plain,(
    ! [F_1895,C_1896,E_1894,A_1892,D_1893,B_1897] :
      ( k2_partfun1(k4_subset_1(A_1892,C_1896,D_1893),B_1897,k1_tmap_1(A_1892,B_1897,C_1896,D_1893,E_1894,F_1895),C_1896) = E_1894
      | ~ m1_subset_1(k1_tmap_1(A_1892,B_1897,C_1896,D_1893,E_1894,F_1895),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1892,C_1896,D_1893),B_1897)))
      | ~ v1_funct_2(k1_tmap_1(A_1892,B_1897,C_1896,D_1893,E_1894,F_1895),k4_subset_1(A_1892,C_1896,D_1893),B_1897)
      | ~ v1_funct_1(k1_tmap_1(A_1892,B_1897,C_1896,D_1893,E_1894,F_1895))
      | k2_partfun1(D_1893,B_1897,F_1895,k9_subset_1(A_1892,C_1896,D_1893)) != k2_partfun1(C_1896,B_1897,E_1894,k9_subset_1(A_1892,C_1896,D_1893))
      | ~ m1_subset_1(F_1895,k1_zfmisc_1(k2_zfmisc_1(D_1893,B_1897)))
      | ~ v1_funct_2(F_1895,D_1893,B_1897)
      | ~ v1_funct_1(F_1895)
      | ~ m1_subset_1(E_1894,k1_zfmisc_1(k2_zfmisc_1(C_1896,B_1897)))
      | ~ v1_funct_2(E_1894,C_1896,B_1897)
      | ~ v1_funct_1(E_1894)
      | ~ m1_subset_1(D_1893,k1_zfmisc_1(A_1892))
      | v1_xboole_0(D_1893)
      | ~ m1_subset_1(C_1896,k1_zfmisc_1(A_1892))
      | v1_xboole_0(C_1896)
      | v1_xboole_0(B_1897)
      | v1_xboole_0(A_1892) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_17756,plain,(
    ! [F_2098,C_2100,B_2097,A_2102,E_2101,D_2099] :
      ( k2_partfun1(k4_subset_1(A_2102,C_2100,D_2099),B_2097,k1_tmap_1(A_2102,B_2097,C_2100,D_2099,E_2101,F_2098),C_2100) = E_2101
      | ~ v1_funct_2(k1_tmap_1(A_2102,B_2097,C_2100,D_2099,E_2101,F_2098),k4_subset_1(A_2102,C_2100,D_2099),B_2097)
      | ~ v1_funct_1(k1_tmap_1(A_2102,B_2097,C_2100,D_2099,E_2101,F_2098))
      | k2_partfun1(D_2099,B_2097,F_2098,k9_subset_1(A_2102,C_2100,D_2099)) != k2_partfun1(C_2100,B_2097,E_2101,k9_subset_1(A_2102,C_2100,D_2099))
      | ~ m1_subset_1(F_2098,k1_zfmisc_1(k2_zfmisc_1(D_2099,B_2097)))
      | ~ v1_funct_2(F_2098,D_2099,B_2097)
      | ~ v1_funct_1(F_2098)
      | ~ m1_subset_1(E_2101,k1_zfmisc_1(k2_zfmisc_1(C_2100,B_2097)))
      | ~ v1_funct_2(E_2101,C_2100,B_2097)
      | ~ v1_funct_1(E_2101)
      | ~ m1_subset_1(D_2099,k1_zfmisc_1(A_2102))
      | v1_xboole_0(D_2099)
      | ~ m1_subset_1(C_2100,k1_zfmisc_1(A_2102))
      | v1_xboole_0(C_2100)
      | v1_xboole_0(B_2097)
      | v1_xboole_0(A_2102) ) ),
    inference(resolution,[status(thm)],[c_54,c_16165])).

tff(c_21150,plain,(
    ! [E_2529,A_2530,D_2527,C_2528,F_2526,B_2525] :
      ( k2_partfun1(k4_subset_1(A_2530,C_2528,D_2527),B_2525,k1_tmap_1(A_2530,B_2525,C_2528,D_2527,E_2529,F_2526),C_2528) = E_2529
      | ~ v1_funct_1(k1_tmap_1(A_2530,B_2525,C_2528,D_2527,E_2529,F_2526))
      | k2_partfun1(D_2527,B_2525,F_2526,k9_subset_1(A_2530,C_2528,D_2527)) != k2_partfun1(C_2528,B_2525,E_2529,k9_subset_1(A_2530,C_2528,D_2527))
      | ~ m1_subset_1(F_2526,k1_zfmisc_1(k2_zfmisc_1(D_2527,B_2525)))
      | ~ v1_funct_2(F_2526,D_2527,B_2525)
      | ~ v1_funct_1(F_2526)
      | ~ m1_subset_1(E_2529,k1_zfmisc_1(k2_zfmisc_1(C_2528,B_2525)))
      | ~ v1_funct_2(E_2529,C_2528,B_2525)
      | ~ v1_funct_1(E_2529)
      | ~ m1_subset_1(D_2527,k1_zfmisc_1(A_2530))
      | v1_xboole_0(D_2527)
      | ~ m1_subset_1(C_2528,k1_zfmisc_1(A_2530))
      | v1_xboole_0(C_2528)
      | v1_xboole_0(B_2525)
      | v1_xboole_0(A_2530) ) ),
    inference(resolution,[status(thm)],[c_56,c_17756])).

tff(c_21157,plain,(
    ! [A_2530,C_2528,E_2529] :
      ( k2_partfun1(k4_subset_1(A_2530,C_2528,'#skF_4'),'#skF_2',k1_tmap_1(A_2530,'#skF_2',C_2528,'#skF_4',E_2529,'#skF_6'),C_2528) = E_2529
      | ~ v1_funct_1(k1_tmap_1(A_2530,'#skF_2',C_2528,'#skF_4',E_2529,'#skF_6'))
      | k2_partfun1(C_2528,'#skF_2',E_2529,k9_subset_1(A_2530,C_2528,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_2530,C_2528,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_2529,k1_zfmisc_1(k2_zfmisc_1(C_2528,'#skF_2')))
      | ~ v1_funct_2(E_2529,C_2528,'#skF_2')
      | ~ v1_funct_1(E_2529)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2530))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_2528,k1_zfmisc_1(A_2530))
      | v1_xboole_0(C_2528)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_2530) ) ),
    inference(resolution,[status(thm)],[c_62,c_21150])).

tff(c_21164,plain,(
    ! [A_2530,C_2528,E_2529] :
      ( k2_partfun1(k4_subset_1(A_2530,C_2528,'#skF_4'),'#skF_2',k1_tmap_1(A_2530,'#skF_2',C_2528,'#skF_4',E_2529,'#skF_6'),C_2528) = E_2529
      | ~ v1_funct_1(k1_tmap_1(A_2530,'#skF_2',C_2528,'#skF_4',E_2529,'#skF_6'))
      | k2_partfun1(C_2528,'#skF_2',E_2529,k9_subset_1(A_2530,C_2528,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2530,C_2528,'#skF_4'))
      | ~ m1_subset_1(E_2529,k1_zfmisc_1(k2_zfmisc_1(C_2528,'#skF_2')))
      | ~ v1_funct_2(E_2529,C_2528,'#skF_2')
      | ~ v1_funct_1(E_2529)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2530))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_2528,k1_zfmisc_1(A_2530))
      | v1_xboole_0(C_2528)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_2530) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_15663,c_21157])).

tff(c_22519,plain,(
    ! [A_2640,C_2641,E_2642] :
      ( k2_partfun1(k4_subset_1(A_2640,C_2641,'#skF_4'),'#skF_2',k1_tmap_1(A_2640,'#skF_2',C_2641,'#skF_4',E_2642,'#skF_6'),C_2641) = E_2642
      | ~ v1_funct_1(k1_tmap_1(A_2640,'#skF_2',C_2641,'#skF_4',E_2642,'#skF_6'))
      | k2_partfun1(C_2641,'#skF_2',E_2642,k9_subset_1(A_2640,C_2641,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2640,C_2641,'#skF_4'))
      | ~ m1_subset_1(E_2642,k1_zfmisc_1(k2_zfmisc_1(C_2641,'#skF_2')))
      | ~ v1_funct_2(E_2642,C_2641,'#skF_2')
      | ~ v1_funct_1(E_2642)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2640))
      | ~ m1_subset_1(C_2641,k1_zfmisc_1(A_2640))
      | v1_xboole_0(C_2641)
      | v1_xboole_0(A_2640) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_78,c_21164])).

tff(c_22529,plain,(
    ! [A_2640] :
      ( k2_partfun1(k4_subset_1(A_2640,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_2640,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_2640,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_2640,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2640,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2640))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_2640))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2640) ) ),
    inference(resolution,[status(thm)],[c_68,c_22519])).

tff(c_22540,plain,(
    ! [A_2640] :
      ( k2_partfun1(k4_subset_1(A_2640,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_2640,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_2640,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_2640,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2640,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2640))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_2640))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2640) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_15666,c_22529])).

tff(c_24470,plain,(
    ! [A_2840] :
      ( k2_partfun1(k4_subset_1(A_2840,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_2840,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_2840,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_2840,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2840,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2840))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_2840))
      | v1_xboole_0(A_2840) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_22540])).

tff(c_2385,plain,(
    ! [B_503,A_504] :
      ( k1_relat_1(B_503) = A_504
      | ~ v1_partfun1(B_503,A_504)
      | ~ v4_relat_1(B_503,A_504)
      | ~ v1_relat_1(B_503) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2394,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2302,c_2385])).

tff(c_2403,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2236,c_2394])).

tff(c_2884,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2403])).

tff(c_3113,plain,(
    ! [C_567,A_568,B_569] :
      ( v1_partfun1(C_567,A_568)
      | ~ v1_funct_2(C_567,A_568,B_569)
      | ~ v1_funct_1(C_567)
      | ~ m1_subset_1(C_567,k1_zfmisc_1(k2_zfmisc_1(A_568,B_569)))
      | v1_xboole_0(B_569) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_3120,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_3113])).

tff(c_3127,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_3120])).

tff(c_3129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2884,c_3127])).

tff(c_3130,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2403])).

tff(c_3138,plain,
    ( k7_relat_1('#skF_6','#skF_4') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3130,c_2309])).

tff(c_3147,plain,(
    k7_relat_1('#skF_6','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2236,c_3138])).

tff(c_24,plain,(
    ! [C_18,A_16,B_17] :
      ( k7_relat_1(k7_relat_1(C_18,A_16),B_17) = k1_xboole_0
      | ~ r1_xboole_0(A_16,B_17)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_3164,plain,(
    ! [B_17] :
      ( k7_relat_1('#skF_6',B_17) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_17)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3147,c_24])).

tff(c_3245,plain,(
    ! [B_577] :
      ( k7_relat_1('#skF_6',B_577) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_577) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2236,c_3164])).

tff(c_3262,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_3245])).

tff(c_2339,plain,(
    ! [A_495,B_496] :
      ( r1_xboole_0(A_495,B_496)
      | ~ r1_subset_1(A_495,B_496)
      | v1_xboole_0(B_496)
      | v1_xboole_0(A_495) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_3899,plain,(
    ! [A_639,B_640] :
      ( k3_xboole_0(A_639,B_640) = k1_xboole_0
      | ~ r1_subset_1(A_639,B_640)
      | v1_xboole_0(B_640)
      | v1_xboole_0(A_639) ) ),
    inference(resolution,[status(thm)],[c_2339,c_2])).

tff(c_3902,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_3899])).

tff(c_3905,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_78,c_3902])).

tff(c_3210,plain,(
    ! [A_572,B_573,C_574] :
      ( k9_subset_1(A_572,B_573,C_574) = k3_xboole_0(B_573,C_574)
      | ~ m1_subset_1(C_574,k1_zfmisc_1(A_572)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3225,plain,(
    ! [B_573] : k9_subset_1('#skF_1',B_573,'#skF_4') = k3_xboole_0(B_573,'#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_3210])).

tff(c_2391,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2303,c_2385])).

tff(c_2400,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2237,c_2391])).

tff(c_2404,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2400])).

tff(c_2841,plain,(
    ! [C_547,A_548,B_549] :
      ( v1_partfun1(C_547,A_548)
      | ~ v1_funct_2(C_547,A_548,B_549)
      | ~ v1_funct_1(C_547)
      | ~ m1_subset_1(C_547,k1_zfmisc_1(k2_zfmisc_1(A_548,B_549)))
      | v1_xboole_0(B_549) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2851,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_2841])).

tff(c_2859,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_2851])).

tff(c_2861,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2404,c_2859])).

tff(c_2862,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2400])).

tff(c_2870,plain,
    ( k7_relat_1('#skF_5','#skF_3') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2862,c_2309])).

tff(c_2879,plain,(
    k7_relat_1('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2237,c_2870])).

tff(c_3155,plain,(
    ! [B_17] :
      ( k7_relat_1('#skF_5',B_17) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_17)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2879,c_24])).

tff(c_3281,plain,(
    ! [B_579] :
      ( k7_relat_1('#skF_5',B_579) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_579) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2237,c_3155])).

tff(c_3298,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_3281])).

tff(c_3519,plain,(
    ! [B_596,F_597,D_598,E_600,C_599,A_601] :
      ( v1_funct_1(k1_tmap_1(A_601,B_596,C_599,D_598,E_600,F_597))
      | ~ m1_subset_1(F_597,k1_zfmisc_1(k2_zfmisc_1(D_598,B_596)))
      | ~ v1_funct_2(F_597,D_598,B_596)
      | ~ v1_funct_1(F_597)
      | ~ m1_subset_1(E_600,k1_zfmisc_1(k2_zfmisc_1(C_599,B_596)))
      | ~ v1_funct_2(E_600,C_599,B_596)
      | ~ v1_funct_1(E_600)
      | ~ m1_subset_1(D_598,k1_zfmisc_1(A_601))
      | v1_xboole_0(D_598)
      | ~ m1_subset_1(C_599,k1_zfmisc_1(A_601))
      | v1_xboole_0(C_599)
      | v1_xboole_0(B_596)
      | v1_xboole_0(A_601) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_3524,plain,(
    ! [A_601,C_599,E_600] :
      ( v1_funct_1(k1_tmap_1(A_601,'#skF_2',C_599,'#skF_4',E_600,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_600,k1_zfmisc_1(k2_zfmisc_1(C_599,'#skF_2')))
      | ~ v1_funct_2(E_600,C_599,'#skF_2')
      | ~ v1_funct_1(E_600)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_601))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_599,k1_zfmisc_1(A_601))
      | v1_xboole_0(C_599)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_601) ) ),
    inference(resolution,[status(thm)],[c_62,c_3519])).

tff(c_3530,plain,(
    ! [A_601,C_599,E_600] :
      ( v1_funct_1(k1_tmap_1(A_601,'#skF_2',C_599,'#skF_4',E_600,'#skF_6'))
      | ~ m1_subset_1(E_600,k1_zfmisc_1(k2_zfmisc_1(C_599,'#skF_2')))
      | ~ v1_funct_2(E_600,C_599,'#skF_2')
      | ~ v1_funct_1(E_600)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_601))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_599,k1_zfmisc_1(A_601))
      | v1_xboole_0(C_599)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_601) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_3524])).

tff(c_4130,plain,(
    ! [A_680,C_681,E_682] :
      ( v1_funct_1(k1_tmap_1(A_680,'#skF_2',C_681,'#skF_4',E_682,'#skF_6'))
      | ~ m1_subset_1(E_682,k1_zfmisc_1(k2_zfmisc_1(C_681,'#skF_2')))
      | ~ v1_funct_2(E_682,C_681,'#skF_2')
      | ~ v1_funct_1(E_682)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_680))
      | ~ m1_subset_1(C_681,k1_zfmisc_1(A_680))
      | v1_xboole_0(C_681)
      | v1_xboole_0(A_680) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_78,c_3530])).

tff(c_4140,plain,(
    ! [A_680] :
      ( v1_funct_1(k1_tmap_1(A_680,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_680))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_680))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_680) ) ),
    inference(resolution,[status(thm)],[c_68,c_4130])).

tff(c_4151,plain,(
    ! [A_680] :
      ( v1_funct_1(k1_tmap_1(A_680,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_680))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_680))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_680) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_4140])).

tff(c_4226,plain,(
    ! [A_694] :
      ( v1_funct_1(k1_tmap_1(A_694,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_694))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_694))
      | v1_xboole_0(A_694) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_4151])).

tff(c_4233,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_80,c_4226])).

tff(c_4237,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_4233])).

tff(c_4238,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_4237])).

tff(c_3346,plain,(
    ! [A_582,B_583,C_584,D_585] :
      ( k2_partfun1(A_582,B_583,C_584,D_585) = k7_relat_1(C_584,D_585)
      | ~ m1_subset_1(C_584,k1_zfmisc_1(k2_zfmisc_1(A_582,B_583)))
      | ~ v1_funct_1(C_584) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_3353,plain,(
    ! [D_585] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_585) = k7_relat_1('#skF_5',D_585)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_68,c_3346])).

tff(c_3360,plain,(
    ! [D_585] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_585) = k7_relat_1('#skF_5',D_585) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3353])).

tff(c_3351,plain,(
    ! [D_585] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_585) = k7_relat_1('#skF_6',D_585)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_62,c_3346])).

tff(c_3357,plain,(
    ! [D_585] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_585) = k7_relat_1('#skF_6',D_585) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3351])).

tff(c_3910,plain,(
    ! [A_641,C_645,F_644,E_643,D_642,B_646] :
      ( k2_partfun1(k4_subset_1(A_641,C_645,D_642),B_646,k1_tmap_1(A_641,B_646,C_645,D_642,E_643,F_644),D_642) = F_644
      | ~ m1_subset_1(k1_tmap_1(A_641,B_646,C_645,D_642,E_643,F_644),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_641,C_645,D_642),B_646)))
      | ~ v1_funct_2(k1_tmap_1(A_641,B_646,C_645,D_642,E_643,F_644),k4_subset_1(A_641,C_645,D_642),B_646)
      | ~ v1_funct_1(k1_tmap_1(A_641,B_646,C_645,D_642,E_643,F_644))
      | k2_partfun1(D_642,B_646,F_644,k9_subset_1(A_641,C_645,D_642)) != k2_partfun1(C_645,B_646,E_643,k9_subset_1(A_641,C_645,D_642))
      | ~ m1_subset_1(F_644,k1_zfmisc_1(k2_zfmisc_1(D_642,B_646)))
      | ~ v1_funct_2(F_644,D_642,B_646)
      | ~ v1_funct_1(F_644)
      | ~ m1_subset_1(E_643,k1_zfmisc_1(k2_zfmisc_1(C_645,B_646)))
      | ~ v1_funct_2(E_643,C_645,B_646)
      | ~ v1_funct_1(E_643)
      | ~ m1_subset_1(D_642,k1_zfmisc_1(A_641))
      | v1_xboole_0(D_642)
      | ~ m1_subset_1(C_645,k1_zfmisc_1(A_641))
      | v1_xboole_0(C_645)
      | v1_xboole_0(B_646)
      | v1_xboole_0(A_641) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_5777,plain,(
    ! [E_869,D_867,F_866,A_870,C_868,B_865] :
      ( k2_partfun1(k4_subset_1(A_870,C_868,D_867),B_865,k1_tmap_1(A_870,B_865,C_868,D_867,E_869,F_866),D_867) = F_866
      | ~ v1_funct_2(k1_tmap_1(A_870,B_865,C_868,D_867,E_869,F_866),k4_subset_1(A_870,C_868,D_867),B_865)
      | ~ v1_funct_1(k1_tmap_1(A_870,B_865,C_868,D_867,E_869,F_866))
      | k2_partfun1(D_867,B_865,F_866,k9_subset_1(A_870,C_868,D_867)) != k2_partfun1(C_868,B_865,E_869,k9_subset_1(A_870,C_868,D_867))
      | ~ m1_subset_1(F_866,k1_zfmisc_1(k2_zfmisc_1(D_867,B_865)))
      | ~ v1_funct_2(F_866,D_867,B_865)
      | ~ v1_funct_1(F_866)
      | ~ m1_subset_1(E_869,k1_zfmisc_1(k2_zfmisc_1(C_868,B_865)))
      | ~ v1_funct_2(E_869,C_868,B_865)
      | ~ v1_funct_1(E_869)
      | ~ m1_subset_1(D_867,k1_zfmisc_1(A_870))
      | v1_xboole_0(D_867)
      | ~ m1_subset_1(C_868,k1_zfmisc_1(A_870))
      | v1_xboole_0(C_868)
      | v1_xboole_0(B_865)
      | v1_xboole_0(A_870) ) ),
    inference(resolution,[status(thm)],[c_54,c_3910])).

tff(c_8847,plain,(
    ! [E_1284,C_1283,D_1282,A_1285,B_1280,F_1281] :
      ( k2_partfun1(k4_subset_1(A_1285,C_1283,D_1282),B_1280,k1_tmap_1(A_1285,B_1280,C_1283,D_1282,E_1284,F_1281),D_1282) = F_1281
      | ~ v1_funct_1(k1_tmap_1(A_1285,B_1280,C_1283,D_1282,E_1284,F_1281))
      | k2_partfun1(D_1282,B_1280,F_1281,k9_subset_1(A_1285,C_1283,D_1282)) != k2_partfun1(C_1283,B_1280,E_1284,k9_subset_1(A_1285,C_1283,D_1282))
      | ~ m1_subset_1(F_1281,k1_zfmisc_1(k2_zfmisc_1(D_1282,B_1280)))
      | ~ v1_funct_2(F_1281,D_1282,B_1280)
      | ~ v1_funct_1(F_1281)
      | ~ m1_subset_1(E_1284,k1_zfmisc_1(k2_zfmisc_1(C_1283,B_1280)))
      | ~ v1_funct_2(E_1284,C_1283,B_1280)
      | ~ v1_funct_1(E_1284)
      | ~ m1_subset_1(D_1282,k1_zfmisc_1(A_1285))
      | v1_xboole_0(D_1282)
      | ~ m1_subset_1(C_1283,k1_zfmisc_1(A_1285))
      | v1_xboole_0(C_1283)
      | v1_xboole_0(B_1280)
      | v1_xboole_0(A_1285) ) ),
    inference(resolution,[status(thm)],[c_56,c_5777])).

tff(c_8854,plain,(
    ! [A_1285,C_1283,E_1284] :
      ( k2_partfun1(k4_subset_1(A_1285,C_1283,'#skF_4'),'#skF_2',k1_tmap_1(A_1285,'#skF_2',C_1283,'#skF_4',E_1284,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1285,'#skF_2',C_1283,'#skF_4',E_1284,'#skF_6'))
      | k2_partfun1(C_1283,'#skF_2',E_1284,k9_subset_1(A_1285,C_1283,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_1285,C_1283,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1284,k1_zfmisc_1(k2_zfmisc_1(C_1283,'#skF_2')))
      | ~ v1_funct_2(E_1284,C_1283,'#skF_2')
      | ~ v1_funct_1(E_1284)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1285))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1283,k1_zfmisc_1(A_1285))
      | v1_xboole_0(C_1283)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1285) ) ),
    inference(resolution,[status(thm)],[c_62,c_8847])).

tff(c_8861,plain,(
    ! [A_1285,C_1283,E_1284] :
      ( k2_partfun1(k4_subset_1(A_1285,C_1283,'#skF_4'),'#skF_2',k1_tmap_1(A_1285,'#skF_2',C_1283,'#skF_4',E_1284,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1285,'#skF_2',C_1283,'#skF_4',E_1284,'#skF_6'))
      | k2_partfun1(C_1283,'#skF_2',E_1284,k9_subset_1(A_1285,C_1283,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1285,C_1283,'#skF_4'))
      | ~ m1_subset_1(E_1284,k1_zfmisc_1(k2_zfmisc_1(C_1283,'#skF_2')))
      | ~ v1_funct_2(E_1284,C_1283,'#skF_2')
      | ~ v1_funct_1(E_1284)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1285))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1283,k1_zfmisc_1(A_1285))
      | v1_xboole_0(C_1283)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1285) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_3357,c_8854])).

tff(c_10141,plain,(
    ! [A_1390,C_1391,E_1392] :
      ( k2_partfun1(k4_subset_1(A_1390,C_1391,'#skF_4'),'#skF_2',k1_tmap_1(A_1390,'#skF_2',C_1391,'#skF_4',E_1392,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1390,'#skF_2',C_1391,'#skF_4',E_1392,'#skF_6'))
      | k2_partfun1(C_1391,'#skF_2',E_1392,k9_subset_1(A_1390,C_1391,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1390,C_1391,'#skF_4'))
      | ~ m1_subset_1(E_1392,k1_zfmisc_1(k2_zfmisc_1(C_1391,'#skF_2')))
      | ~ v1_funct_2(E_1392,C_1391,'#skF_2')
      | ~ v1_funct_1(E_1392)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1390))
      | ~ m1_subset_1(C_1391,k1_zfmisc_1(A_1390))
      | v1_xboole_0(C_1391)
      | v1_xboole_0(A_1390) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_78,c_8861])).

tff(c_10151,plain,(
    ! [A_1390] :
      ( k2_partfun1(k4_subset_1(A_1390,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1390,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1390,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1390,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1390,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1390))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1390))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1390) ) ),
    inference(resolution,[status(thm)],[c_68,c_10141])).

tff(c_10162,plain,(
    ! [A_1390] :
      ( k2_partfun1(k4_subset_1(A_1390,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1390,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1390,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1390,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1390,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1390))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1390))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1390) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_3360,c_10151])).

tff(c_14112,plain,(
    ! [A_1719] :
      ( k2_partfun1(k4_subset_1(A_1719,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1719,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1719,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1719,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1719,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1719))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1719))
      | v1_xboole_0(A_1719) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_10162])).

tff(c_207,plain,(
    ! [C_248,A_249,B_250] :
      ( v1_relat_1(C_248)
      | ~ m1_subset_1(C_248,k1_zfmisc_1(k2_zfmisc_1(A_249,B_250))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_219,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_207])).

tff(c_239,plain,(
    ! [C_256,A_257,B_258] :
      ( v4_relat_1(C_256,A_257)
      | ~ m1_subset_1(C_256,k1_zfmisc_1(k2_zfmisc_1(A_257,B_258))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_251,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_239])).

tff(c_364,plain,(
    ! [B_283,A_284] :
      ( k1_relat_1(B_283) = A_284
      | ~ v1_partfun1(B_283,A_284)
      | ~ v4_relat_1(B_283,A_284)
      | ~ v1_relat_1(B_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_373,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_251,c_364])).

tff(c_382,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_373])).

tff(c_891,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_382])).

tff(c_1120,plain,(
    ! [C_349,A_350,B_351] :
      ( v1_partfun1(C_349,A_350)
      | ~ v1_funct_2(C_349,A_350,B_351)
      | ~ v1_funct_1(C_349)
      | ~ m1_subset_1(C_349,k1_zfmisc_1(k2_zfmisc_1(A_350,B_351)))
      | v1_xboole_0(B_351) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1127,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_1120])).

tff(c_1134,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1127])).

tff(c_1136,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_891,c_1134])).

tff(c_1137,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_382])).

tff(c_302,plain,(
    ! [B_272,A_273] :
      ( k7_relat_1(B_272,A_273) = B_272
      | ~ r1_tarski(k1_relat_1(B_272),A_273)
      | ~ v1_relat_1(B_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_307,plain,(
    ! [B_272] :
      ( k7_relat_1(B_272,k1_relat_1(B_272)) = B_272
      | ~ v1_relat_1(B_272) ) ),
    inference(resolution,[status(thm)],[c_10,c_302])).

tff(c_1145,plain,
    ( k7_relat_1('#skF_6','#skF_4') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1137,c_307])).

tff(c_1154,plain,(
    k7_relat_1('#skF_6','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_1145])).

tff(c_1171,plain,(
    ! [B_17] :
      ( k7_relat_1('#skF_6',B_17) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_17)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1154,c_24])).

tff(c_1252,plain,(
    ! [B_359] :
      ( k7_relat_1('#skF_6',B_359) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_359) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_1171])).

tff(c_1269,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_1252])).

tff(c_318,plain,(
    ! [A_275,B_276] :
      ( r1_xboole_0(A_275,B_276)
      | ~ r1_subset_1(A_275,B_276)
      | v1_xboole_0(B_276)
      | v1_xboole_0(A_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1906,plain,(
    ! [A_421,B_422] :
      ( k3_xboole_0(A_421,B_422) = k1_xboole_0
      | ~ r1_subset_1(A_421,B_422)
      | v1_xboole_0(B_422)
      | v1_xboole_0(A_421) ) ),
    inference(resolution,[status(thm)],[c_318,c_2])).

tff(c_1909,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_1906])).

tff(c_1912,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_78,c_1909])).

tff(c_220,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_207])).

tff(c_252,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_239])).

tff(c_370,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_252,c_364])).

tff(c_379,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_370])).

tff(c_383,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_379])).

tff(c_848,plain,(
    ! [C_329,A_330,B_331] :
      ( v1_partfun1(C_329,A_330)
      | ~ v1_funct_2(C_329,A_330,B_331)
      | ~ v1_funct_1(C_329)
      | ~ m1_subset_1(C_329,k1_zfmisc_1(k2_zfmisc_1(A_330,B_331)))
      | v1_xboole_0(B_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_858,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_848])).

tff(c_866,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_858])).

tff(c_868,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_383,c_866])).

tff(c_869,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_379])).

tff(c_877,plain,
    ( k7_relat_1('#skF_5','#skF_3') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_869,c_307])).

tff(c_886,plain,(
    k7_relat_1('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_877])).

tff(c_1162,plain,(
    ! [B_17] :
      ( k7_relat_1('#skF_5',B_17) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_17)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_886,c_24])).

tff(c_1288,plain,(
    ! [B_361] :
      ( k7_relat_1('#skF_5',B_361) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_361) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_1162])).

tff(c_1305,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_1288])).

tff(c_1353,plain,(
    ! [A_364,B_365,C_366,D_367] :
      ( k2_partfun1(A_364,B_365,C_366,D_367) = k7_relat_1(C_366,D_367)
      | ~ m1_subset_1(C_366,k1_zfmisc_1(k2_zfmisc_1(A_364,B_365)))
      | ~ v1_funct_1(C_366) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1360,plain,(
    ! [D_367] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_367) = k7_relat_1('#skF_5',D_367)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_68,c_1353])).

tff(c_1367,plain,(
    ! [D_367] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_367) = k7_relat_1('#skF_5',D_367) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1360])).

tff(c_1358,plain,(
    ! [D_367] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_367) = k7_relat_1('#skF_6',D_367)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_62,c_1353])).

tff(c_1364,plain,(
    ! [D_367] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_367) = k7_relat_1('#skF_6',D_367) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1358])).

tff(c_1217,plain,(
    ! [A_354,B_355,C_356] :
      ( k9_subset_1(A_354,B_355,C_356) = k3_xboole_0(B_355,C_356)
      | ~ m1_subset_1(C_356,k1_zfmisc_1(A_354)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1232,plain,(
    ! [B_355] : k9_subset_1('#skF_1',B_355,'#skF_4') = k3_xboole_0(B_355,'#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_1217])).

tff(c_60,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_108,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_1242,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1232,c_1232,c_108])).

tff(c_2122,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1269,c_1912,c_1305,c_1912,c_1367,c_1364,c_1242])).

tff(c_2123,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_2319,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_2123])).

tff(c_14145,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14112,c_2319])).

tff(c_14187,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_3262,c_3905,c_3225,c_3298,c_3905,c_3225,c_4238,c_14145])).

tff(c_14189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_14187])).

tff(c_14190,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2123])).

tff(c_24493,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_24470,c_14190])).

tff(c_24529,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_15456,c_15483,c_16125,c_15571,c_16125,c_15571,c_16462,c_24493])).

tff(c_24531,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_24529])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:47:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.00/9.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.00/9.76  
% 19.00/9.76  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.00/9.76  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 19.00/9.76  
% 19.00/9.76  %Foreground sorts:
% 19.00/9.76  
% 19.00/9.76  
% 19.00/9.76  %Background operators:
% 19.00/9.76  
% 19.00/9.76  
% 19.00/9.76  %Foreground operators:
% 19.00/9.76  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 19.00/9.76  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 19.00/9.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.00/9.76  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 19.00/9.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 19.00/9.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 19.00/9.76  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 19.00/9.76  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 19.00/9.76  tff('#skF_5', type, '#skF_5': $i).
% 19.00/9.76  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 19.00/9.76  tff('#skF_6', type, '#skF_6': $i).
% 19.00/9.76  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 19.00/9.76  tff('#skF_2', type, '#skF_2': $i).
% 19.00/9.76  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 19.00/9.76  tff('#skF_3', type, '#skF_3': $i).
% 19.00/9.76  tff('#skF_1', type, '#skF_1': $i).
% 19.00/9.76  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 19.00/9.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 19.00/9.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.00/9.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 19.00/9.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 19.00/9.76  tff('#skF_4', type, '#skF_4': $i).
% 19.00/9.76  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 19.00/9.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.00/9.76  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 19.00/9.76  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 19.00/9.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 19.00/9.76  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 19.00/9.76  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 19.00/9.76  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 19.00/9.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 19.00/9.76  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 19.00/9.76  
% 19.21/9.79  tff(f_238, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 19.21/9.79  tff(f_37, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 19.21/9.79  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 19.21/9.79  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 19.21/9.79  tff(f_108, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 19.21/9.79  tff(f_100, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 19.21/9.79  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 19.21/9.79  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 19.21/9.79  tff(f_60, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 19.21/9.79  tff(f_76, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 19.21/9.79  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 19.21/9.79  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 19.21/9.79  tff(f_196, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 19.21/9.79  tff(f_114, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 19.21/9.79  tff(f_162, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 19.21/9.79  tff(c_86, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_238])).
% 19.21/9.79  tff(c_80, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_238])).
% 19.21/9.79  tff(c_76, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_238])).
% 19.21/9.79  tff(c_12, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 19.21/9.79  tff(c_62, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_238])).
% 19.21/9.79  tff(c_2224, plain, (![C_468, A_469, B_470]: (v1_relat_1(C_468) | ~m1_subset_1(C_468, k1_zfmisc_1(k2_zfmisc_1(A_469, B_470))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 19.21/9.79  tff(c_2236, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_62, c_2224])).
% 19.21/9.79  tff(c_84, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_238])).
% 19.21/9.79  tff(c_2290, plain, (![C_484, A_485, B_486]: (v4_relat_1(C_484, A_485) | ~m1_subset_1(C_484, k1_zfmisc_1(k2_zfmisc_1(A_485, B_486))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 19.21/9.79  tff(c_2302, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_62, c_2290])).
% 19.21/9.79  tff(c_14235, plain, (![B_1730, A_1731]: (k1_relat_1(B_1730)=A_1731 | ~v1_partfun1(B_1730, A_1731) | ~v4_relat_1(B_1730, A_1731) | ~v1_relat_1(B_1730))), inference(cnfTransformation, [status(thm)], [f_108])).
% 19.21/9.79  tff(c_14244, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2302, c_14235])).
% 19.21/9.79  tff(c_14253, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2236, c_14244])).
% 19.21/9.79  tff(c_14957, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_14253])).
% 19.21/9.79  tff(c_66, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_238])).
% 19.21/9.79  tff(c_64, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_238])).
% 19.21/9.79  tff(c_15319, plain, (![C_1819, A_1820, B_1821]: (v1_partfun1(C_1819, A_1820) | ~v1_funct_2(C_1819, A_1820, B_1821) | ~v1_funct_1(C_1819) | ~m1_subset_1(C_1819, k1_zfmisc_1(k2_zfmisc_1(A_1820, B_1821))) | v1_xboole_0(B_1821))), inference(cnfTransformation, [status(thm)], [f_100])).
% 19.21/9.79  tff(c_15326, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_62, c_15319])).
% 19.21/9.79  tff(c_15333, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_15326])).
% 19.21/9.79  tff(c_15335, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_14957, c_15333])).
% 19.21/9.79  tff(c_15336, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_14253])).
% 19.21/9.79  tff(c_10, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 19.21/9.79  tff(c_2304, plain, (![B_487, A_488]: (k7_relat_1(B_487, A_488)=B_487 | ~r1_tarski(k1_relat_1(B_487), A_488) | ~v1_relat_1(B_487))), inference(cnfTransformation, [status(thm)], [f_66])).
% 19.21/9.79  tff(c_2309, plain, (![B_487]: (k7_relat_1(B_487, k1_relat_1(B_487))=B_487 | ~v1_relat_1(B_487))), inference(resolution, [status(thm)], [c_10, c_2304])).
% 19.21/9.79  tff(c_15344, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6' | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_15336, c_2309])).
% 19.21/9.79  tff(c_15353, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2236, c_15344])).
% 19.21/9.79  tff(c_15393, plain, (![C_1826, A_1827, B_1828]: (k7_relat_1(k7_relat_1(C_1826, A_1827), B_1828)=k1_xboole_0 | ~r1_xboole_0(A_1827, B_1828) | ~v1_relat_1(C_1826))), inference(cnfTransformation, [status(thm)], [f_60])).
% 19.21/9.79  tff(c_15418, plain, (![B_1828]: (k7_relat_1('#skF_6', B_1828)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_1828) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_15353, c_15393])).
% 19.21/9.79  tff(c_15439, plain, (![B_1829]: (k7_relat_1('#skF_6', B_1829)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_1829))), inference(demodulation, [status(thm), theory('equality')], [c_2236, c_15418])).
% 19.21/9.79  tff(c_15456, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_15439])).
% 19.21/9.79  tff(c_68, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_238])).
% 19.21/9.79  tff(c_2237, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_68, c_2224])).
% 19.21/9.79  tff(c_2303, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_2290])).
% 19.21/9.79  tff(c_14241, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2303, c_14235])).
% 19.21/9.79  tff(c_14250, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2237, c_14241])).
% 19.21/9.79  tff(c_14254, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_14250])).
% 19.21/9.79  tff(c_72, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_238])).
% 19.21/9.79  tff(c_70, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_238])).
% 19.21/9.79  tff(c_14910, plain, (![C_1793, A_1794, B_1795]: (v1_partfun1(C_1793, A_1794) | ~v1_funct_2(C_1793, A_1794, B_1795) | ~v1_funct_1(C_1793) | ~m1_subset_1(C_1793, k1_zfmisc_1(k2_zfmisc_1(A_1794, B_1795))) | v1_xboole_0(B_1795))), inference(cnfTransformation, [status(thm)], [f_100])).
% 19.21/9.79  tff(c_14920, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_14910])).
% 19.21/9.79  tff(c_14928, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_14920])).
% 19.21/9.79  tff(c_14930, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_14254, c_14928])).
% 19.21/9.79  tff(c_14931, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_14250])).
% 19.21/9.79  tff(c_14939, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5' | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_14931, c_2309])).
% 19.21/9.79  tff(c_14948, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2237, c_14939])).
% 19.21/9.79  tff(c_15421, plain, (![B_1828]: (k7_relat_1('#skF_5', B_1828)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_1828) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_14948, c_15393])).
% 19.21/9.79  tff(c_15466, plain, (![B_1830]: (k7_relat_1('#skF_5', B_1830)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_1830))), inference(demodulation, [status(thm), theory('equality')], [c_2237, c_15421])).
% 19.21/9.79  tff(c_15483, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_15466])).
% 19.21/9.79  tff(c_82, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_238])).
% 19.21/9.79  tff(c_78, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_238])).
% 19.21/9.79  tff(c_74, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_238])).
% 19.21/9.79  tff(c_14211, plain, (![A_1725, B_1726]: (r1_xboole_0(A_1725, B_1726) | ~r1_subset_1(A_1725, B_1726) | v1_xboole_0(B_1726) | v1_xboole_0(A_1725))), inference(cnfTransformation, [status(thm)], [f_76])).
% 19.21/9.79  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 19.21/9.79  tff(c_16119, plain, (![A_1888, B_1889]: (k3_xboole_0(A_1888, B_1889)=k1_xboole_0 | ~r1_subset_1(A_1888, B_1889) | v1_xboole_0(B_1889) | v1_xboole_0(A_1888))), inference(resolution, [status(thm)], [c_14211, c_2])).
% 19.21/9.79  tff(c_16122, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_74, c_16119])).
% 19.21/9.79  tff(c_16125, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_82, c_78, c_16122])).
% 19.21/9.79  tff(c_15556, plain, (![A_1835, B_1836, C_1837]: (k9_subset_1(A_1835, B_1836, C_1837)=k3_xboole_0(B_1836, C_1837) | ~m1_subset_1(C_1837, k1_zfmisc_1(A_1835)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 19.21/9.79  tff(c_15571, plain, (![B_1836]: (k9_subset_1('#skF_1', B_1836, '#skF_4')=k3_xboole_0(B_1836, '#skF_4'))), inference(resolution, [status(thm)], [c_76, c_15556])).
% 19.21/9.79  tff(c_15790, plain, (![E_1858, D_1856, B_1854, F_1855, A_1859, C_1857]: (v1_funct_1(k1_tmap_1(A_1859, B_1854, C_1857, D_1856, E_1858, F_1855)) | ~m1_subset_1(F_1855, k1_zfmisc_1(k2_zfmisc_1(D_1856, B_1854))) | ~v1_funct_2(F_1855, D_1856, B_1854) | ~v1_funct_1(F_1855) | ~m1_subset_1(E_1858, k1_zfmisc_1(k2_zfmisc_1(C_1857, B_1854))) | ~v1_funct_2(E_1858, C_1857, B_1854) | ~v1_funct_1(E_1858) | ~m1_subset_1(D_1856, k1_zfmisc_1(A_1859)) | v1_xboole_0(D_1856) | ~m1_subset_1(C_1857, k1_zfmisc_1(A_1859)) | v1_xboole_0(C_1857) | v1_xboole_0(B_1854) | v1_xboole_0(A_1859))), inference(cnfTransformation, [status(thm)], [f_196])).
% 19.21/9.79  tff(c_15795, plain, (![A_1859, C_1857, E_1858]: (v1_funct_1(k1_tmap_1(A_1859, '#skF_2', C_1857, '#skF_4', E_1858, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1858, k1_zfmisc_1(k2_zfmisc_1(C_1857, '#skF_2'))) | ~v1_funct_2(E_1858, C_1857, '#skF_2') | ~v1_funct_1(E_1858) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1859)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1857, k1_zfmisc_1(A_1859)) | v1_xboole_0(C_1857) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1859))), inference(resolution, [status(thm)], [c_62, c_15790])).
% 19.21/9.79  tff(c_15801, plain, (![A_1859, C_1857, E_1858]: (v1_funct_1(k1_tmap_1(A_1859, '#skF_2', C_1857, '#skF_4', E_1858, '#skF_6')) | ~m1_subset_1(E_1858, k1_zfmisc_1(k2_zfmisc_1(C_1857, '#skF_2'))) | ~v1_funct_2(E_1858, C_1857, '#skF_2') | ~v1_funct_1(E_1858) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1859)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1857, k1_zfmisc_1(A_1859)) | v1_xboole_0(C_1857) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1859))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_15795])).
% 19.21/9.79  tff(c_16363, plain, (![A_1935, C_1936, E_1937]: (v1_funct_1(k1_tmap_1(A_1935, '#skF_2', C_1936, '#skF_4', E_1937, '#skF_6')) | ~m1_subset_1(E_1937, k1_zfmisc_1(k2_zfmisc_1(C_1936, '#skF_2'))) | ~v1_funct_2(E_1937, C_1936, '#skF_2') | ~v1_funct_1(E_1937) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1935)) | ~m1_subset_1(C_1936, k1_zfmisc_1(A_1935)) | v1_xboole_0(C_1936) | v1_xboole_0(A_1935))), inference(negUnitSimplification, [status(thm)], [c_84, c_78, c_15801])).
% 19.21/9.79  tff(c_16373, plain, (![A_1935]: (v1_funct_1(k1_tmap_1(A_1935, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1935)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1935)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1935))), inference(resolution, [status(thm)], [c_68, c_16363])).
% 19.21/9.79  tff(c_16384, plain, (![A_1935]: (v1_funct_1(k1_tmap_1(A_1935, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1935)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1935)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1935))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_16373])).
% 19.21/9.79  tff(c_16450, plain, (![A_1950]: (v1_funct_1(k1_tmap_1(A_1950, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1950)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1950)) | v1_xboole_0(A_1950))), inference(negUnitSimplification, [status(thm)], [c_82, c_16384])).
% 19.21/9.79  tff(c_16457, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_80, c_16450])).
% 19.21/9.79  tff(c_16461, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_16457])).
% 19.21/9.79  tff(c_16462, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_86, c_16461])).
% 19.21/9.79  tff(c_15652, plain, (![A_1842, B_1843, C_1844, D_1845]: (k2_partfun1(A_1842, B_1843, C_1844, D_1845)=k7_relat_1(C_1844, D_1845) | ~m1_subset_1(C_1844, k1_zfmisc_1(k2_zfmisc_1(A_1842, B_1843))) | ~v1_funct_1(C_1844))), inference(cnfTransformation, [status(thm)], [f_114])).
% 19.21/9.79  tff(c_15659, plain, (![D_1845]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_1845)=k7_relat_1('#skF_5', D_1845) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_68, c_15652])).
% 19.21/9.79  tff(c_15666, plain, (![D_1845]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_1845)=k7_relat_1('#skF_5', D_1845))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_15659])).
% 19.21/9.79  tff(c_15657, plain, (![D_1845]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_1845)=k7_relat_1('#skF_6', D_1845) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_62, c_15652])).
% 19.21/9.79  tff(c_15663, plain, (![D_1845]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_1845)=k7_relat_1('#skF_6', D_1845))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_15657])).
% 19.21/9.79  tff(c_56, plain, (![D_169, E_170, A_166, B_167, C_168, F_171]: (v1_funct_2(k1_tmap_1(A_166, B_167, C_168, D_169, E_170, F_171), k4_subset_1(A_166, C_168, D_169), B_167) | ~m1_subset_1(F_171, k1_zfmisc_1(k2_zfmisc_1(D_169, B_167))) | ~v1_funct_2(F_171, D_169, B_167) | ~v1_funct_1(F_171) | ~m1_subset_1(E_170, k1_zfmisc_1(k2_zfmisc_1(C_168, B_167))) | ~v1_funct_2(E_170, C_168, B_167) | ~v1_funct_1(E_170) | ~m1_subset_1(D_169, k1_zfmisc_1(A_166)) | v1_xboole_0(D_169) | ~m1_subset_1(C_168, k1_zfmisc_1(A_166)) | v1_xboole_0(C_168) | v1_xboole_0(B_167) | v1_xboole_0(A_166))), inference(cnfTransformation, [status(thm)], [f_196])).
% 19.21/9.79  tff(c_54, plain, (![D_169, E_170, A_166, B_167, C_168, F_171]: (m1_subset_1(k1_tmap_1(A_166, B_167, C_168, D_169, E_170, F_171), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_166, C_168, D_169), B_167))) | ~m1_subset_1(F_171, k1_zfmisc_1(k2_zfmisc_1(D_169, B_167))) | ~v1_funct_2(F_171, D_169, B_167) | ~v1_funct_1(F_171) | ~m1_subset_1(E_170, k1_zfmisc_1(k2_zfmisc_1(C_168, B_167))) | ~v1_funct_2(E_170, C_168, B_167) | ~v1_funct_1(E_170) | ~m1_subset_1(D_169, k1_zfmisc_1(A_166)) | v1_xboole_0(D_169) | ~m1_subset_1(C_168, k1_zfmisc_1(A_166)) | v1_xboole_0(C_168) | v1_xboole_0(B_167) | v1_xboole_0(A_166))), inference(cnfTransformation, [status(thm)], [f_196])).
% 19.21/9.79  tff(c_16165, plain, (![F_1895, C_1896, E_1894, A_1892, D_1893, B_1897]: (k2_partfun1(k4_subset_1(A_1892, C_1896, D_1893), B_1897, k1_tmap_1(A_1892, B_1897, C_1896, D_1893, E_1894, F_1895), C_1896)=E_1894 | ~m1_subset_1(k1_tmap_1(A_1892, B_1897, C_1896, D_1893, E_1894, F_1895), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1892, C_1896, D_1893), B_1897))) | ~v1_funct_2(k1_tmap_1(A_1892, B_1897, C_1896, D_1893, E_1894, F_1895), k4_subset_1(A_1892, C_1896, D_1893), B_1897) | ~v1_funct_1(k1_tmap_1(A_1892, B_1897, C_1896, D_1893, E_1894, F_1895)) | k2_partfun1(D_1893, B_1897, F_1895, k9_subset_1(A_1892, C_1896, D_1893))!=k2_partfun1(C_1896, B_1897, E_1894, k9_subset_1(A_1892, C_1896, D_1893)) | ~m1_subset_1(F_1895, k1_zfmisc_1(k2_zfmisc_1(D_1893, B_1897))) | ~v1_funct_2(F_1895, D_1893, B_1897) | ~v1_funct_1(F_1895) | ~m1_subset_1(E_1894, k1_zfmisc_1(k2_zfmisc_1(C_1896, B_1897))) | ~v1_funct_2(E_1894, C_1896, B_1897) | ~v1_funct_1(E_1894) | ~m1_subset_1(D_1893, k1_zfmisc_1(A_1892)) | v1_xboole_0(D_1893) | ~m1_subset_1(C_1896, k1_zfmisc_1(A_1892)) | v1_xboole_0(C_1896) | v1_xboole_0(B_1897) | v1_xboole_0(A_1892))), inference(cnfTransformation, [status(thm)], [f_162])).
% 19.21/9.79  tff(c_17756, plain, (![F_2098, C_2100, B_2097, A_2102, E_2101, D_2099]: (k2_partfun1(k4_subset_1(A_2102, C_2100, D_2099), B_2097, k1_tmap_1(A_2102, B_2097, C_2100, D_2099, E_2101, F_2098), C_2100)=E_2101 | ~v1_funct_2(k1_tmap_1(A_2102, B_2097, C_2100, D_2099, E_2101, F_2098), k4_subset_1(A_2102, C_2100, D_2099), B_2097) | ~v1_funct_1(k1_tmap_1(A_2102, B_2097, C_2100, D_2099, E_2101, F_2098)) | k2_partfun1(D_2099, B_2097, F_2098, k9_subset_1(A_2102, C_2100, D_2099))!=k2_partfun1(C_2100, B_2097, E_2101, k9_subset_1(A_2102, C_2100, D_2099)) | ~m1_subset_1(F_2098, k1_zfmisc_1(k2_zfmisc_1(D_2099, B_2097))) | ~v1_funct_2(F_2098, D_2099, B_2097) | ~v1_funct_1(F_2098) | ~m1_subset_1(E_2101, k1_zfmisc_1(k2_zfmisc_1(C_2100, B_2097))) | ~v1_funct_2(E_2101, C_2100, B_2097) | ~v1_funct_1(E_2101) | ~m1_subset_1(D_2099, k1_zfmisc_1(A_2102)) | v1_xboole_0(D_2099) | ~m1_subset_1(C_2100, k1_zfmisc_1(A_2102)) | v1_xboole_0(C_2100) | v1_xboole_0(B_2097) | v1_xboole_0(A_2102))), inference(resolution, [status(thm)], [c_54, c_16165])).
% 19.21/9.79  tff(c_21150, plain, (![E_2529, A_2530, D_2527, C_2528, F_2526, B_2525]: (k2_partfun1(k4_subset_1(A_2530, C_2528, D_2527), B_2525, k1_tmap_1(A_2530, B_2525, C_2528, D_2527, E_2529, F_2526), C_2528)=E_2529 | ~v1_funct_1(k1_tmap_1(A_2530, B_2525, C_2528, D_2527, E_2529, F_2526)) | k2_partfun1(D_2527, B_2525, F_2526, k9_subset_1(A_2530, C_2528, D_2527))!=k2_partfun1(C_2528, B_2525, E_2529, k9_subset_1(A_2530, C_2528, D_2527)) | ~m1_subset_1(F_2526, k1_zfmisc_1(k2_zfmisc_1(D_2527, B_2525))) | ~v1_funct_2(F_2526, D_2527, B_2525) | ~v1_funct_1(F_2526) | ~m1_subset_1(E_2529, k1_zfmisc_1(k2_zfmisc_1(C_2528, B_2525))) | ~v1_funct_2(E_2529, C_2528, B_2525) | ~v1_funct_1(E_2529) | ~m1_subset_1(D_2527, k1_zfmisc_1(A_2530)) | v1_xboole_0(D_2527) | ~m1_subset_1(C_2528, k1_zfmisc_1(A_2530)) | v1_xboole_0(C_2528) | v1_xboole_0(B_2525) | v1_xboole_0(A_2530))), inference(resolution, [status(thm)], [c_56, c_17756])).
% 19.21/9.79  tff(c_21157, plain, (![A_2530, C_2528, E_2529]: (k2_partfun1(k4_subset_1(A_2530, C_2528, '#skF_4'), '#skF_2', k1_tmap_1(A_2530, '#skF_2', C_2528, '#skF_4', E_2529, '#skF_6'), C_2528)=E_2529 | ~v1_funct_1(k1_tmap_1(A_2530, '#skF_2', C_2528, '#skF_4', E_2529, '#skF_6')) | k2_partfun1(C_2528, '#skF_2', E_2529, k9_subset_1(A_2530, C_2528, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_2530, C_2528, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_2529, k1_zfmisc_1(k2_zfmisc_1(C_2528, '#skF_2'))) | ~v1_funct_2(E_2529, C_2528, '#skF_2') | ~v1_funct_1(E_2529) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2530)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_2528, k1_zfmisc_1(A_2530)) | v1_xboole_0(C_2528) | v1_xboole_0('#skF_2') | v1_xboole_0(A_2530))), inference(resolution, [status(thm)], [c_62, c_21150])).
% 19.21/9.79  tff(c_21164, plain, (![A_2530, C_2528, E_2529]: (k2_partfun1(k4_subset_1(A_2530, C_2528, '#skF_4'), '#skF_2', k1_tmap_1(A_2530, '#skF_2', C_2528, '#skF_4', E_2529, '#skF_6'), C_2528)=E_2529 | ~v1_funct_1(k1_tmap_1(A_2530, '#skF_2', C_2528, '#skF_4', E_2529, '#skF_6')) | k2_partfun1(C_2528, '#skF_2', E_2529, k9_subset_1(A_2530, C_2528, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2530, C_2528, '#skF_4')) | ~m1_subset_1(E_2529, k1_zfmisc_1(k2_zfmisc_1(C_2528, '#skF_2'))) | ~v1_funct_2(E_2529, C_2528, '#skF_2') | ~v1_funct_1(E_2529) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2530)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_2528, k1_zfmisc_1(A_2530)) | v1_xboole_0(C_2528) | v1_xboole_0('#skF_2') | v1_xboole_0(A_2530))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_15663, c_21157])).
% 19.21/9.79  tff(c_22519, plain, (![A_2640, C_2641, E_2642]: (k2_partfun1(k4_subset_1(A_2640, C_2641, '#skF_4'), '#skF_2', k1_tmap_1(A_2640, '#skF_2', C_2641, '#skF_4', E_2642, '#skF_6'), C_2641)=E_2642 | ~v1_funct_1(k1_tmap_1(A_2640, '#skF_2', C_2641, '#skF_4', E_2642, '#skF_6')) | k2_partfun1(C_2641, '#skF_2', E_2642, k9_subset_1(A_2640, C_2641, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2640, C_2641, '#skF_4')) | ~m1_subset_1(E_2642, k1_zfmisc_1(k2_zfmisc_1(C_2641, '#skF_2'))) | ~v1_funct_2(E_2642, C_2641, '#skF_2') | ~v1_funct_1(E_2642) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2640)) | ~m1_subset_1(C_2641, k1_zfmisc_1(A_2640)) | v1_xboole_0(C_2641) | v1_xboole_0(A_2640))), inference(negUnitSimplification, [status(thm)], [c_84, c_78, c_21164])).
% 19.21/9.79  tff(c_22529, plain, (![A_2640]: (k2_partfun1(k4_subset_1(A_2640, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_2640, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_2640, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_2640, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2640, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2640)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_2640)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2640))), inference(resolution, [status(thm)], [c_68, c_22519])).
% 19.21/9.79  tff(c_22540, plain, (![A_2640]: (k2_partfun1(k4_subset_1(A_2640, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_2640, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_2640, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_2640, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2640, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2640)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_2640)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2640))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_15666, c_22529])).
% 19.21/9.79  tff(c_24470, plain, (![A_2840]: (k2_partfun1(k4_subset_1(A_2840, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_2840, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_2840, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_2840, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2840, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2840)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_2840)) | v1_xboole_0(A_2840))), inference(negUnitSimplification, [status(thm)], [c_82, c_22540])).
% 19.21/9.79  tff(c_2385, plain, (![B_503, A_504]: (k1_relat_1(B_503)=A_504 | ~v1_partfun1(B_503, A_504) | ~v4_relat_1(B_503, A_504) | ~v1_relat_1(B_503))), inference(cnfTransformation, [status(thm)], [f_108])).
% 19.21/9.79  tff(c_2394, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2302, c_2385])).
% 19.21/9.79  tff(c_2403, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2236, c_2394])).
% 19.21/9.79  tff(c_2884, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_2403])).
% 19.21/9.79  tff(c_3113, plain, (![C_567, A_568, B_569]: (v1_partfun1(C_567, A_568) | ~v1_funct_2(C_567, A_568, B_569) | ~v1_funct_1(C_567) | ~m1_subset_1(C_567, k1_zfmisc_1(k2_zfmisc_1(A_568, B_569))) | v1_xboole_0(B_569))), inference(cnfTransformation, [status(thm)], [f_100])).
% 19.21/9.79  tff(c_3120, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_62, c_3113])).
% 19.21/9.79  tff(c_3127, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_3120])).
% 19.21/9.79  tff(c_3129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_2884, c_3127])).
% 19.21/9.79  tff(c_3130, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_2403])).
% 19.21/9.79  tff(c_3138, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6' | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3130, c_2309])).
% 19.21/9.79  tff(c_3147, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2236, c_3138])).
% 19.21/9.79  tff(c_24, plain, (![C_18, A_16, B_17]: (k7_relat_1(k7_relat_1(C_18, A_16), B_17)=k1_xboole_0 | ~r1_xboole_0(A_16, B_17) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_60])).
% 19.21/9.79  tff(c_3164, plain, (![B_17]: (k7_relat_1('#skF_6', B_17)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_17) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3147, c_24])).
% 19.21/9.79  tff(c_3245, plain, (![B_577]: (k7_relat_1('#skF_6', B_577)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_577))), inference(demodulation, [status(thm), theory('equality')], [c_2236, c_3164])).
% 19.21/9.79  tff(c_3262, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_3245])).
% 19.21/9.79  tff(c_2339, plain, (![A_495, B_496]: (r1_xboole_0(A_495, B_496) | ~r1_subset_1(A_495, B_496) | v1_xboole_0(B_496) | v1_xboole_0(A_495))), inference(cnfTransformation, [status(thm)], [f_76])).
% 19.21/9.79  tff(c_3899, plain, (![A_639, B_640]: (k3_xboole_0(A_639, B_640)=k1_xboole_0 | ~r1_subset_1(A_639, B_640) | v1_xboole_0(B_640) | v1_xboole_0(A_639))), inference(resolution, [status(thm)], [c_2339, c_2])).
% 19.21/9.79  tff(c_3902, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_74, c_3899])).
% 19.21/9.79  tff(c_3905, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_82, c_78, c_3902])).
% 19.21/9.79  tff(c_3210, plain, (![A_572, B_573, C_574]: (k9_subset_1(A_572, B_573, C_574)=k3_xboole_0(B_573, C_574) | ~m1_subset_1(C_574, k1_zfmisc_1(A_572)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 19.21/9.79  tff(c_3225, plain, (![B_573]: (k9_subset_1('#skF_1', B_573, '#skF_4')=k3_xboole_0(B_573, '#skF_4'))), inference(resolution, [status(thm)], [c_76, c_3210])).
% 19.21/9.79  tff(c_2391, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2303, c_2385])).
% 19.21/9.79  tff(c_2400, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2237, c_2391])).
% 19.21/9.79  tff(c_2404, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_2400])).
% 19.21/9.79  tff(c_2841, plain, (![C_547, A_548, B_549]: (v1_partfun1(C_547, A_548) | ~v1_funct_2(C_547, A_548, B_549) | ~v1_funct_1(C_547) | ~m1_subset_1(C_547, k1_zfmisc_1(k2_zfmisc_1(A_548, B_549))) | v1_xboole_0(B_549))), inference(cnfTransformation, [status(thm)], [f_100])).
% 19.21/9.79  tff(c_2851, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_2841])).
% 19.21/9.79  tff(c_2859, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_2851])).
% 19.21/9.79  tff(c_2861, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_2404, c_2859])).
% 19.21/9.79  tff(c_2862, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_2400])).
% 19.21/9.79  tff(c_2870, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5' | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2862, c_2309])).
% 19.21/9.79  tff(c_2879, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2237, c_2870])).
% 19.21/9.79  tff(c_3155, plain, (![B_17]: (k7_relat_1('#skF_5', B_17)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_17) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2879, c_24])).
% 19.21/9.79  tff(c_3281, plain, (![B_579]: (k7_relat_1('#skF_5', B_579)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_579))), inference(demodulation, [status(thm), theory('equality')], [c_2237, c_3155])).
% 19.21/9.79  tff(c_3298, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_3281])).
% 19.21/9.79  tff(c_3519, plain, (![B_596, F_597, D_598, E_600, C_599, A_601]: (v1_funct_1(k1_tmap_1(A_601, B_596, C_599, D_598, E_600, F_597)) | ~m1_subset_1(F_597, k1_zfmisc_1(k2_zfmisc_1(D_598, B_596))) | ~v1_funct_2(F_597, D_598, B_596) | ~v1_funct_1(F_597) | ~m1_subset_1(E_600, k1_zfmisc_1(k2_zfmisc_1(C_599, B_596))) | ~v1_funct_2(E_600, C_599, B_596) | ~v1_funct_1(E_600) | ~m1_subset_1(D_598, k1_zfmisc_1(A_601)) | v1_xboole_0(D_598) | ~m1_subset_1(C_599, k1_zfmisc_1(A_601)) | v1_xboole_0(C_599) | v1_xboole_0(B_596) | v1_xboole_0(A_601))), inference(cnfTransformation, [status(thm)], [f_196])).
% 19.21/9.79  tff(c_3524, plain, (![A_601, C_599, E_600]: (v1_funct_1(k1_tmap_1(A_601, '#skF_2', C_599, '#skF_4', E_600, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_600, k1_zfmisc_1(k2_zfmisc_1(C_599, '#skF_2'))) | ~v1_funct_2(E_600, C_599, '#skF_2') | ~v1_funct_1(E_600) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_601)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_599, k1_zfmisc_1(A_601)) | v1_xboole_0(C_599) | v1_xboole_0('#skF_2') | v1_xboole_0(A_601))), inference(resolution, [status(thm)], [c_62, c_3519])).
% 19.21/9.79  tff(c_3530, plain, (![A_601, C_599, E_600]: (v1_funct_1(k1_tmap_1(A_601, '#skF_2', C_599, '#skF_4', E_600, '#skF_6')) | ~m1_subset_1(E_600, k1_zfmisc_1(k2_zfmisc_1(C_599, '#skF_2'))) | ~v1_funct_2(E_600, C_599, '#skF_2') | ~v1_funct_1(E_600) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_601)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_599, k1_zfmisc_1(A_601)) | v1_xboole_0(C_599) | v1_xboole_0('#skF_2') | v1_xboole_0(A_601))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_3524])).
% 19.21/9.79  tff(c_4130, plain, (![A_680, C_681, E_682]: (v1_funct_1(k1_tmap_1(A_680, '#skF_2', C_681, '#skF_4', E_682, '#skF_6')) | ~m1_subset_1(E_682, k1_zfmisc_1(k2_zfmisc_1(C_681, '#skF_2'))) | ~v1_funct_2(E_682, C_681, '#skF_2') | ~v1_funct_1(E_682) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_680)) | ~m1_subset_1(C_681, k1_zfmisc_1(A_680)) | v1_xboole_0(C_681) | v1_xboole_0(A_680))), inference(negUnitSimplification, [status(thm)], [c_84, c_78, c_3530])).
% 19.21/9.79  tff(c_4140, plain, (![A_680]: (v1_funct_1(k1_tmap_1(A_680, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_680)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_680)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_680))), inference(resolution, [status(thm)], [c_68, c_4130])).
% 19.21/9.79  tff(c_4151, plain, (![A_680]: (v1_funct_1(k1_tmap_1(A_680, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_680)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_680)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_680))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_4140])).
% 19.21/9.79  tff(c_4226, plain, (![A_694]: (v1_funct_1(k1_tmap_1(A_694, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_694)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_694)) | v1_xboole_0(A_694))), inference(negUnitSimplification, [status(thm)], [c_82, c_4151])).
% 19.21/9.79  tff(c_4233, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_80, c_4226])).
% 19.21/9.79  tff(c_4237, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_4233])).
% 19.21/9.79  tff(c_4238, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_86, c_4237])).
% 19.21/9.79  tff(c_3346, plain, (![A_582, B_583, C_584, D_585]: (k2_partfun1(A_582, B_583, C_584, D_585)=k7_relat_1(C_584, D_585) | ~m1_subset_1(C_584, k1_zfmisc_1(k2_zfmisc_1(A_582, B_583))) | ~v1_funct_1(C_584))), inference(cnfTransformation, [status(thm)], [f_114])).
% 19.21/9.79  tff(c_3353, plain, (![D_585]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_585)=k7_relat_1('#skF_5', D_585) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_68, c_3346])).
% 19.21/9.79  tff(c_3360, plain, (![D_585]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_585)=k7_relat_1('#skF_5', D_585))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_3353])).
% 19.21/9.79  tff(c_3351, plain, (![D_585]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_585)=k7_relat_1('#skF_6', D_585) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_62, c_3346])).
% 19.21/9.79  tff(c_3357, plain, (![D_585]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_585)=k7_relat_1('#skF_6', D_585))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_3351])).
% 19.21/9.79  tff(c_3910, plain, (![A_641, C_645, F_644, E_643, D_642, B_646]: (k2_partfun1(k4_subset_1(A_641, C_645, D_642), B_646, k1_tmap_1(A_641, B_646, C_645, D_642, E_643, F_644), D_642)=F_644 | ~m1_subset_1(k1_tmap_1(A_641, B_646, C_645, D_642, E_643, F_644), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_641, C_645, D_642), B_646))) | ~v1_funct_2(k1_tmap_1(A_641, B_646, C_645, D_642, E_643, F_644), k4_subset_1(A_641, C_645, D_642), B_646) | ~v1_funct_1(k1_tmap_1(A_641, B_646, C_645, D_642, E_643, F_644)) | k2_partfun1(D_642, B_646, F_644, k9_subset_1(A_641, C_645, D_642))!=k2_partfun1(C_645, B_646, E_643, k9_subset_1(A_641, C_645, D_642)) | ~m1_subset_1(F_644, k1_zfmisc_1(k2_zfmisc_1(D_642, B_646))) | ~v1_funct_2(F_644, D_642, B_646) | ~v1_funct_1(F_644) | ~m1_subset_1(E_643, k1_zfmisc_1(k2_zfmisc_1(C_645, B_646))) | ~v1_funct_2(E_643, C_645, B_646) | ~v1_funct_1(E_643) | ~m1_subset_1(D_642, k1_zfmisc_1(A_641)) | v1_xboole_0(D_642) | ~m1_subset_1(C_645, k1_zfmisc_1(A_641)) | v1_xboole_0(C_645) | v1_xboole_0(B_646) | v1_xboole_0(A_641))), inference(cnfTransformation, [status(thm)], [f_162])).
% 19.21/9.79  tff(c_5777, plain, (![E_869, D_867, F_866, A_870, C_868, B_865]: (k2_partfun1(k4_subset_1(A_870, C_868, D_867), B_865, k1_tmap_1(A_870, B_865, C_868, D_867, E_869, F_866), D_867)=F_866 | ~v1_funct_2(k1_tmap_1(A_870, B_865, C_868, D_867, E_869, F_866), k4_subset_1(A_870, C_868, D_867), B_865) | ~v1_funct_1(k1_tmap_1(A_870, B_865, C_868, D_867, E_869, F_866)) | k2_partfun1(D_867, B_865, F_866, k9_subset_1(A_870, C_868, D_867))!=k2_partfun1(C_868, B_865, E_869, k9_subset_1(A_870, C_868, D_867)) | ~m1_subset_1(F_866, k1_zfmisc_1(k2_zfmisc_1(D_867, B_865))) | ~v1_funct_2(F_866, D_867, B_865) | ~v1_funct_1(F_866) | ~m1_subset_1(E_869, k1_zfmisc_1(k2_zfmisc_1(C_868, B_865))) | ~v1_funct_2(E_869, C_868, B_865) | ~v1_funct_1(E_869) | ~m1_subset_1(D_867, k1_zfmisc_1(A_870)) | v1_xboole_0(D_867) | ~m1_subset_1(C_868, k1_zfmisc_1(A_870)) | v1_xboole_0(C_868) | v1_xboole_0(B_865) | v1_xboole_0(A_870))), inference(resolution, [status(thm)], [c_54, c_3910])).
% 19.21/9.79  tff(c_8847, plain, (![E_1284, C_1283, D_1282, A_1285, B_1280, F_1281]: (k2_partfun1(k4_subset_1(A_1285, C_1283, D_1282), B_1280, k1_tmap_1(A_1285, B_1280, C_1283, D_1282, E_1284, F_1281), D_1282)=F_1281 | ~v1_funct_1(k1_tmap_1(A_1285, B_1280, C_1283, D_1282, E_1284, F_1281)) | k2_partfun1(D_1282, B_1280, F_1281, k9_subset_1(A_1285, C_1283, D_1282))!=k2_partfun1(C_1283, B_1280, E_1284, k9_subset_1(A_1285, C_1283, D_1282)) | ~m1_subset_1(F_1281, k1_zfmisc_1(k2_zfmisc_1(D_1282, B_1280))) | ~v1_funct_2(F_1281, D_1282, B_1280) | ~v1_funct_1(F_1281) | ~m1_subset_1(E_1284, k1_zfmisc_1(k2_zfmisc_1(C_1283, B_1280))) | ~v1_funct_2(E_1284, C_1283, B_1280) | ~v1_funct_1(E_1284) | ~m1_subset_1(D_1282, k1_zfmisc_1(A_1285)) | v1_xboole_0(D_1282) | ~m1_subset_1(C_1283, k1_zfmisc_1(A_1285)) | v1_xboole_0(C_1283) | v1_xboole_0(B_1280) | v1_xboole_0(A_1285))), inference(resolution, [status(thm)], [c_56, c_5777])).
% 19.21/9.79  tff(c_8854, plain, (![A_1285, C_1283, E_1284]: (k2_partfun1(k4_subset_1(A_1285, C_1283, '#skF_4'), '#skF_2', k1_tmap_1(A_1285, '#skF_2', C_1283, '#skF_4', E_1284, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1285, '#skF_2', C_1283, '#skF_4', E_1284, '#skF_6')) | k2_partfun1(C_1283, '#skF_2', E_1284, k9_subset_1(A_1285, C_1283, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_1285, C_1283, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1284, k1_zfmisc_1(k2_zfmisc_1(C_1283, '#skF_2'))) | ~v1_funct_2(E_1284, C_1283, '#skF_2') | ~v1_funct_1(E_1284) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1285)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1283, k1_zfmisc_1(A_1285)) | v1_xboole_0(C_1283) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1285))), inference(resolution, [status(thm)], [c_62, c_8847])).
% 19.21/9.79  tff(c_8861, plain, (![A_1285, C_1283, E_1284]: (k2_partfun1(k4_subset_1(A_1285, C_1283, '#skF_4'), '#skF_2', k1_tmap_1(A_1285, '#skF_2', C_1283, '#skF_4', E_1284, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1285, '#skF_2', C_1283, '#skF_4', E_1284, '#skF_6')) | k2_partfun1(C_1283, '#skF_2', E_1284, k9_subset_1(A_1285, C_1283, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1285, C_1283, '#skF_4')) | ~m1_subset_1(E_1284, k1_zfmisc_1(k2_zfmisc_1(C_1283, '#skF_2'))) | ~v1_funct_2(E_1284, C_1283, '#skF_2') | ~v1_funct_1(E_1284) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1285)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1283, k1_zfmisc_1(A_1285)) | v1_xboole_0(C_1283) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1285))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_3357, c_8854])).
% 19.21/9.79  tff(c_10141, plain, (![A_1390, C_1391, E_1392]: (k2_partfun1(k4_subset_1(A_1390, C_1391, '#skF_4'), '#skF_2', k1_tmap_1(A_1390, '#skF_2', C_1391, '#skF_4', E_1392, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1390, '#skF_2', C_1391, '#skF_4', E_1392, '#skF_6')) | k2_partfun1(C_1391, '#skF_2', E_1392, k9_subset_1(A_1390, C_1391, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1390, C_1391, '#skF_4')) | ~m1_subset_1(E_1392, k1_zfmisc_1(k2_zfmisc_1(C_1391, '#skF_2'))) | ~v1_funct_2(E_1392, C_1391, '#skF_2') | ~v1_funct_1(E_1392) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1390)) | ~m1_subset_1(C_1391, k1_zfmisc_1(A_1390)) | v1_xboole_0(C_1391) | v1_xboole_0(A_1390))), inference(negUnitSimplification, [status(thm)], [c_84, c_78, c_8861])).
% 19.21/9.79  tff(c_10151, plain, (![A_1390]: (k2_partfun1(k4_subset_1(A_1390, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1390, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1390, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_1390, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1390, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1390)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1390)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1390))), inference(resolution, [status(thm)], [c_68, c_10141])).
% 19.21/9.79  tff(c_10162, plain, (![A_1390]: (k2_partfun1(k4_subset_1(A_1390, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1390, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1390, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1390, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1390, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1390)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1390)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1390))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_3360, c_10151])).
% 19.21/9.79  tff(c_14112, plain, (![A_1719]: (k2_partfun1(k4_subset_1(A_1719, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1719, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1719, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1719, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1719, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1719)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1719)) | v1_xboole_0(A_1719))), inference(negUnitSimplification, [status(thm)], [c_82, c_10162])).
% 19.21/9.79  tff(c_207, plain, (![C_248, A_249, B_250]: (v1_relat_1(C_248) | ~m1_subset_1(C_248, k1_zfmisc_1(k2_zfmisc_1(A_249, B_250))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 19.21/9.79  tff(c_219, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_62, c_207])).
% 19.21/9.79  tff(c_239, plain, (![C_256, A_257, B_258]: (v4_relat_1(C_256, A_257) | ~m1_subset_1(C_256, k1_zfmisc_1(k2_zfmisc_1(A_257, B_258))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 19.21/9.79  tff(c_251, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_62, c_239])).
% 19.21/9.79  tff(c_364, plain, (![B_283, A_284]: (k1_relat_1(B_283)=A_284 | ~v1_partfun1(B_283, A_284) | ~v4_relat_1(B_283, A_284) | ~v1_relat_1(B_283))), inference(cnfTransformation, [status(thm)], [f_108])).
% 19.21/9.79  tff(c_373, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_251, c_364])).
% 19.21/9.79  tff(c_382, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_219, c_373])).
% 19.21/9.79  tff(c_891, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_382])).
% 19.21/9.79  tff(c_1120, plain, (![C_349, A_350, B_351]: (v1_partfun1(C_349, A_350) | ~v1_funct_2(C_349, A_350, B_351) | ~v1_funct_1(C_349) | ~m1_subset_1(C_349, k1_zfmisc_1(k2_zfmisc_1(A_350, B_351))) | v1_xboole_0(B_351))), inference(cnfTransformation, [status(thm)], [f_100])).
% 19.21/9.79  tff(c_1127, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_62, c_1120])).
% 19.21/9.80  tff(c_1134, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1127])).
% 19.21/9.80  tff(c_1136, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_891, c_1134])).
% 19.21/9.80  tff(c_1137, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_382])).
% 19.21/9.80  tff(c_302, plain, (![B_272, A_273]: (k7_relat_1(B_272, A_273)=B_272 | ~r1_tarski(k1_relat_1(B_272), A_273) | ~v1_relat_1(B_272))), inference(cnfTransformation, [status(thm)], [f_66])).
% 19.21/9.80  tff(c_307, plain, (![B_272]: (k7_relat_1(B_272, k1_relat_1(B_272))=B_272 | ~v1_relat_1(B_272))), inference(resolution, [status(thm)], [c_10, c_302])).
% 19.21/9.80  tff(c_1145, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6' | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1137, c_307])).
% 19.21/9.80  tff(c_1154, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_219, c_1145])).
% 19.21/9.80  tff(c_1171, plain, (![B_17]: (k7_relat_1('#skF_6', B_17)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_17) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1154, c_24])).
% 19.21/9.80  tff(c_1252, plain, (![B_359]: (k7_relat_1('#skF_6', B_359)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_359))), inference(demodulation, [status(thm), theory('equality')], [c_219, c_1171])).
% 19.21/9.80  tff(c_1269, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_1252])).
% 19.21/9.80  tff(c_318, plain, (![A_275, B_276]: (r1_xboole_0(A_275, B_276) | ~r1_subset_1(A_275, B_276) | v1_xboole_0(B_276) | v1_xboole_0(A_275))), inference(cnfTransformation, [status(thm)], [f_76])).
% 19.21/9.80  tff(c_1906, plain, (![A_421, B_422]: (k3_xboole_0(A_421, B_422)=k1_xboole_0 | ~r1_subset_1(A_421, B_422) | v1_xboole_0(B_422) | v1_xboole_0(A_421))), inference(resolution, [status(thm)], [c_318, c_2])).
% 19.21/9.80  tff(c_1909, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_74, c_1906])).
% 19.21/9.80  tff(c_1912, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_82, c_78, c_1909])).
% 19.21/9.80  tff(c_220, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_68, c_207])).
% 19.21/9.80  tff(c_252, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_239])).
% 19.21/9.80  tff(c_370, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_252, c_364])).
% 19.21/9.80  tff(c_379, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_220, c_370])).
% 19.21/9.80  tff(c_383, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_379])).
% 19.21/9.80  tff(c_848, plain, (![C_329, A_330, B_331]: (v1_partfun1(C_329, A_330) | ~v1_funct_2(C_329, A_330, B_331) | ~v1_funct_1(C_329) | ~m1_subset_1(C_329, k1_zfmisc_1(k2_zfmisc_1(A_330, B_331))) | v1_xboole_0(B_331))), inference(cnfTransformation, [status(thm)], [f_100])).
% 19.21/9.80  tff(c_858, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_848])).
% 19.21/9.80  tff(c_866, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_858])).
% 19.21/9.80  tff(c_868, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_383, c_866])).
% 19.21/9.80  tff(c_869, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_379])).
% 19.21/9.80  tff(c_877, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5' | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_869, c_307])).
% 19.21/9.80  tff(c_886, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_220, c_877])).
% 19.21/9.80  tff(c_1162, plain, (![B_17]: (k7_relat_1('#skF_5', B_17)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_17) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_886, c_24])).
% 19.21/9.80  tff(c_1288, plain, (![B_361]: (k7_relat_1('#skF_5', B_361)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_361))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_1162])).
% 19.21/9.80  tff(c_1305, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_1288])).
% 19.21/9.80  tff(c_1353, plain, (![A_364, B_365, C_366, D_367]: (k2_partfun1(A_364, B_365, C_366, D_367)=k7_relat_1(C_366, D_367) | ~m1_subset_1(C_366, k1_zfmisc_1(k2_zfmisc_1(A_364, B_365))) | ~v1_funct_1(C_366))), inference(cnfTransformation, [status(thm)], [f_114])).
% 19.21/9.80  tff(c_1360, plain, (![D_367]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_367)=k7_relat_1('#skF_5', D_367) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_68, c_1353])).
% 19.21/9.80  tff(c_1367, plain, (![D_367]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_367)=k7_relat_1('#skF_5', D_367))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1360])).
% 19.21/9.80  tff(c_1358, plain, (![D_367]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_367)=k7_relat_1('#skF_6', D_367) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_62, c_1353])).
% 19.21/9.80  tff(c_1364, plain, (![D_367]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_367)=k7_relat_1('#skF_6', D_367))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1358])).
% 19.21/9.80  tff(c_1217, plain, (![A_354, B_355, C_356]: (k9_subset_1(A_354, B_355, C_356)=k3_xboole_0(B_355, C_356) | ~m1_subset_1(C_356, k1_zfmisc_1(A_354)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 19.21/9.80  tff(c_1232, plain, (![B_355]: (k9_subset_1('#skF_1', B_355, '#skF_4')=k3_xboole_0(B_355, '#skF_4'))), inference(resolution, [status(thm)], [c_76, c_1217])).
% 19.21/9.80  tff(c_60, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_238])).
% 19.21/9.80  tff(c_108, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_60])).
% 19.21/9.80  tff(c_1242, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1232, c_1232, c_108])).
% 19.21/9.80  tff(c_2122, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1269, c_1912, c_1305, c_1912, c_1367, c_1364, c_1242])).
% 19.21/9.80  tff(c_2123, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_60])).
% 19.21/9.80  tff(c_2319, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_2123])).
% 19.21/9.80  tff(c_14145, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14112, c_2319])).
% 19.21/9.80  tff(c_14187, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_3262, c_3905, c_3225, c_3298, c_3905, c_3225, c_4238, c_14145])).
% 19.21/9.80  tff(c_14189, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_14187])).
% 19.21/9.80  tff(c_14190, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_2123])).
% 19.21/9.80  tff(c_24493, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_24470, c_14190])).
% 19.21/9.80  tff(c_24529, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_15456, c_15483, c_16125, c_15571, c_16125, c_15571, c_16462, c_24493])).
% 19.21/9.80  tff(c_24531, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_24529])).
% 19.21/9.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.21/9.80  
% 19.21/9.80  Inference rules
% 19.21/9.80  ----------------------
% 19.21/9.80  #Ref     : 0
% 19.21/9.80  #Sup     : 4984
% 19.21/9.80  #Fact    : 0
% 19.21/9.80  #Define  : 0
% 19.21/9.80  #Split   : 152
% 19.21/9.80  #Chain   : 0
% 19.21/9.80  #Close   : 0
% 19.21/9.80  
% 19.21/9.80  Ordering : KBO
% 19.21/9.80  
% 19.21/9.80  Simplification rules
% 19.21/9.80  ----------------------
% 19.21/9.80  #Subsume      : 1503
% 19.21/9.80  #Demod        : 5376
% 19.21/9.80  #Tautology    : 1505
% 19.21/9.80  #SimpNegUnit  : 1422
% 19.21/9.80  #BackRed      : 302
% 19.21/9.80  
% 19.21/9.80  #Partial instantiations: 0
% 19.21/9.80  #Strategies tried      : 1
% 19.21/9.80  
% 19.21/9.80  Timing (in seconds)
% 19.21/9.80  ----------------------
% 19.21/9.80  Preprocessing        : 0.43
% 19.21/9.80  Parsing              : 0.21
% 19.21/9.80  CNF conversion       : 0.06
% 19.21/9.80  Main loop            : 8.57
% 19.21/9.80  Inferencing          : 2.27
% 19.21/9.80  Reduction            : 2.97
% 19.21/9.80  Demodulation         : 2.22
% 19.21/9.80  BG Simplification    : 0.18
% 19.21/9.80  Subsumption          : 2.78
% 19.21/9.80  Abstraction          : 0.32
% 19.21/9.80  MUC search           : 0.00
% 19.21/9.80  Cooper               : 0.00
% 19.21/9.80  Total                : 9.07
% 19.21/9.80  Index Insertion      : 0.00
% 19.21/9.80  Index Deletion       : 0.00
% 19.21/9.80  Index Matching       : 0.00
% 19.21/9.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
