%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:09 EST 2020

% Result     : Theorem 30.94s
% Output     : CNFRefutation 31.20s
% Verified   : 
% Statistics : Number of formulae       :  255 ( 654 expanded)
%              Number of leaves         :   51 ( 253 expanded)
%              Depth                    :   12
%              Number of atoms          :  795 (3359 expanded)
%              Number of equality atoms :  152 ( 589 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_264,negated_conjecture,(
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

tff(f_30,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_102,axiom,(
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

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_222,axiom,(
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

tff(f_140,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_188,axiom,(
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

tff(f_134,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_126,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

tff(c_94,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_88,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_84,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_18,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_26,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_46019,plain,(
    ! [C_2098,B_2099,A_2100] :
      ( ~ v1_xboole_0(C_2098)
      | ~ m1_subset_1(B_2099,k1_zfmisc_1(C_2098))
      | ~ r2_hidden(A_2100,B_2099) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_46035,plain,(
    ! [B_2101,A_2102,A_2103] :
      ( ~ v1_xboole_0(B_2101)
      | ~ r2_hidden(A_2102,A_2103)
      | ~ r1_tarski(A_2103,B_2101) ) ),
    inference(resolution,[status(thm)],[c_26,c_46019])).

tff(c_46106,plain,(
    ! [B_2120,B_2121,A_2122] :
      ( ~ v1_xboole_0(B_2120)
      | ~ r1_tarski(B_2121,B_2120)
      | r1_xboole_0(A_2122,B_2121) ) ),
    inference(resolution,[status(thm)],[c_10,c_46035])).

tff(c_46121,plain,(
    ! [B_9,A_2122] :
      ( ~ v1_xboole_0(B_9)
      | r1_xboole_0(A_2122,B_9) ) ),
    inference(resolution,[status(thm)],[c_18,c_46106])).

tff(c_76,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_45985,plain,(
    ! [C_2086,A_2087,B_2088] :
      ( v1_relat_1(C_2086)
      | ~ m1_subset_1(C_2086,k1_zfmisc_1(k2_zfmisc_1(A_2087,B_2088))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_45998,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_45985])).

tff(c_46122,plain,(
    ! [C_2123,A_2124,B_2125] :
      ( v4_relat_1(C_2123,A_2124)
      | ~ m1_subset_1(C_2123,k1_zfmisc_1(k2_zfmisc_1(A_2124,B_2125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_46135,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_46122])).

tff(c_34,plain,(
    ! [B_27,A_26] :
      ( k7_relat_1(B_27,A_26) = B_27
      | ~ v4_relat_1(B_27,A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_46144,plain,
    ( k7_relat_1('#skF_6','#skF_4') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46135,c_34])).

tff(c_46147,plain,(
    k7_relat_1('#skF_6','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45998,c_46144])).

tff(c_47818,plain,(
    ! [C_2287,A_2288,B_2289] :
      ( k7_relat_1(k7_relat_1(C_2287,A_2288),B_2289) = k1_xboole_0
      | ~ r1_xboole_0(A_2288,B_2289)
      | ~ v1_relat_1(C_2287) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_47853,plain,(
    ! [B_2289] :
      ( k7_relat_1('#skF_6',B_2289) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_2289)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46147,c_47818])).

tff(c_47869,plain,(
    ! [B_2290] :
      ( k7_relat_1('#skF_6',B_2290) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_2290) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45998,c_47853])).

tff(c_47892,plain,(
    ! [B_2291] :
      ( k7_relat_1('#skF_6',B_2291) = k1_xboole_0
      | ~ v1_xboole_0(B_2291) ) ),
    inference(resolution,[status(thm)],[c_46121,c_47869])).

tff(c_47896,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_47892])).

tff(c_90,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_86,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_82,plain,(
    r1_subset_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_46240,plain,(
    ! [A_2147,B_2148] :
      ( r1_xboole_0(A_2147,B_2148)
      | ~ r1_subset_1(A_2147,B_2148)
      | v1_xboole_0(B_2148)
      | v1_xboole_0(A_2147) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48512,plain,(
    ! [A_2371,B_2372] :
      ( k3_xboole_0(A_2371,B_2372) = k1_xboole_0
      | ~ r1_subset_1(A_2371,B_2372)
      | v1_xboole_0(B_2372)
      | v1_xboole_0(A_2371) ) ),
    inference(resolution,[status(thm)],[c_46240,c_2])).

tff(c_48515,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_48512])).

tff(c_48518,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_86,c_48515])).

tff(c_47736,plain,(
    ! [A_2275,B_2276,C_2277] :
      ( k9_subset_1(A_2275,B_2276,C_2277) = k3_xboole_0(B_2276,C_2277)
      | ~ m1_subset_1(C_2277,k1_zfmisc_1(A_2275)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_47751,plain,(
    ! [B_2276] : k9_subset_1('#skF_2',B_2276,'#skF_5') = k3_xboole_0(B_2276,'#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_47736])).

tff(c_70,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_45997,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_45985])).

tff(c_46134,plain,(
    v4_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_46122])).

tff(c_46138,plain,
    ( k7_relat_1('#skF_7','#skF_5') = '#skF_7'
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_46134,c_34])).

tff(c_46141,plain,(
    k7_relat_1('#skF_7','#skF_5') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45997,c_46138])).

tff(c_47856,plain,(
    ! [B_2289] :
      ( k7_relat_1('#skF_7',B_2289) = k1_xboole_0
      | ~ r1_xboole_0('#skF_5',B_2289)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46141,c_47818])).

tff(c_47921,plain,(
    ! [B_2296] :
      ( k7_relat_1('#skF_7',B_2296) = k1_xboole_0
      | ~ r1_xboole_0('#skF_5',B_2296) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45997,c_47856])).

tff(c_47944,plain,(
    ! [B_2297] :
      ( k7_relat_1('#skF_7',B_2297) = k1_xboole_0
      | ~ v1_xboole_0(B_2297) ) ),
    inference(resolution,[status(thm)],[c_46121,c_47921])).

tff(c_47948,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_47944])).

tff(c_80,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_78,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_92,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_74,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_72,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_48116,plain,(
    ! [C_2308,B_2311,F_2313,A_2309,D_2312,E_2310] :
      ( v1_funct_1(k1_tmap_1(A_2309,B_2311,C_2308,D_2312,E_2310,F_2313))
      | ~ m1_subset_1(F_2313,k1_zfmisc_1(k2_zfmisc_1(D_2312,B_2311)))
      | ~ v1_funct_2(F_2313,D_2312,B_2311)
      | ~ v1_funct_1(F_2313)
      | ~ m1_subset_1(E_2310,k1_zfmisc_1(k2_zfmisc_1(C_2308,B_2311)))
      | ~ v1_funct_2(E_2310,C_2308,B_2311)
      | ~ v1_funct_1(E_2310)
      | ~ m1_subset_1(D_2312,k1_zfmisc_1(A_2309))
      | v1_xboole_0(D_2312)
      | ~ m1_subset_1(C_2308,k1_zfmisc_1(A_2309))
      | v1_xboole_0(C_2308)
      | v1_xboole_0(B_2311)
      | v1_xboole_0(A_2309) ) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_48121,plain,(
    ! [A_2309,C_2308,E_2310] :
      ( v1_funct_1(k1_tmap_1(A_2309,'#skF_3',C_2308,'#skF_5',E_2310,'#skF_7'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_2310,k1_zfmisc_1(k2_zfmisc_1(C_2308,'#skF_3')))
      | ~ v1_funct_2(E_2310,C_2308,'#skF_3')
      | ~ v1_funct_1(E_2310)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2309))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_2308,k1_zfmisc_1(A_2309))
      | v1_xboole_0(C_2308)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2309) ) ),
    inference(resolution,[status(thm)],[c_70,c_48116])).

tff(c_48127,plain,(
    ! [A_2309,C_2308,E_2310] :
      ( v1_funct_1(k1_tmap_1(A_2309,'#skF_3',C_2308,'#skF_5',E_2310,'#skF_7'))
      | ~ m1_subset_1(E_2310,k1_zfmisc_1(k2_zfmisc_1(C_2308,'#skF_3')))
      | ~ v1_funct_2(E_2310,C_2308,'#skF_3')
      | ~ v1_funct_1(E_2310)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2309))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_2308,k1_zfmisc_1(A_2309))
      | v1_xboole_0(C_2308)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2309) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_48121])).

tff(c_48192,plain,(
    ! [A_2315,C_2316,E_2317] :
      ( v1_funct_1(k1_tmap_1(A_2315,'#skF_3',C_2316,'#skF_5',E_2317,'#skF_7'))
      | ~ m1_subset_1(E_2317,k1_zfmisc_1(k2_zfmisc_1(C_2316,'#skF_3')))
      | ~ v1_funct_2(E_2317,C_2316,'#skF_3')
      | ~ v1_funct_1(E_2317)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2315))
      | ~ m1_subset_1(C_2316,k1_zfmisc_1(A_2315))
      | v1_xboole_0(C_2316)
      | v1_xboole_0(A_2315) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_86,c_48127])).

tff(c_48199,plain,(
    ! [A_2315] :
      ( v1_funct_1(k1_tmap_1(A_2315,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2315))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2315))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_2315) ) ),
    inference(resolution,[status(thm)],[c_76,c_48192])).

tff(c_48207,plain,(
    ! [A_2315] :
      ( v1_funct_1(k1_tmap_1(A_2315,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2315))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2315))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_2315) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_48199])).

tff(c_48457,plain,(
    ! [A_2360] :
      ( v1_funct_1(k1_tmap_1(A_2360,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2360))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2360))
      | v1_xboole_0(A_2360) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_48207])).

tff(c_48464,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_48457])).

tff(c_48468,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_48464])).

tff(c_48469,plain,(
    v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_48468])).

tff(c_47897,plain,(
    ! [A_2292,B_2293,C_2294,D_2295] :
      ( k2_partfun1(A_2292,B_2293,C_2294,D_2295) = k7_relat_1(C_2294,D_2295)
      | ~ m1_subset_1(C_2294,k1_zfmisc_1(k2_zfmisc_1(A_2292,B_2293)))
      | ~ v1_funct_1(C_2294) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_47904,plain,(
    ! [D_2295] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_6',D_2295) = k7_relat_1('#skF_6',D_2295)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_76,c_47897])).

tff(c_47911,plain,(
    ! [D_2295] : k2_partfun1('#skF_4','#skF_3','#skF_6',D_2295) = k7_relat_1('#skF_6',D_2295) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_47904])).

tff(c_47902,plain,(
    ! [D_2295] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_7',D_2295) = k7_relat_1('#skF_7',D_2295)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_70,c_47897])).

tff(c_47908,plain,(
    ! [D_2295] : k2_partfun1('#skF_5','#skF_3','#skF_7',D_2295) = k7_relat_1('#skF_7',D_2295) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_47902])).

tff(c_64,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_62,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_48477,plain,(
    ! [C_2366,F_2362,E_2363,D_2365,B_2364,A_2367] :
      ( k2_partfun1(k4_subset_1(A_2367,C_2366,D_2365),B_2364,k1_tmap_1(A_2367,B_2364,C_2366,D_2365,E_2363,F_2362),C_2366) = E_2363
      | ~ m1_subset_1(k1_tmap_1(A_2367,B_2364,C_2366,D_2365,E_2363,F_2362),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_2367,C_2366,D_2365),B_2364)))
      | ~ v1_funct_2(k1_tmap_1(A_2367,B_2364,C_2366,D_2365,E_2363,F_2362),k4_subset_1(A_2367,C_2366,D_2365),B_2364)
      | ~ v1_funct_1(k1_tmap_1(A_2367,B_2364,C_2366,D_2365,E_2363,F_2362))
      | k2_partfun1(D_2365,B_2364,F_2362,k9_subset_1(A_2367,C_2366,D_2365)) != k2_partfun1(C_2366,B_2364,E_2363,k9_subset_1(A_2367,C_2366,D_2365))
      | ~ m1_subset_1(F_2362,k1_zfmisc_1(k2_zfmisc_1(D_2365,B_2364)))
      | ~ v1_funct_2(F_2362,D_2365,B_2364)
      | ~ v1_funct_1(F_2362)
      | ~ m1_subset_1(E_2363,k1_zfmisc_1(k2_zfmisc_1(C_2366,B_2364)))
      | ~ v1_funct_2(E_2363,C_2366,B_2364)
      | ~ v1_funct_1(E_2363)
      | ~ m1_subset_1(D_2365,k1_zfmisc_1(A_2367))
      | v1_xboole_0(D_2365)
      | ~ m1_subset_1(C_2366,k1_zfmisc_1(A_2367))
      | v1_xboole_0(C_2366)
      | v1_xboole_0(B_2364)
      | v1_xboole_0(A_2367) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_81679,plain,(
    ! [A_3822,C_3821,B_3824,E_3823,F_3826,D_3825] :
      ( k2_partfun1(k4_subset_1(A_3822,C_3821,D_3825),B_3824,k1_tmap_1(A_3822,B_3824,C_3821,D_3825,E_3823,F_3826),C_3821) = E_3823
      | ~ v1_funct_2(k1_tmap_1(A_3822,B_3824,C_3821,D_3825,E_3823,F_3826),k4_subset_1(A_3822,C_3821,D_3825),B_3824)
      | ~ v1_funct_1(k1_tmap_1(A_3822,B_3824,C_3821,D_3825,E_3823,F_3826))
      | k2_partfun1(D_3825,B_3824,F_3826,k9_subset_1(A_3822,C_3821,D_3825)) != k2_partfun1(C_3821,B_3824,E_3823,k9_subset_1(A_3822,C_3821,D_3825))
      | ~ m1_subset_1(F_3826,k1_zfmisc_1(k2_zfmisc_1(D_3825,B_3824)))
      | ~ v1_funct_2(F_3826,D_3825,B_3824)
      | ~ v1_funct_1(F_3826)
      | ~ m1_subset_1(E_3823,k1_zfmisc_1(k2_zfmisc_1(C_3821,B_3824)))
      | ~ v1_funct_2(E_3823,C_3821,B_3824)
      | ~ v1_funct_1(E_3823)
      | ~ m1_subset_1(D_3825,k1_zfmisc_1(A_3822))
      | v1_xboole_0(D_3825)
      | ~ m1_subset_1(C_3821,k1_zfmisc_1(A_3822))
      | v1_xboole_0(C_3821)
      | v1_xboole_0(B_3824)
      | v1_xboole_0(A_3822) ) ),
    inference(resolution,[status(thm)],[c_62,c_48477])).

tff(c_91551,plain,(
    ! [C_4206,B_4209,E_4208,D_4210,A_4207,F_4211] :
      ( k2_partfun1(k4_subset_1(A_4207,C_4206,D_4210),B_4209,k1_tmap_1(A_4207,B_4209,C_4206,D_4210,E_4208,F_4211),C_4206) = E_4208
      | ~ v1_funct_1(k1_tmap_1(A_4207,B_4209,C_4206,D_4210,E_4208,F_4211))
      | k2_partfun1(D_4210,B_4209,F_4211,k9_subset_1(A_4207,C_4206,D_4210)) != k2_partfun1(C_4206,B_4209,E_4208,k9_subset_1(A_4207,C_4206,D_4210))
      | ~ m1_subset_1(F_4211,k1_zfmisc_1(k2_zfmisc_1(D_4210,B_4209)))
      | ~ v1_funct_2(F_4211,D_4210,B_4209)
      | ~ v1_funct_1(F_4211)
      | ~ m1_subset_1(E_4208,k1_zfmisc_1(k2_zfmisc_1(C_4206,B_4209)))
      | ~ v1_funct_2(E_4208,C_4206,B_4209)
      | ~ v1_funct_1(E_4208)
      | ~ m1_subset_1(D_4210,k1_zfmisc_1(A_4207))
      | v1_xboole_0(D_4210)
      | ~ m1_subset_1(C_4206,k1_zfmisc_1(A_4207))
      | v1_xboole_0(C_4206)
      | v1_xboole_0(B_4209)
      | v1_xboole_0(A_4207) ) ),
    inference(resolution,[status(thm)],[c_64,c_81679])).

tff(c_91560,plain,(
    ! [A_4207,C_4206,E_4208] :
      ( k2_partfun1(k4_subset_1(A_4207,C_4206,'#skF_5'),'#skF_3',k1_tmap_1(A_4207,'#skF_3',C_4206,'#skF_5',E_4208,'#skF_7'),C_4206) = E_4208
      | ~ v1_funct_1(k1_tmap_1(A_4207,'#skF_3',C_4206,'#skF_5',E_4208,'#skF_7'))
      | k2_partfun1(C_4206,'#skF_3',E_4208,k9_subset_1(A_4207,C_4206,'#skF_5')) != k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1(A_4207,C_4206,'#skF_5'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_4208,k1_zfmisc_1(k2_zfmisc_1(C_4206,'#skF_3')))
      | ~ v1_funct_2(E_4208,C_4206,'#skF_3')
      | ~ v1_funct_1(E_4208)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4207))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_4206,k1_zfmisc_1(A_4207))
      | v1_xboole_0(C_4206)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_4207) ) ),
    inference(resolution,[status(thm)],[c_70,c_91551])).

tff(c_91568,plain,(
    ! [A_4207,C_4206,E_4208] :
      ( k2_partfun1(k4_subset_1(A_4207,C_4206,'#skF_5'),'#skF_3',k1_tmap_1(A_4207,'#skF_3',C_4206,'#skF_5',E_4208,'#skF_7'),C_4206) = E_4208
      | ~ v1_funct_1(k1_tmap_1(A_4207,'#skF_3',C_4206,'#skF_5',E_4208,'#skF_7'))
      | k2_partfun1(C_4206,'#skF_3',E_4208,k9_subset_1(A_4207,C_4206,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_4207,C_4206,'#skF_5'))
      | ~ m1_subset_1(E_4208,k1_zfmisc_1(k2_zfmisc_1(C_4206,'#skF_3')))
      | ~ v1_funct_2(E_4208,C_4206,'#skF_3')
      | ~ v1_funct_1(E_4208)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4207))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_4206,k1_zfmisc_1(A_4207))
      | v1_xboole_0(C_4206)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_4207) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_47908,c_91560])).

tff(c_100543,plain,(
    ! [A_4553,C_4554,E_4555] :
      ( k2_partfun1(k4_subset_1(A_4553,C_4554,'#skF_5'),'#skF_3',k1_tmap_1(A_4553,'#skF_3',C_4554,'#skF_5',E_4555,'#skF_7'),C_4554) = E_4555
      | ~ v1_funct_1(k1_tmap_1(A_4553,'#skF_3',C_4554,'#skF_5',E_4555,'#skF_7'))
      | k2_partfun1(C_4554,'#skF_3',E_4555,k9_subset_1(A_4553,C_4554,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_4553,C_4554,'#skF_5'))
      | ~ m1_subset_1(E_4555,k1_zfmisc_1(k2_zfmisc_1(C_4554,'#skF_3')))
      | ~ v1_funct_2(E_4555,C_4554,'#skF_3')
      | ~ v1_funct_1(E_4555)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4553))
      | ~ m1_subset_1(C_4554,k1_zfmisc_1(A_4553))
      | v1_xboole_0(C_4554)
      | v1_xboole_0(A_4553) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_86,c_91568])).

tff(c_100556,plain,(
    ! [A_4553] :
      ( k2_partfun1(k4_subset_1(A_4553,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_4553,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_4553,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1(A_4553,'#skF_4','#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_4553,'#skF_4','#skF_5'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4553))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4553))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_4553) ) ),
    inference(resolution,[status(thm)],[c_76,c_100543])).

tff(c_100568,plain,(
    ! [A_4553] :
      ( k2_partfun1(k4_subset_1(A_4553,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_4553,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_4553,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_4553,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_4553,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4553))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4553))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_4553) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_47911,c_100556])).

tff(c_102368,plain,(
    ! [A_4582] :
      ( k2_partfun1(k4_subset_1(A_4582,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_4582,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_4582,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_4582,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_4582,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4582))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4582))
      | v1_xboole_0(A_4582) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_100568])).

tff(c_2515,plain,(
    ! [C_545,B_546,A_547] :
      ( ~ v1_xboole_0(C_545)
      | ~ m1_subset_1(B_546,k1_zfmisc_1(C_545))
      | ~ r2_hidden(A_547,B_546) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2549,plain,(
    ! [B_553,A_554,A_555] :
      ( ~ v1_xboole_0(B_553)
      | ~ r2_hidden(A_554,A_555)
      | ~ r1_tarski(A_555,B_553) ) ),
    inference(resolution,[status(thm)],[c_26,c_2515])).

tff(c_2595,plain,(
    ! [B_567,B_568,A_569] :
      ( ~ v1_xboole_0(B_567)
      | ~ r1_tarski(B_568,B_567)
      | r1_xboole_0(A_569,B_568) ) ),
    inference(resolution,[status(thm)],[c_10,c_2549])).

tff(c_2610,plain,(
    ! [B_9,A_569] :
      ( ~ v1_xboole_0(B_9)
      | r1_xboole_0(A_569,B_9) ) ),
    inference(resolution,[status(thm)],[c_18,c_2595])).

tff(c_2438,plain,(
    ! [C_524,A_525,B_526] :
      ( v1_relat_1(C_524)
      | ~ m1_subset_1(C_524,k1_zfmisc_1(k2_zfmisc_1(A_525,B_526))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2450,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_2438])).

tff(c_2501,plain,(
    ! [C_542,A_543,B_544] :
      ( v4_relat_1(C_542,A_543)
      | ~ m1_subset_1(C_542,k1_zfmisc_1(k2_zfmisc_1(A_543,B_544))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2513,plain,(
    v4_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_2501])).

tff(c_2653,plain,(
    ! [B_581,A_582] :
      ( k7_relat_1(B_581,A_582) = B_581
      | ~ v4_relat_1(B_581,A_582)
      | ~ v1_relat_1(B_581) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2662,plain,
    ( k7_relat_1('#skF_7','#skF_5') = '#skF_7'
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_2513,c_2653])).

tff(c_2671,plain,(
    k7_relat_1('#skF_7','#skF_5') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2450,c_2662])).

tff(c_3840,plain,(
    ! [C_690,A_691,B_692] :
      ( k7_relat_1(k7_relat_1(C_690,A_691),B_692) = k1_xboole_0
      | ~ r1_xboole_0(A_691,B_692)
      | ~ v1_relat_1(C_690) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_3875,plain,(
    ! [B_692] :
      ( k7_relat_1('#skF_7',B_692) = k1_xboole_0
      | ~ r1_xboole_0('#skF_5',B_692)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2671,c_3840])).

tff(c_3891,plain,(
    ! [B_693] :
      ( k7_relat_1('#skF_7',B_693) = k1_xboole_0
      | ~ r1_xboole_0('#skF_5',B_693) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2450,c_3875])).

tff(c_3914,plain,(
    ! [B_694] :
      ( k7_relat_1('#skF_7',B_694) = k1_xboole_0
      | ~ v1_xboole_0(B_694) ) ),
    inference(resolution,[status(thm)],[c_2610,c_3891])).

tff(c_3918,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_3914])).

tff(c_2689,plain,(
    ! [A_585,B_586] :
      ( r1_xboole_0(A_585,B_586)
      | ~ r1_subset_1(A_585,B_586)
      | v1_xboole_0(B_586)
      | v1_xboole_0(A_585) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_4632,plain,(
    ! [A_788,B_789] :
      ( k3_xboole_0(A_788,B_789) = k1_xboole_0
      | ~ r1_subset_1(A_788,B_789)
      | v1_xboole_0(B_789)
      | v1_xboole_0(A_788) ) ),
    inference(resolution,[status(thm)],[c_2689,c_2])).

tff(c_4638,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_4632])).

tff(c_4642,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_86,c_4638])).

tff(c_38,plain,(
    ! [A_28,B_29] :
      ( r1_xboole_0(A_28,B_29)
      | ~ r1_subset_1(A_28,B_29)
      | v1_xboole_0(B_29)
      | v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2451,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_2438])).

tff(c_2514,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_2501])).

tff(c_2659,plain,
    ( k7_relat_1('#skF_6','#skF_4') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2514,c_2653])).

tff(c_2668,plain,(
    k7_relat_1('#skF_6','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2451,c_2659])).

tff(c_3878,plain,(
    ! [B_692] :
      ( k7_relat_1('#skF_6',B_692) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_692)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2668,c_3840])).

tff(c_3972,plain,(
    ! [B_701] :
      ( k7_relat_1('#skF_6',B_701) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_701) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2451,c_3878])).

tff(c_3976,plain,(
    ! [B_29] :
      ( k7_relat_1('#skF_6',B_29) = k1_xboole_0
      | ~ r1_subset_1('#skF_4',B_29)
      | v1_xboole_0(B_29)
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_3972])).

tff(c_4224,plain,(
    ! [B_717] :
      ( k7_relat_1('#skF_6',B_717) = k1_xboole_0
      | ~ r1_subset_1('#skF_4',B_717)
      | v1_xboole_0(B_717) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_3976])).

tff(c_4227,plain,
    ( k7_relat_1('#skF_6','#skF_5') = k1_xboole_0
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_4224])).

tff(c_4230,plain,(
    k7_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_4227])).

tff(c_2745,plain,(
    ! [B_598,A_599] :
      ( k1_relat_1(B_598) = A_599
      | ~ v1_partfun1(B_598,A_599)
      | ~ v4_relat_1(B_598,A_599)
      | ~ v1_relat_1(B_598) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2751,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2514,c_2745])).

tff(c_2760,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2451,c_2751])).

tff(c_2764,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2760])).

tff(c_3421,plain,(
    ! [C_654,A_655,B_656] :
      ( v1_partfun1(C_654,A_655)
      | ~ v1_funct_2(C_654,A_655,B_656)
      | ~ v1_funct_1(C_654)
      | ~ m1_subset_1(C_654,k1_zfmisc_1(k2_zfmisc_1(A_655,B_656)))
      | v1_xboole_0(B_656) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_3431,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_3421])).

tff(c_3439,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_3431])).

tff(c_3441,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_2764,c_3439])).

tff(c_3442,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2760])).

tff(c_30,plain,(
    ! [B_22,A_21] :
      ( k7_relat_1(B_22,k3_xboole_0(k1_relat_1(B_22),A_21)) = k7_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3447,plain,(
    ! [A_21] :
      ( k7_relat_1('#skF_6',k3_xboole_0('#skF_4',A_21)) = k7_relat_1('#skF_6',A_21)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3442,c_30])).

tff(c_3454,plain,(
    ! [A_21] : k7_relat_1('#skF_6',k3_xboole_0('#skF_4',A_21)) = k7_relat_1('#skF_6',A_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2451,c_3447])).

tff(c_3919,plain,(
    ! [A_695,B_696,C_697] :
      ( k9_subset_1(A_695,B_696,C_697) = k3_xboole_0(B_696,C_697)
      | ~ m1_subset_1(C_697,k1_zfmisc_1(A_695)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_3934,plain,(
    ! [B_696] : k9_subset_1('#skF_2',B_696,'#skF_5') = k3_xboole_0(B_696,'#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_3919])).

tff(c_4282,plain,(
    ! [B_725,A_723,F_727,C_722,D_726,E_724] :
      ( v1_funct_1(k1_tmap_1(A_723,B_725,C_722,D_726,E_724,F_727))
      | ~ m1_subset_1(F_727,k1_zfmisc_1(k2_zfmisc_1(D_726,B_725)))
      | ~ v1_funct_2(F_727,D_726,B_725)
      | ~ v1_funct_1(F_727)
      | ~ m1_subset_1(E_724,k1_zfmisc_1(k2_zfmisc_1(C_722,B_725)))
      | ~ v1_funct_2(E_724,C_722,B_725)
      | ~ v1_funct_1(E_724)
      | ~ m1_subset_1(D_726,k1_zfmisc_1(A_723))
      | v1_xboole_0(D_726)
      | ~ m1_subset_1(C_722,k1_zfmisc_1(A_723))
      | v1_xboole_0(C_722)
      | v1_xboole_0(B_725)
      | v1_xboole_0(A_723) ) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_4287,plain,(
    ! [A_723,C_722,E_724] :
      ( v1_funct_1(k1_tmap_1(A_723,'#skF_3',C_722,'#skF_5',E_724,'#skF_7'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_724,k1_zfmisc_1(k2_zfmisc_1(C_722,'#skF_3')))
      | ~ v1_funct_2(E_724,C_722,'#skF_3')
      | ~ v1_funct_1(E_724)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_723))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_722,k1_zfmisc_1(A_723))
      | v1_xboole_0(C_722)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_723) ) ),
    inference(resolution,[status(thm)],[c_70,c_4282])).

tff(c_4293,plain,(
    ! [A_723,C_722,E_724] :
      ( v1_funct_1(k1_tmap_1(A_723,'#skF_3',C_722,'#skF_5',E_724,'#skF_7'))
      | ~ m1_subset_1(E_724,k1_zfmisc_1(k2_zfmisc_1(C_722,'#skF_3')))
      | ~ v1_funct_2(E_724,C_722,'#skF_3')
      | ~ v1_funct_1(E_724)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_723))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_722,k1_zfmisc_1(A_723))
      | v1_xboole_0(C_722)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_723) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_4287])).

tff(c_4580,plain,(
    ! [A_777,C_778,E_779] :
      ( v1_funct_1(k1_tmap_1(A_777,'#skF_3',C_778,'#skF_5',E_779,'#skF_7'))
      | ~ m1_subset_1(E_779,k1_zfmisc_1(k2_zfmisc_1(C_778,'#skF_3')))
      | ~ v1_funct_2(E_779,C_778,'#skF_3')
      | ~ v1_funct_1(E_779)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_777))
      | ~ m1_subset_1(C_778,k1_zfmisc_1(A_777))
      | v1_xboole_0(C_778)
      | v1_xboole_0(A_777) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_86,c_4293])).

tff(c_4593,plain,(
    ! [A_777] :
      ( v1_funct_1(k1_tmap_1(A_777,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_777))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_777))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_777) ) ),
    inference(resolution,[status(thm)],[c_76,c_4580])).

tff(c_4605,plain,(
    ! [A_777] :
      ( v1_funct_1(k1_tmap_1(A_777,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_777))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_777))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_777) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_4593])).

tff(c_4852,plain,(
    ! [A_809] :
      ( v1_funct_1(k1_tmap_1(A_809,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_809))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_809))
      | v1_xboole_0(A_809) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_4605])).

tff(c_4859,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_4852])).

tff(c_4863,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_4859])).

tff(c_4864,plain,(
    v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_4863])).

tff(c_4057,plain,(
    ! [A_705,B_706,C_707,D_708] :
      ( k2_partfun1(A_705,B_706,C_707,D_708) = k7_relat_1(C_707,D_708)
      | ~ m1_subset_1(C_707,k1_zfmisc_1(k2_zfmisc_1(A_705,B_706)))
      | ~ v1_funct_1(C_707) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_4064,plain,(
    ! [D_708] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_6',D_708) = k7_relat_1('#skF_6',D_708)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_76,c_4057])).

tff(c_4071,plain,(
    ! [D_708] : k2_partfun1('#skF_4','#skF_3','#skF_6',D_708) = k7_relat_1('#skF_6',D_708) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4064])).

tff(c_4062,plain,(
    ! [D_708] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_7',D_708) = k7_relat_1('#skF_7',D_708)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_70,c_4057])).

tff(c_4068,plain,(
    ! [D_708] : k2_partfun1('#skF_5','#skF_3','#skF_7',D_708) = k7_relat_1('#skF_7',D_708) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_4062])).

tff(c_4558,plain,(
    ! [F_769,D_772,E_770,C_773,B_771,A_774] :
      ( k2_partfun1(k4_subset_1(A_774,C_773,D_772),B_771,k1_tmap_1(A_774,B_771,C_773,D_772,E_770,F_769),D_772) = F_769
      | ~ m1_subset_1(k1_tmap_1(A_774,B_771,C_773,D_772,E_770,F_769),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_774,C_773,D_772),B_771)))
      | ~ v1_funct_2(k1_tmap_1(A_774,B_771,C_773,D_772,E_770,F_769),k4_subset_1(A_774,C_773,D_772),B_771)
      | ~ v1_funct_1(k1_tmap_1(A_774,B_771,C_773,D_772,E_770,F_769))
      | k2_partfun1(D_772,B_771,F_769,k9_subset_1(A_774,C_773,D_772)) != k2_partfun1(C_773,B_771,E_770,k9_subset_1(A_774,C_773,D_772))
      | ~ m1_subset_1(F_769,k1_zfmisc_1(k2_zfmisc_1(D_772,B_771)))
      | ~ v1_funct_2(F_769,D_772,B_771)
      | ~ v1_funct_1(F_769)
      | ~ m1_subset_1(E_770,k1_zfmisc_1(k2_zfmisc_1(C_773,B_771)))
      | ~ v1_funct_2(E_770,C_773,B_771)
      | ~ v1_funct_1(E_770)
      | ~ m1_subset_1(D_772,k1_zfmisc_1(A_774))
      | v1_xboole_0(D_772)
      | ~ m1_subset_1(C_773,k1_zfmisc_1(A_774))
      | v1_xboole_0(C_773)
      | v1_xboole_0(B_771)
      | v1_xboole_0(A_774) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_10817,plain,(
    ! [D_1176,E_1174,F_1177,A_1173,C_1172,B_1175] :
      ( k2_partfun1(k4_subset_1(A_1173,C_1172,D_1176),B_1175,k1_tmap_1(A_1173,B_1175,C_1172,D_1176,E_1174,F_1177),D_1176) = F_1177
      | ~ v1_funct_2(k1_tmap_1(A_1173,B_1175,C_1172,D_1176,E_1174,F_1177),k4_subset_1(A_1173,C_1172,D_1176),B_1175)
      | ~ v1_funct_1(k1_tmap_1(A_1173,B_1175,C_1172,D_1176,E_1174,F_1177))
      | k2_partfun1(D_1176,B_1175,F_1177,k9_subset_1(A_1173,C_1172,D_1176)) != k2_partfun1(C_1172,B_1175,E_1174,k9_subset_1(A_1173,C_1172,D_1176))
      | ~ m1_subset_1(F_1177,k1_zfmisc_1(k2_zfmisc_1(D_1176,B_1175)))
      | ~ v1_funct_2(F_1177,D_1176,B_1175)
      | ~ v1_funct_1(F_1177)
      | ~ m1_subset_1(E_1174,k1_zfmisc_1(k2_zfmisc_1(C_1172,B_1175)))
      | ~ v1_funct_2(E_1174,C_1172,B_1175)
      | ~ v1_funct_1(E_1174)
      | ~ m1_subset_1(D_1176,k1_zfmisc_1(A_1173))
      | v1_xboole_0(D_1176)
      | ~ m1_subset_1(C_1172,k1_zfmisc_1(A_1173))
      | v1_xboole_0(C_1172)
      | v1_xboole_0(B_1175)
      | v1_xboole_0(A_1173) ) ),
    inference(resolution,[status(thm)],[c_62,c_4558])).

tff(c_20510,plain,(
    ! [D_1563,E_1561,C_1559,F_1564,B_1562,A_1560] :
      ( k2_partfun1(k4_subset_1(A_1560,C_1559,D_1563),B_1562,k1_tmap_1(A_1560,B_1562,C_1559,D_1563,E_1561,F_1564),D_1563) = F_1564
      | ~ v1_funct_1(k1_tmap_1(A_1560,B_1562,C_1559,D_1563,E_1561,F_1564))
      | k2_partfun1(D_1563,B_1562,F_1564,k9_subset_1(A_1560,C_1559,D_1563)) != k2_partfun1(C_1559,B_1562,E_1561,k9_subset_1(A_1560,C_1559,D_1563))
      | ~ m1_subset_1(F_1564,k1_zfmisc_1(k2_zfmisc_1(D_1563,B_1562)))
      | ~ v1_funct_2(F_1564,D_1563,B_1562)
      | ~ v1_funct_1(F_1564)
      | ~ m1_subset_1(E_1561,k1_zfmisc_1(k2_zfmisc_1(C_1559,B_1562)))
      | ~ v1_funct_2(E_1561,C_1559,B_1562)
      | ~ v1_funct_1(E_1561)
      | ~ m1_subset_1(D_1563,k1_zfmisc_1(A_1560))
      | v1_xboole_0(D_1563)
      | ~ m1_subset_1(C_1559,k1_zfmisc_1(A_1560))
      | v1_xboole_0(C_1559)
      | v1_xboole_0(B_1562)
      | v1_xboole_0(A_1560) ) ),
    inference(resolution,[status(thm)],[c_64,c_10817])).

tff(c_20519,plain,(
    ! [A_1560,C_1559,E_1561] :
      ( k2_partfun1(k4_subset_1(A_1560,C_1559,'#skF_5'),'#skF_3',k1_tmap_1(A_1560,'#skF_3',C_1559,'#skF_5',E_1561,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1560,'#skF_3',C_1559,'#skF_5',E_1561,'#skF_7'))
      | k2_partfun1(C_1559,'#skF_3',E_1561,k9_subset_1(A_1560,C_1559,'#skF_5')) != k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1(A_1560,C_1559,'#skF_5'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_1561,k1_zfmisc_1(k2_zfmisc_1(C_1559,'#skF_3')))
      | ~ v1_funct_2(E_1561,C_1559,'#skF_3')
      | ~ v1_funct_1(E_1561)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1560))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1559,k1_zfmisc_1(A_1560))
      | v1_xboole_0(C_1559)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1560) ) ),
    inference(resolution,[status(thm)],[c_70,c_20510])).

tff(c_20527,plain,(
    ! [A_1560,C_1559,E_1561] :
      ( k2_partfun1(k4_subset_1(A_1560,C_1559,'#skF_5'),'#skF_3',k1_tmap_1(A_1560,'#skF_3',C_1559,'#skF_5',E_1561,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1560,'#skF_3',C_1559,'#skF_5',E_1561,'#skF_7'))
      | k2_partfun1(C_1559,'#skF_3',E_1561,k9_subset_1(A_1560,C_1559,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_1560,C_1559,'#skF_5'))
      | ~ m1_subset_1(E_1561,k1_zfmisc_1(k2_zfmisc_1(C_1559,'#skF_3')))
      | ~ v1_funct_2(E_1561,C_1559,'#skF_3')
      | ~ v1_funct_1(E_1561)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1560))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1559,k1_zfmisc_1(A_1560))
      | v1_xboole_0(C_1559)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1560) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_4068,c_20519])).

tff(c_44928,plain,(
    ! [A_2076,C_2077,E_2078] :
      ( k2_partfun1(k4_subset_1(A_2076,C_2077,'#skF_5'),'#skF_3',k1_tmap_1(A_2076,'#skF_3',C_2077,'#skF_5',E_2078,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_2076,'#skF_3',C_2077,'#skF_5',E_2078,'#skF_7'))
      | k2_partfun1(C_2077,'#skF_3',E_2078,k9_subset_1(A_2076,C_2077,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_2076,C_2077,'#skF_5'))
      | ~ m1_subset_1(E_2078,k1_zfmisc_1(k2_zfmisc_1(C_2077,'#skF_3')))
      | ~ v1_funct_2(E_2078,C_2077,'#skF_3')
      | ~ v1_funct_1(E_2078)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2076))
      | ~ m1_subset_1(C_2077,k1_zfmisc_1(A_2076))
      | v1_xboole_0(C_2077)
      | v1_xboole_0(A_2076) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_86,c_20527])).

tff(c_44947,plain,(
    ! [A_2076] :
      ( k2_partfun1(k4_subset_1(A_2076,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_2076,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_2076,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1(A_2076,'#skF_4','#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_2076,'#skF_4','#skF_5'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2076))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2076))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_2076) ) ),
    inference(resolution,[status(thm)],[c_76,c_44928])).

tff(c_44961,plain,(
    ! [A_2076] :
      ( k2_partfun1(k4_subset_1(A_2076,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_2076,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_2076,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_2076,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_2076,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2076))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2076))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_2076) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_4071,c_44947])).

tff(c_45918,plain,(
    ! [A_2083] :
      ( k2_partfun1(k4_subset_1(A_2083,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_2083,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_2083,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_2083,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_2083,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2083))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2083))
      | v1_xboole_0(A_2083) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_44961])).

tff(c_261,plain,(
    ! [C_273,B_274,A_275] :
      ( ~ v1_xboole_0(C_273)
      | ~ m1_subset_1(B_274,k1_zfmisc_1(C_273))
      | ~ r2_hidden(A_275,B_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_277,plain,(
    ! [B_276,A_277,A_278] :
      ( ~ v1_xboole_0(B_276)
      | ~ r2_hidden(A_277,A_278)
      | ~ r1_tarski(A_278,B_276) ) ),
    inference(resolution,[status(thm)],[c_26,c_261])).

tff(c_381,plain,(
    ! [B_298,B_299,A_300] :
      ( ~ v1_xboole_0(B_298)
      | ~ r1_tarski(B_299,B_298)
      | r1_xboole_0(A_300,B_299) ) ),
    inference(resolution,[status(thm)],[c_10,c_277])).

tff(c_396,plain,(
    ! [B_9,A_300] :
      ( ~ v1_xboole_0(B_9)
      | r1_xboole_0(A_300,B_9) ) ),
    inference(resolution,[status(thm)],[c_18,c_381])).

tff(c_127,plain,(
    ! [C_247,A_248,B_249] :
      ( v1_relat_1(C_247)
      | ~ m1_subset_1(C_247,k1_zfmisc_1(k2_zfmisc_1(A_248,B_249))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_139,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_127])).

tff(c_305,plain,(
    ! [C_284,A_285,B_286] :
      ( v4_relat_1(C_284,A_285)
      | ~ m1_subset_1(C_284,k1_zfmisc_1(k2_zfmisc_1(A_285,B_286))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_317,plain,(
    v4_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_305])).

tff(c_321,plain,
    ( k7_relat_1('#skF_7','#skF_5') = '#skF_7'
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_317,c_34])).

tff(c_324,plain,(
    k7_relat_1('#skF_7','#skF_5') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_321])).

tff(c_1427,plain,(
    ! [C_409,A_410,B_411] :
      ( k7_relat_1(k7_relat_1(C_409,A_410),B_411) = k1_xboole_0
      | ~ r1_xboole_0(A_410,B_411)
      | ~ v1_relat_1(C_409) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1465,plain,(
    ! [B_411] :
      ( k7_relat_1('#skF_7',B_411) = k1_xboole_0
      | ~ r1_xboole_0('#skF_5',B_411)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_1427])).

tff(c_1530,plain,(
    ! [B_418] :
      ( k7_relat_1('#skF_7',B_418) = k1_xboole_0
      | ~ r1_xboole_0('#skF_5',B_418) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_1465])).

tff(c_1553,plain,(
    ! [B_419] :
      ( k7_relat_1('#skF_7',B_419) = k1_xboole_0
      | ~ v1_xboole_0(B_419) ) ),
    inference(resolution,[status(thm)],[c_396,c_1530])).

tff(c_1557,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_1553])).

tff(c_405,plain,(
    ! [A_303,B_304] :
      ( r1_xboole_0(A_303,B_304)
      | ~ r1_subset_1(A_303,B_304)
      | v1_xboole_0(B_304)
      | v1_xboole_0(A_303) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2139,plain,(
    ! [A_495,B_496] :
      ( k3_xboole_0(A_495,B_496) = k1_xboole_0
      | ~ r1_subset_1(A_495,B_496)
      | v1_xboole_0(B_496)
      | v1_xboole_0(A_495) ) ),
    inference(resolution,[status(thm)],[c_405,c_2])).

tff(c_2145,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_2139])).

tff(c_2149,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_86,c_2145])).

tff(c_140,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_127])).

tff(c_318,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_305])).

tff(c_327,plain,
    ( k7_relat_1('#skF_6','#skF_4') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_318,c_34])).

tff(c_330,plain,(
    k7_relat_1('#skF_6','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_327])).

tff(c_1462,plain,(
    ! [B_411] :
      ( k7_relat_1('#skF_6',B_411) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_411)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_1427])).

tff(c_1478,plain,(
    ! [B_412] :
      ( k7_relat_1('#skF_6',B_412) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_412) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_1462])).

tff(c_1482,plain,(
    ! [B_29] :
      ( k7_relat_1('#skF_6',B_29) = k1_xboole_0
      | ~ r1_subset_1('#skF_4',B_29)
      | v1_xboole_0(B_29)
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_1478])).

tff(c_1558,plain,(
    ! [B_420] :
      ( k7_relat_1('#skF_6',B_420) = k1_xboole_0
      | ~ r1_subset_1('#skF_4',B_420)
      | v1_xboole_0(B_420) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_1482])).

tff(c_1561,plain,
    ( k7_relat_1('#skF_6','#skF_5') = k1_xboole_0
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_1558])).

tff(c_1564,plain,(
    k7_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1561])).

tff(c_585,plain,(
    ! [B_339,A_340] :
      ( k1_relat_1(B_339) = A_340
      | ~ v1_partfun1(B_339,A_340)
      | ~ v4_relat_1(B_339,A_340)
      | ~ v1_relat_1(B_339) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_591,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_318,c_585])).

tff(c_600,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_591])).

tff(c_604,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_600])).

tff(c_1111,plain,(
    ! [C_382,A_383,B_384] :
      ( v1_partfun1(C_382,A_383)
      | ~ v1_funct_2(C_382,A_383,B_384)
      | ~ v1_funct_1(C_382)
      | ~ m1_subset_1(C_382,k1_zfmisc_1(k2_zfmisc_1(A_383,B_384)))
      | v1_xboole_0(B_384) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1121,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_1111])).

tff(c_1129,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_1121])).

tff(c_1131,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_604,c_1129])).

tff(c_1132,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_600])).

tff(c_1137,plain,(
    ! [A_21] :
      ( k7_relat_1('#skF_6',k3_xboole_0('#skF_4',A_21)) = k7_relat_1('#skF_6',A_21)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1132,c_30])).

tff(c_1144,plain,(
    ! [A_21] : k7_relat_1('#skF_6',k3_xboole_0('#skF_4',A_21)) = k7_relat_1('#skF_6',A_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_1137])).

tff(c_1506,plain,(
    ! [A_414,B_415,C_416,D_417] :
      ( k2_partfun1(A_414,B_415,C_416,D_417) = k7_relat_1(C_416,D_417)
      | ~ m1_subset_1(C_416,k1_zfmisc_1(k2_zfmisc_1(A_414,B_415)))
      | ~ v1_funct_1(C_416) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1513,plain,(
    ! [D_417] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_6',D_417) = k7_relat_1('#skF_6',D_417)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_76,c_1506])).

tff(c_1520,plain,(
    ! [D_417] : k2_partfun1('#skF_4','#skF_3','#skF_6',D_417) = k7_relat_1('#skF_6',D_417) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1513])).

tff(c_1511,plain,(
    ! [D_417] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_7',D_417) = k7_relat_1('#skF_7',D_417)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_70,c_1506])).

tff(c_1517,plain,(
    ! [D_417] : k2_partfun1('#skF_5','#skF_3','#skF_7',D_417) = k7_relat_1('#skF_7',D_417) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1511])).

tff(c_489,plain,(
    ! [A_325,B_326,C_327] :
      ( k9_subset_1(A_325,B_326,C_327) = k3_xboole_0(B_326,C_327)
      | ~ m1_subset_1(C_327,k1_zfmisc_1(A_325)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_504,plain,(
    ! [B_326] : k9_subset_1('#skF_2',B_326,'#skF_5') = k3_xboole_0(B_326,'#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_489])).

tff(c_68,plain,
    ( k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') != '#skF_7'
    | k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') != '#skF_6'
    | k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_125,plain,(
    k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_514,plain,(
    k2_partfun1('#skF_5','#skF_3','#skF_7',k3_xboole_0('#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3','#skF_6',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_504,c_125])).

tff(c_1656,plain,(
    k2_partfun1('#skF_4','#skF_3','#skF_6',k3_xboole_0('#skF_4','#skF_5')) != k7_relat_1('#skF_7',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1517,c_514])).

tff(c_2360,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1557,c_2149,c_1564,c_1144,c_1520,c_1656])).

tff(c_2361,plain,
    ( k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_2414,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_2361])).

tff(c_45935,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_45918,c_2414])).

tff(c_45957,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_84,c_3918,c_4642,c_4230,c_3454,c_3934,c_3934,c_4864,c_45935])).

tff(c_45959,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_45957])).

tff(c_45960,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2361])).

tff(c_102388,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_102368,c_45960])).

tff(c_102413,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_84,c_47896,c_48518,c_47751,c_47948,c_48518,c_47751,c_48469,c_102388])).

tff(c_102415,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_102413])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:40:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 30.94/20.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 30.94/20.59  
% 30.94/20.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 30.94/20.59  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 30.94/20.59  
% 30.94/20.59  %Foreground sorts:
% 30.94/20.59  
% 30.94/20.59  
% 30.94/20.59  %Background operators:
% 30.94/20.59  
% 30.94/20.59  
% 30.94/20.59  %Foreground operators:
% 30.94/20.59  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 30.94/20.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 30.94/20.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 30.94/20.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 30.94/20.59  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 30.94/20.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 30.94/20.59  tff('#skF_7', type, '#skF_7': $i).
% 30.94/20.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 30.94/20.59  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 30.94/20.59  tff('#skF_5', type, '#skF_5': $i).
% 30.94/20.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 30.94/20.59  tff('#skF_6', type, '#skF_6': $i).
% 30.94/20.59  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 30.94/20.59  tff('#skF_2', type, '#skF_2': $i).
% 30.94/20.59  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 30.94/20.59  tff('#skF_3', type, '#skF_3': $i).
% 30.94/20.59  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 30.94/20.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 30.94/20.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 30.94/20.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 30.94/20.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 30.94/20.59  tff('#skF_4', type, '#skF_4': $i).
% 30.94/20.59  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 30.94/20.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 30.94/20.59  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 30.94/20.59  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 30.94/20.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 30.94/20.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 30.94/20.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 30.94/20.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 30.94/20.59  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 30.94/20.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 30.94/20.59  
% 31.20/20.62  tff(f_264, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 31.20/20.62  tff(f_30, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 31.20/20.62  tff(f_54, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 31.20/20.62  tff(f_48, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 31.20/20.62  tff(f_69, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 31.20/20.62  tff(f_76, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 31.20/20.62  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 31.20/20.62  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 31.20/20.62  tff(f_92, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 31.20/20.62  tff(f_86, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 31.20/20.62  tff(f_102, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 31.20/20.62  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 31.20/20.62  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 31.20/20.62  tff(f_222, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 31.20/20.62  tff(f_140, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 31.20/20.62  tff(f_188, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 31.20/20.62  tff(f_134, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 31.20/20.62  tff(f_126, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 31.20/20.62  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_relat_1)).
% 31.20/20.62  tff(c_94, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_264])).
% 31.20/20.62  tff(c_88, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_264])).
% 31.20/20.62  tff(c_84, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_264])).
% 31.20/20.62  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 31.20/20.62  tff(c_18, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 31.20/20.62  tff(c_10, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_48])).
% 31.20/20.62  tff(c_26, plain, (![A_16, B_17]: (m1_subset_1(A_16, k1_zfmisc_1(B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_69])).
% 31.20/20.62  tff(c_46019, plain, (![C_2098, B_2099, A_2100]: (~v1_xboole_0(C_2098) | ~m1_subset_1(B_2099, k1_zfmisc_1(C_2098)) | ~r2_hidden(A_2100, B_2099))), inference(cnfTransformation, [status(thm)], [f_76])).
% 31.20/20.62  tff(c_46035, plain, (![B_2101, A_2102, A_2103]: (~v1_xboole_0(B_2101) | ~r2_hidden(A_2102, A_2103) | ~r1_tarski(A_2103, B_2101))), inference(resolution, [status(thm)], [c_26, c_46019])).
% 31.20/20.62  tff(c_46106, plain, (![B_2120, B_2121, A_2122]: (~v1_xboole_0(B_2120) | ~r1_tarski(B_2121, B_2120) | r1_xboole_0(A_2122, B_2121))), inference(resolution, [status(thm)], [c_10, c_46035])).
% 31.20/20.62  tff(c_46121, plain, (![B_9, A_2122]: (~v1_xboole_0(B_9) | r1_xboole_0(A_2122, B_9))), inference(resolution, [status(thm)], [c_18, c_46106])).
% 31.20/20.62  tff(c_76, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_264])).
% 31.20/20.62  tff(c_45985, plain, (![C_2086, A_2087, B_2088]: (v1_relat_1(C_2086) | ~m1_subset_1(C_2086, k1_zfmisc_1(k2_zfmisc_1(A_2087, B_2088))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 31.20/20.62  tff(c_45998, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_45985])).
% 31.20/20.62  tff(c_46122, plain, (![C_2123, A_2124, B_2125]: (v4_relat_1(C_2123, A_2124) | ~m1_subset_1(C_2123, k1_zfmisc_1(k2_zfmisc_1(A_2124, B_2125))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 31.20/20.62  tff(c_46135, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_76, c_46122])).
% 31.20/20.62  tff(c_34, plain, (![B_27, A_26]: (k7_relat_1(B_27, A_26)=B_27 | ~v4_relat_1(B_27, A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_92])).
% 31.20/20.62  tff(c_46144, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_46135, c_34])).
% 31.20/20.62  tff(c_46147, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_45998, c_46144])).
% 31.20/20.62  tff(c_47818, plain, (![C_2287, A_2288, B_2289]: (k7_relat_1(k7_relat_1(C_2287, A_2288), B_2289)=k1_xboole_0 | ~r1_xboole_0(A_2288, B_2289) | ~v1_relat_1(C_2287))), inference(cnfTransformation, [status(thm)], [f_86])).
% 31.20/20.62  tff(c_47853, plain, (![B_2289]: (k7_relat_1('#skF_6', B_2289)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_2289) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_46147, c_47818])).
% 31.20/20.62  tff(c_47869, plain, (![B_2290]: (k7_relat_1('#skF_6', B_2290)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_2290))), inference(demodulation, [status(thm), theory('equality')], [c_45998, c_47853])).
% 31.20/20.62  tff(c_47892, plain, (![B_2291]: (k7_relat_1('#skF_6', B_2291)=k1_xboole_0 | ~v1_xboole_0(B_2291))), inference(resolution, [status(thm)], [c_46121, c_47869])).
% 31.20/20.62  tff(c_47896, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_47892])).
% 31.20/20.62  tff(c_90, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_264])).
% 31.20/20.62  tff(c_86, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_264])).
% 31.20/20.62  tff(c_82, plain, (r1_subset_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_264])).
% 31.20/20.62  tff(c_46240, plain, (![A_2147, B_2148]: (r1_xboole_0(A_2147, B_2148) | ~r1_subset_1(A_2147, B_2148) | v1_xboole_0(B_2148) | v1_xboole_0(A_2147))), inference(cnfTransformation, [status(thm)], [f_102])).
% 31.20/20.62  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 31.20/20.62  tff(c_48512, plain, (![A_2371, B_2372]: (k3_xboole_0(A_2371, B_2372)=k1_xboole_0 | ~r1_subset_1(A_2371, B_2372) | v1_xboole_0(B_2372) | v1_xboole_0(A_2371))), inference(resolution, [status(thm)], [c_46240, c_2])).
% 31.20/20.62  tff(c_48515, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0 | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_82, c_48512])).
% 31.20/20.62  tff(c_48518, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_90, c_86, c_48515])).
% 31.20/20.62  tff(c_47736, plain, (![A_2275, B_2276, C_2277]: (k9_subset_1(A_2275, B_2276, C_2277)=k3_xboole_0(B_2276, C_2277) | ~m1_subset_1(C_2277, k1_zfmisc_1(A_2275)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 31.20/20.62  tff(c_47751, plain, (![B_2276]: (k9_subset_1('#skF_2', B_2276, '#skF_5')=k3_xboole_0(B_2276, '#skF_5'))), inference(resolution, [status(thm)], [c_84, c_47736])).
% 31.20/20.62  tff(c_70, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_264])).
% 31.20/20.62  tff(c_45997, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_70, c_45985])).
% 31.20/20.62  tff(c_46134, plain, (v4_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_70, c_46122])).
% 31.20/20.62  tff(c_46138, plain, (k7_relat_1('#skF_7', '#skF_5')='#skF_7' | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_46134, c_34])).
% 31.20/20.62  tff(c_46141, plain, (k7_relat_1('#skF_7', '#skF_5')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_45997, c_46138])).
% 31.20/20.62  tff(c_47856, plain, (![B_2289]: (k7_relat_1('#skF_7', B_2289)=k1_xboole_0 | ~r1_xboole_0('#skF_5', B_2289) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_46141, c_47818])).
% 31.20/20.62  tff(c_47921, plain, (![B_2296]: (k7_relat_1('#skF_7', B_2296)=k1_xboole_0 | ~r1_xboole_0('#skF_5', B_2296))), inference(demodulation, [status(thm), theory('equality')], [c_45997, c_47856])).
% 31.20/20.62  tff(c_47944, plain, (![B_2297]: (k7_relat_1('#skF_7', B_2297)=k1_xboole_0 | ~v1_xboole_0(B_2297))), inference(resolution, [status(thm)], [c_46121, c_47921])).
% 31.20/20.62  tff(c_47948, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_47944])).
% 31.20/20.62  tff(c_80, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_264])).
% 31.20/20.62  tff(c_78, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_264])).
% 31.20/20.62  tff(c_92, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_264])).
% 31.20/20.62  tff(c_74, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_264])).
% 31.20/20.62  tff(c_72, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_264])).
% 31.20/20.62  tff(c_48116, plain, (![C_2308, B_2311, F_2313, A_2309, D_2312, E_2310]: (v1_funct_1(k1_tmap_1(A_2309, B_2311, C_2308, D_2312, E_2310, F_2313)) | ~m1_subset_1(F_2313, k1_zfmisc_1(k2_zfmisc_1(D_2312, B_2311))) | ~v1_funct_2(F_2313, D_2312, B_2311) | ~v1_funct_1(F_2313) | ~m1_subset_1(E_2310, k1_zfmisc_1(k2_zfmisc_1(C_2308, B_2311))) | ~v1_funct_2(E_2310, C_2308, B_2311) | ~v1_funct_1(E_2310) | ~m1_subset_1(D_2312, k1_zfmisc_1(A_2309)) | v1_xboole_0(D_2312) | ~m1_subset_1(C_2308, k1_zfmisc_1(A_2309)) | v1_xboole_0(C_2308) | v1_xboole_0(B_2311) | v1_xboole_0(A_2309))), inference(cnfTransformation, [status(thm)], [f_222])).
% 31.20/20.62  tff(c_48121, plain, (![A_2309, C_2308, E_2310]: (v1_funct_1(k1_tmap_1(A_2309, '#skF_3', C_2308, '#skF_5', E_2310, '#skF_7')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_2310, k1_zfmisc_1(k2_zfmisc_1(C_2308, '#skF_3'))) | ~v1_funct_2(E_2310, C_2308, '#skF_3') | ~v1_funct_1(E_2310) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2309)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_2308, k1_zfmisc_1(A_2309)) | v1_xboole_0(C_2308) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2309))), inference(resolution, [status(thm)], [c_70, c_48116])).
% 31.20/20.62  tff(c_48127, plain, (![A_2309, C_2308, E_2310]: (v1_funct_1(k1_tmap_1(A_2309, '#skF_3', C_2308, '#skF_5', E_2310, '#skF_7')) | ~m1_subset_1(E_2310, k1_zfmisc_1(k2_zfmisc_1(C_2308, '#skF_3'))) | ~v1_funct_2(E_2310, C_2308, '#skF_3') | ~v1_funct_1(E_2310) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2309)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_2308, k1_zfmisc_1(A_2309)) | v1_xboole_0(C_2308) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2309))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_48121])).
% 31.20/20.62  tff(c_48192, plain, (![A_2315, C_2316, E_2317]: (v1_funct_1(k1_tmap_1(A_2315, '#skF_3', C_2316, '#skF_5', E_2317, '#skF_7')) | ~m1_subset_1(E_2317, k1_zfmisc_1(k2_zfmisc_1(C_2316, '#skF_3'))) | ~v1_funct_2(E_2317, C_2316, '#skF_3') | ~v1_funct_1(E_2317) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2315)) | ~m1_subset_1(C_2316, k1_zfmisc_1(A_2315)) | v1_xboole_0(C_2316) | v1_xboole_0(A_2315))), inference(negUnitSimplification, [status(thm)], [c_92, c_86, c_48127])).
% 31.20/20.62  tff(c_48199, plain, (![A_2315]: (v1_funct_1(k1_tmap_1(A_2315, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2315)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2315)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_2315))), inference(resolution, [status(thm)], [c_76, c_48192])).
% 31.20/20.62  tff(c_48207, plain, (![A_2315]: (v1_funct_1(k1_tmap_1(A_2315, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2315)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2315)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_2315))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_48199])).
% 31.20/20.62  tff(c_48457, plain, (![A_2360]: (v1_funct_1(k1_tmap_1(A_2360, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2360)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2360)) | v1_xboole_0(A_2360))), inference(negUnitSimplification, [status(thm)], [c_90, c_48207])).
% 31.20/20.62  tff(c_48464, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_84, c_48457])).
% 31.20/20.62  tff(c_48468, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_48464])).
% 31.20/20.62  tff(c_48469, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_94, c_48468])).
% 31.20/20.62  tff(c_47897, plain, (![A_2292, B_2293, C_2294, D_2295]: (k2_partfun1(A_2292, B_2293, C_2294, D_2295)=k7_relat_1(C_2294, D_2295) | ~m1_subset_1(C_2294, k1_zfmisc_1(k2_zfmisc_1(A_2292, B_2293))) | ~v1_funct_1(C_2294))), inference(cnfTransformation, [status(thm)], [f_140])).
% 31.20/20.62  tff(c_47904, plain, (![D_2295]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_2295)=k7_relat_1('#skF_6', D_2295) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_76, c_47897])).
% 31.20/20.62  tff(c_47911, plain, (![D_2295]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_2295)=k7_relat_1('#skF_6', D_2295))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_47904])).
% 31.20/20.62  tff(c_47902, plain, (![D_2295]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_2295)=k7_relat_1('#skF_7', D_2295) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_70, c_47897])).
% 31.20/20.62  tff(c_47908, plain, (![D_2295]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_2295)=k7_relat_1('#skF_7', D_2295))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_47902])).
% 31.20/20.62  tff(c_64, plain, (![E_177, F_178, B_174, D_176, C_175, A_173]: (v1_funct_2(k1_tmap_1(A_173, B_174, C_175, D_176, E_177, F_178), k4_subset_1(A_173, C_175, D_176), B_174) | ~m1_subset_1(F_178, k1_zfmisc_1(k2_zfmisc_1(D_176, B_174))) | ~v1_funct_2(F_178, D_176, B_174) | ~v1_funct_1(F_178) | ~m1_subset_1(E_177, k1_zfmisc_1(k2_zfmisc_1(C_175, B_174))) | ~v1_funct_2(E_177, C_175, B_174) | ~v1_funct_1(E_177) | ~m1_subset_1(D_176, k1_zfmisc_1(A_173)) | v1_xboole_0(D_176) | ~m1_subset_1(C_175, k1_zfmisc_1(A_173)) | v1_xboole_0(C_175) | v1_xboole_0(B_174) | v1_xboole_0(A_173))), inference(cnfTransformation, [status(thm)], [f_222])).
% 31.20/20.62  tff(c_62, plain, (![E_177, F_178, B_174, D_176, C_175, A_173]: (m1_subset_1(k1_tmap_1(A_173, B_174, C_175, D_176, E_177, F_178), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_173, C_175, D_176), B_174))) | ~m1_subset_1(F_178, k1_zfmisc_1(k2_zfmisc_1(D_176, B_174))) | ~v1_funct_2(F_178, D_176, B_174) | ~v1_funct_1(F_178) | ~m1_subset_1(E_177, k1_zfmisc_1(k2_zfmisc_1(C_175, B_174))) | ~v1_funct_2(E_177, C_175, B_174) | ~v1_funct_1(E_177) | ~m1_subset_1(D_176, k1_zfmisc_1(A_173)) | v1_xboole_0(D_176) | ~m1_subset_1(C_175, k1_zfmisc_1(A_173)) | v1_xboole_0(C_175) | v1_xboole_0(B_174) | v1_xboole_0(A_173))), inference(cnfTransformation, [status(thm)], [f_222])).
% 31.20/20.62  tff(c_48477, plain, (![C_2366, F_2362, E_2363, D_2365, B_2364, A_2367]: (k2_partfun1(k4_subset_1(A_2367, C_2366, D_2365), B_2364, k1_tmap_1(A_2367, B_2364, C_2366, D_2365, E_2363, F_2362), C_2366)=E_2363 | ~m1_subset_1(k1_tmap_1(A_2367, B_2364, C_2366, D_2365, E_2363, F_2362), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_2367, C_2366, D_2365), B_2364))) | ~v1_funct_2(k1_tmap_1(A_2367, B_2364, C_2366, D_2365, E_2363, F_2362), k4_subset_1(A_2367, C_2366, D_2365), B_2364) | ~v1_funct_1(k1_tmap_1(A_2367, B_2364, C_2366, D_2365, E_2363, F_2362)) | k2_partfun1(D_2365, B_2364, F_2362, k9_subset_1(A_2367, C_2366, D_2365))!=k2_partfun1(C_2366, B_2364, E_2363, k9_subset_1(A_2367, C_2366, D_2365)) | ~m1_subset_1(F_2362, k1_zfmisc_1(k2_zfmisc_1(D_2365, B_2364))) | ~v1_funct_2(F_2362, D_2365, B_2364) | ~v1_funct_1(F_2362) | ~m1_subset_1(E_2363, k1_zfmisc_1(k2_zfmisc_1(C_2366, B_2364))) | ~v1_funct_2(E_2363, C_2366, B_2364) | ~v1_funct_1(E_2363) | ~m1_subset_1(D_2365, k1_zfmisc_1(A_2367)) | v1_xboole_0(D_2365) | ~m1_subset_1(C_2366, k1_zfmisc_1(A_2367)) | v1_xboole_0(C_2366) | v1_xboole_0(B_2364) | v1_xboole_0(A_2367))), inference(cnfTransformation, [status(thm)], [f_188])).
% 31.20/20.62  tff(c_81679, plain, (![A_3822, C_3821, B_3824, E_3823, F_3826, D_3825]: (k2_partfun1(k4_subset_1(A_3822, C_3821, D_3825), B_3824, k1_tmap_1(A_3822, B_3824, C_3821, D_3825, E_3823, F_3826), C_3821)=E_3823 | ~v1_funct_2(k1_tmap_1(A_3822, B_3824, C_3821, D_3825, E_3823, F_3826), k4_subset_1(A_3822, C_3821, D_3825), B_3824) | ~v1_funct_1(k1_tmap_1(A_3822, B_3824, C_3821, D_3825, E_3823, F_3826)) | k2_partfun1(D_3825, B_3824, F_3826, k9_subset_1(A_3822, C_3821, D_3825))!=k2_partfun1(C_3821, B_3824, E_3823, k9_subset_1(A_3822, C_3821, D_3825)) | ~m1_subset_1(F_3826, k1_zfmisc_1(k2_zfmisc_1(D_3825, B_3824))) | ~v1_funct_2(F_3826, D_3825, B_3824) | ~v1_funct_1(F_3826) | ~m1_subset_1(E_3823, k1_zfmisc_1(k2_zfmisc_1(C_3821, B_3824))) | ~v1_funct_2(E_3823, C_3821, B_3824) | ~v1_funct_1(E_3823) | ~m1_subset_1(D_3825, k1_zfmisc_1(A_3822)) | v1_xboole_0(D_3825) | ~m1_subset_1(C_3821, k1_zfmisc_1(A_3822)) | v1_xboole_0(C_3821) | v1_xboole_0(B_3824) | v1_xboole_0(A_3822))), inference(resolution, [status(thm)], [c_62, c_48477])).
% 31.20/20.62  tff(c_91551, plain, (![C_4206, B_4209, E_4208, D_4210, A_4207, F_4211]: (k2_partfun1(k4_subset_1(A_4207, C_4206, D_4210), B_4209, k1_tmap_1(A_4207, B_4209, C_4206, D_4210, E_4208, F_4211), C_4206)=E_4208 | ~v1_funct_1(k1_tmap_1(A_4207, B_4209, C_4206, D_4210, E_4208, F_4211)) | k2_partfun1(D_4210, B_4209, F_4211, k9_subset_1(A_4207, C_4206, D_4210))!=k2_partfun1(C_4206, B_4209, E_4208, k9_subset_1(A_4207, C_4206, D_4210)) | ~m1_subset_1(F_4211, k1_zfmisc_1(k2_zfmisc_1(D_4210, B_4209))) | ~v1_funct_2(F_4211, D_4210, B_4209) | ~v1_funct_1(F_4211) | ~m1_subset_1(E_4208, k1_zfmisc_1(k2_zfmisc_1(C_4206, B_4209))) | ~v1_funct_2(E_4208, C_4206, B_4209) | ~v1_funct_1(E_4208) | ~m1_subset_1(D_4210, k1_zfmisc_1(A_4207)) | v1_xboole_0(D_4210) | ~m1_subset_1(C_4206, k1_zfmisc_1(A_4207)) | v1_xboole_0(C_4206) | v1_xboole_0(B_4209) | v1_xboole_0(A_4207))), inference(resolution, [status(thm)], [c_64, c_81679])).
% 31.20/20.62  tff(c_91560, plain, (![A_4207, C_4206, E_4208]: (k2_partfun1(k4_subset_1(A_4207, C_4206, '#skF_5'), '#skF_3', k1_tmap_1(A_4207, '#skF_3', C_4206, '#skF_5', E_4208, '#skF_7'), C_4206)=E_4208 | ~v1_funct_1(k1_tmap_1(A_4207, '#skF_3', C_4206, '#skF_5', E_4208, '#skF_7')) | k2_partfun1(C_4206, '#skF_3', E_4208, k9_subset_1(A_4207, C_4206, '#skF_5'))!=k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1(A_4207, C_4206, '#skF_5')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_4208, k1_zfmisc_1(k2_zfmisc_1(C_4206, '#skF_3'))) | ~v1_funct_2(E_4208, C_4206, '#skF_3') | ~v1_funct_1(E_4208) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4207)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_4206, k1_zfmisc_1(A_4207)) | v1_xboole_0(C_4206) | v1_xboole_0('#skF_3') | v1_xboole_0(A_4207))), inference(resolution, [status(thm)], [c_70, c_91551])).
% 31.20/20.62  tff(c_91568, plain, (![A_4207, C_4206, E_4208]: (k2_partfun1(k4_subset_1(A_4207, C_4206, '#skF_5'), '#skF_3', k1_tmap_1(A_4207, '#skF_3', C_4206, '#skF_5', E_4208, '#skF_7'), C_4206)=E_4208 | ~v1_funct_1(k1_tmap_1(A_4207, '#skF_3', C_4206, '#skF_5', E_4208, '#skF_7')) | k2_partfun1(C_4206, '#skF_3', E_4208, k9_subset_1(A_4207, C_4206, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_4207, C_4206, '#skF_5')) | ~m1_subset_1(E_4208, k1_zfmisc_1(k2_zfmisc_1(C_4206, '#skF_3'))) | ~v1_funct_2(E_4208, C_4206, '#skF_3') | ~v1_funct_1(E_4208) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4207)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_4206, k1_zfmisc_1(A_4207)) | v1_xboole_0(C_4206) | v1_xboole_0('#skF_3') | v1_xboole_0(A_4207))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_47908, c_91560])).
% 31.20/20.62  tff(c_100543, plain, (![A_4553, C_4554, E_4555]: (k2_partfun1(k4_subset_1(A_4553, C_4554, '#skF_5'), '#skF_3', k1_tmap_1(A_4553, '#skF_3', C_4554, '#skF_5', E_4555, '#skF_7'), C_4554)=E_4555 | ~v1_funct_1(k1_tmap_1(A_4553, '#skF_3', C_4554, '#skF_5', E_4555, '#skF_7')) | k2_partfun1(C_4554, '#skF_3', E_4555, k9_subset_1(A_4553, C_4554, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_4553, C_4554, '#skF_5')) | ~m1_subset_1(E_4555, k1_zfmisc_1(k2_zfmisc_1(C_4554, '#skF_3'))) | ~v1_funct_2(E_4555, C_4554, '#skF_3') | ~v1_funct_1(E_4555) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4553)) | ~m1_subset_1(C_4554, k1_zfmisc_1(A_4553)) | v1_xboole_0(C_4554) | v1_xboole_0(A_4553))), inference(negUnitSimplification, [status(thm)], [c_92, c_86, c_91568])).
% 31.20/20.62  tff(c_100556, plain, (![A_4553]: (k2_partfun1(k4_subset_1(A_4553, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_4553, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_4553, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1(A_4553, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_4553, '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4553)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4553)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_4553))), inference(resolution, [status(thm)], [c_76, c_100543])).
% 31.20/20.62  tff(c_100568, plain, (![A_4553]: (k2_partfun1(k4_subset_1(A_4553, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_4553, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_4553, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_4553, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_4553, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4553)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4553)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_4553))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_47911, c_100556])).
% 31.20/20.62  tff(c_102368, plain, (![A_4582]: (k2_partfun1(k4_subset_1(A_4582, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_4582, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_4582, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_4582, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_4582, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4582)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4582)) | v1_xboole_0(A_4582))), inference(negUnitSimplification, [status(thm)], [c_90, c_100568])).
% 31.20/20.62  tff(c_2515, plain, (![C_545, B_546, A_547]: (~v1_xboole_0(C_545) | ~m1_subset_1(B_546, k1_zfmisc_1(C_545)) | ~r2_hidden(A_547, B_546))), inference(cnfTransformation, [status(thm)], [f_76])).
% 31.20/20.62  tff(c_2549, plain, (![B_553, A_554, A_555]: (~v1_xboole_0(B_553) | ~r2_hidden(A_554, A_555) | ~r1_tarski(A_555, B_553))), inference(resolution, [status(thm)], [c_26, c_2515])).
% 31.20/20.62  tff(c_2595, plain, (![B_567, B_568, A_569]: (~v1_xboole_0(B_567) | ~r1_tarski(B_568, B_567) | r1_xboole_0(A_569, B_568))), inference(resolution, [status(thm)], [c_10, c_2549])).
% 31.20/20.62  tff(c_2610, plain, (![B_9, A_569]: (~v1_xboole_0(B_9) | r1_xboole_0(A_569, B_9))), inference(resolution, [status(thm)], [c_18, c_2595])).
% 31.20/20.62  tff(c_2438, plain, (![C_524, A_525, B_526]: (v1_relat_1(C_524) | ~m1_subset_1(C_524, k1_zfmisc_1(k2_zfmisc_1(A_525, B_526))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 31.20/20.62  tff(c_2450, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_70, c_2438])).
% 31.20/20.62  tff(c_2501, plain, (![C_542, A_543, B_544]: (v4_relat_1(C_542, A_543) | ~m1_subset_1(C_542, k1_zfmisc_1(k2_zfmisc_1(A_543, B_544))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 31.20/20.62  tff(c_2513, plain, (v4_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_70, c_2501])).
% 31.20/20.62  tff(c_2653, plain, (![B_581, A_582]: (k7_relat_1(B_581, A_582)=B_581 | ~v4_relat_1(B_581, A_582) | ~v1_relat_1(B_581))), inference(cnfTransformation, [status(thm)], [f_92])).
% 31.20/20.62  tff(c_2662, plain, (k7_relat_1('#skF_7', '#skF_5')='#skF_7' | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_2513, c_2653])).
% 31.20/20.62  tff(c_2671, plain, (k7_relat_1('#skF_7', '#skF_5')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_2450, c_2662])).
% 31.20/20.62  tff(c_3840, plain, (![C_690, A_691, B_692]: (k7_relat_1(k7_relat_1(C_690, A_691), B_692)=k1_xboole_0 | ~r1_xboole_0(A_691, B_692) | ~v1_relat_1(C_690))), inference(cnfTransformation, [status(thm)], [f_86])).
% 31.20/20.62  tff(c_3875, plain, (![B_692]: (k7_relat_1('#skF_7', B_692)=k1_xboole_0 | ~r1_xboole_0('#skF_5', B_692) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2671, c_3840])).
% 31.20/20.62  tff(c_3891, plain, (![B_693]: (k7_relat_1('#skF_7', B_693)=k1_xboole_0 | ~r1_xboole_0('#skF_5', B_693))), inference(demodulation, [status(thm), theory('equality')], [c_2450, c_3875])).
% 31.20/20.62  tff(c_3914, plain, (![B_694]: (k7_relat_1('#skF_7', B_694)=k1_xboole_0 | ~v1_xboole_0(B_694))), inference(resolution, [status(thm)], [c_2610, c_3891])).
% 31.20/20.62  tff(c_3918, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_3914])).
% 31.20/20.62  tff(c_2689, plain, (![A_585, B_586]: (r1_xboole_0(A_585, B_586) | ~r1_subset_1(A_585, B_586) | v1_xboole_0(B_586) | v1_xboole_0(A_585))), inference(cnfTransformation, [status(thm)], [f_102])).
% 31.20/20.62  tff(c_4632, plain, (![A_788, B_789]: (k3_xboole_0(A_788, B_789)=k1_xboole_0 | ~r1_subset_1(A_788, B_789) | v1_xboole_0(B_789) | v1_xboole_0(A_788))), inference(resolution, [status(thm)], [c_2689, c_2])).
% 31.20/20.62  tff(c_4638, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0 | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_82, c_4632])).
% 31.20/20.62  tff(c_4642, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_90, c_86, c_4638])).
% 31.20/20.62  tff(c_38, plain, (![A_28, B_29]: (r1_xboole_0(A_28, B_29) | ~r1_subset_1(A_28, B_29) | v1_xboole_0(B_29) | v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_102])).
% 31.20/20.62  tff(c_2451, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_2438])).
% 31.20/20.62  tff(c_2514, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_76, c_2501])).
% 31.20/20.62  tff(c_2659, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2514, c_2653])).
% 31.20/20.62  tff(c_2668, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2451, c_2659])).
% 31.20/20.62  tff(c_3878, plain, (![B_692]: (k7_relat_1('#skF_6', B_692)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_692) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2668, c_3840])).
% 31.20/20.62  tff(c_3972, plain, (![B_701]: (k7_relat_1('#skF_6', B_701)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_701))), inference(demodulation, [status(thm), theory('equality')], [c_2451, c_3878])).
% 31.20/20.62  tff(c_3976, plain, (![B_29]: (k7_relat_1('#skF_6', B_29)=k1_xboole_0 | ~r1_subset_1('#skF_4', B_29) | v1_xboole_0(B_29) | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_38, c_3972])).
% 31.20/20.62  tff(c_4224, plain, (![B_717]: (k7_relat_1('#skF_6', B_717)=k1_xboole_0 | ~r1_subset_1('#skF_4', B_717) | v1_xboole_0(B_717))), inference(negUnitSimplification, [status(thm)], [c_90, c_3976])).
% 31.20/20.62  tff(c_4227, plain, (k7_relat_1('#skF_6', '#skF_5')=k1_xboole_0 | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_82, c_4224])).
% 31.20/20.63  tff(c_4230, plain, (k7_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_86, c_4227])).
% 31.20/20.63  tff(c_2745, plain, (![B_598, A_599]: (k1_relat_1(B_598)=A_599 | ~v1_partfun1(B_598, A_599) | ~v4_relat_1(B_598, A_599) | ~v1_relat_1(B_598))), inference(cnfTransformation, [status(thm)], [f_134])).
% 31.20/20.63  tff(c_2751, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2514, c_2745])).
% 31.20/20.63  tff(c_2760, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2451, c_2751])).
% 31.20/20.63  tff(c_2764, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_2760])).
% 31.20/20.63  tff(c_3421, plain, (![C_654, A_655, B_656]: (v1_partfun1(C_654, A_655) | ~v1_funct_2(C_654, A_655, B_656) | ~v1_funct_1(C_654) | ~m1_subset_1(C_654, k1_zfmisc_1(k2_zfmisc_1(A_655, B_656))) | v1_xboole_0(B_656))), inference(cnfTransformation, [status(thm)], [f_126])).
% 31.20/20.63  tff(c_3431, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_76, c_3421])).
% 31.20/20.63  tff(c_3439, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_3431])).
% 31.20/20.63  tff(c_3441, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_2764, c_3439])).
% 31.20/20.63  tff(c_3442, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_2760])).
% 31.20/20.63  tff(c_30, plain, (![B_22, A_21]: (k7_relat_1(B_22, k3_xboole_0(k1_relat_1(B_22), A_21))=k7_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_80])).
% 31.20/20.63  tff(c_3447, plain, (![A_21]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_4', A_21))=k7_relat_1('#skF_6', A_21) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3442, c_30])).
% 31.20/20.63  tff(c_3454, plain, (![A_21]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_4', A_21))=k7_relat_1('#skF_6', A_21))), inference(demodulation, [status(thm), theory('equality')], [c_2451, c_3447])).
% 31.20/20.63  tff(c_3919, plain, (![A_695, B_696, C_697]: (k9_subset_1(A_695, B_696, C_697)=k3_xboole_0(B_696, C_697) | ~m1_subset_1(C_697, k1_zfmisc_1(A_695)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 31.20/20.63  tff(c_3934, plain, (![B_696]: (k9_subset_1('#skF_2', B_696, '#skF_5')=k3_xboole_0(B_696, '#skF_5'))), inference(resolution, [status(thm)], [c_84, c_3919])).
% 31.20/20.63  tff(c_4282, plain, (![B_725, A_723, F_727, C_722, D_726, E_724]: (v1_funct_1(k1_tmap_1(A_723, B_725, C_722, D_726, E_724, F_727)) | ~m1_subset_1(F_727, k1_zfmisc_1(k2_zfmisc_1(D_726, B_725))) | ~v1_funct_2(F_727, D_726, B_725) | ~v1_funct_1(F_727) | ~m1_subset_1(E_724, k1_zfmisc_1(k2_zfmisc_1(C_722, B_725))) | ~v1_funct_2(E_724, C_722, B_725) | ~v1_funct_1(E_724) | ~m1_subset_1(D_726, k1_zfmisc_1(A_723)) | v1_xboole_0(D_726) | ~m1_subset_1(C_722, k1_zfmisc_1(A_723)) | v1_xboole_0(C_722) | v1_xboole_0(B_725) | v1_xboole_0(A_723))), inference(cnfTransformation, [status(thm)], [f_222])).
% 31.20/20.63  tff(c_4287, plain, (![A_723, C_722, E_724]: (v1_funct_1(k1_tmap_1(A_723, '#skF_3', C_722, '#skF_5', E_724, '#skF_7')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_724, k1_zfmisc_1(k2_zfmisc_1(C_722, '#skF_3'))) | ~v1_funct_2(E_724, C_722, '#skF_3') | ~v1_funct_1(E_724) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_723)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_722, k1_zfmisc_1(A_723)) | v1_xboole_0(C_722) | v1_xboole_0('#skF_3') | v1_xboole_0(A_723))), inference(resolution, [status(thm)], [c_70, c_4282])).
% 31.20/20.63  tff(c_4293, plain, (![A_723, C_722, E_724]: (v1_funct_1(k1_tmap_1(A_723, '#skF_3', C_722, '#skF_5', E_724, '#skF_7')) | ~m1_subset_1(E_724, k1_zfmisc_1(k2_zfmisc_1(C_722, '#skF_3'))) | ~v1_funct_2(E_724, C_722, '#skF_3') | ~v1_funct_1(E_724) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_723)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_722, k1_zfmisc_1(A_723)) | v1_xboole_0(C_722) | v1_xboole_0('#skF_3') | v1_xboole_0(A_723))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_4287])).
% 31.20/20.63  tff(c_4580, plain, (![A_777, C_778, E_779]: (v1_funct_1(k1_tmap_1(A_777, '#skF_3', C_778, '#skF_5', E_779, '#skF_7')) | ~m1_subset_1(E_779, k1_zfmisc_1(k2_zfmisc_1(C_778, '#skF_3'))) | ~v1_funct_2(E_779, C_778, '#skF_3') | ~v1_funct_1(E_779) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_777)) | ~m1_subset_1(C_778, k1_zfmisc_1(A_777)) | v1_xboole_0(C_778) | v1_xboole_0(A_777))), inference(negUnitSimplification, [status(thm)], [c_92, c_86, c_4293])).
% 31.20/20.63  tff(c_4593, plain, (![A_777]: (v1_funct_1(k1_tmap_1(A_777, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_777)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_777)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_777))), inference(resolution, [status(thm)], [c_76, c_4580])).
% 31.20/20.63  tff(c_4605, plain, (![A_777]: (v1_funct_1(k1_tmap_1(A_777, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_777)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_777)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_777))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_4593])).
% 31.20/20.63  tff(c_4852, plain, (![A_809]: (v1_funct_1(k1_tmap_1(A_809, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_809)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_809)) | v1_xboole_0(A_809))), inference(negUnitSimplification, [status(thm)], [c_90, c_4605])).
% 31.20/20.63  tff(c_4859, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_84, c_4852])).
% 31.20/20.63  tff(c_4863, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_4859])).
% 31.20/20.63  tff(c_4864, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_94, c_4863])).
% 31.20/20.63  tff(c_4057, plain, (![A_705, B_706, C_707, D_708]: (k2_partfun1(A_705, B_706, C_707, D_708)=k7_relat_1(C_707, D_708) | ~m1_subset_1(C_707, k1_zfmisc_1(k2_zfmisc_1(A_705, B_706))) | ~v1_funct_1(C_707))), inference(cnfTransformation, [status(thm)], [f_140])).
% 31.20/20.63  tff(c_4064, plain, (![D_708]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_708)=k7_relat_1('#skF_6', D_708) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_76, c_4057])).
% 31.20/20.63  tff(c_4071, plain, (![D_708]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_708)=k7_relat_1('#skF_6', D_708))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_4064])).
% 31.20/20.63  tff(c_4062, plain, (![D_708]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_708)=k7_relat_1('#skF_7', D_708) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_70, c_4057])).
% 31.20/20.63  tff(c_4068, plain, (![D_708]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_708)=k7_relat_1('#skF_7', D_708))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_4062])).
% 31.20/20.63  tff(c_4558, plain, (![F_769, D_772, E_770, C_773, B_771, A_774]: (k2_partfun1(k4_subset_1(A_774, C_773, D_772), B_771, k1_tmap_1(A_774, B_771, C_773, D_772, E_770, F_769), D_772)=F_769 | ~m1_subset_1(k1_tmap_1(A_774, B_771, C_773, D_772, E_770, F_769), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_774, C_773, D_772), B_771))) | ~v1_funct_2(k1_tmap_1(A_774, B_771, C_773, D_772, E_770, F_769), k4_subset_1(A_774, C_773, D_772), B_771) | ~v1_funct_1(k1_tmap_1(A_774, B_771, C_773, D_772, E_770, F_769)) | k2_partfun1(D_772, B_771, F_769, k9_subset_1(A_774, C_773, D_772))!=k2_partfun1(C_773, B_771, E_770, k9_subset_1(A_774, C_773, D_772)) | ~m1_subset_1(F_769, k1_zfmisc_1(k2_zfmisc_1(D_772, B_771))) | ~v1_funct_2(F_769, D_772, B_771) | ~v1_funct_1(F_769) | ~m1_subset_1(E_770, k1_zfmisc_1(k2_zfmisc_1(C_773, B_771))) | ~v1_funct_2(E_770, C_773, B_771) | ~v1_funct_1(E_770) | ~m1_subset_1(D_772, k1_zfmisc_1(A_774)) | v1_xboole_0(D_772) | ~m1_subset_1(C_773, k1_zfmisc_1(A_774)) | v1_xboole_0(C_773) | v1_xboole_0(B_771) | v1_xboole_0(A_774))), inference(cnfTransformation, [status(thm)], [f_188])).
% 31.20/20.63  tff(c_10817, plain, (![D_1176, E_1174, F_1177, A_1173, C_1172, B_1175]: (k2_partfun1(k4_subset_1(A_1173, C_1172, D_1176), B_1175, k1_tmap_1(A_1173, B_1175, C_1172, D_1176, E_1174, F_1177), D_1176)=F_1177 | ~v1_funct_2(k1_tmap_1(A_1173, B_1175, C_1172, D_1176, E_1174, F_1177), k4_subset_1(A_1173, C_1172, D_1176), B_1175) | ~v1_funct_1(k1_tmap_1(A_1173, B_1175, C_1172, D_1176, E_1174, F_1177)) | k2_partfun1(D_1176, B_1175, F_1177, k9_subset_1(A_1173, C_1172, D_1176))!=k2_partfun1(C_1172, B_1175, E_1174, k9_subset_1(A_1173, C_1172, D_1176)) | ~m1_subset_1(F_1177, k1_zfmisc_1(k2_zfmisc_1(D_1176, B_1175))) | ~v1_funct_2(F_1177, D_1176, B_1175) | ~v1_funct_1(F_1177) | ~m1_subset_1(E_1174, k1_zfmisc_1(k2_zfmisc_1(C_1172, B_1175))) | ~v1_funct_2(E_1174, C_1172, B_1175) | ~v1_funct_1(E_1174) | ~m1_subset_1(D_1176, k1_zfmisc_1(A_1173)) | v1_xboole_0(D_1176) | ~m1_subset_1(C_1172, k1_zfmisc_1(A_1173)) | v1_xboole_0(C_1172) | v1_xboole_0(B_1175) | v1_xboole_0(A_1173))), inference(resolution, [status(thm)], [c_62, c_4558])).
% 31.20/20.63  tff(c_20510, plain, (![D_1563, E_1561, C_1559, F_1564, B_1562, A_1560]: (k2_partfun1(k4_subset_1(A_1560, C_1559, D_1563), B_1562, k1_tmap_1(A_1560, B_1562, C_1559, D_1563, E_1561, F_1564), D_1563)=F_1564 | ~v1_funct_1(k1_tmap_1(A_1560, B_1562, C_1559, D_1563, E_1561, F_1564)) | k2_partfun1(D_1563, B_1562, F_1564, k9_subset_1(A_1560, C_1559, D_1563))!=k2_partfun1(C_1559, B_1562, E_1561, k9_subset_1(A_1560, C_1559, D_1563)) | ~m1_subset_1(F_1564, k1_zfmisc_1(k2_zfmisc_1(D_1563, B_1562))) | ~v1_funct_2(F_1564, D_1563, B_1562) | ~v1_funct_1(F_1564) | ~m1_subset_1(E_1561, k1_zfmisc_1(k2_zfmisc_1(C_1559, B_1562))) | ~v1_funct_2(E_1561, C_1559, B_1562) | ~v1_funct_1(E_1561) | ~m1_subset_1(D_1563, k1_zfmisc_1(A_1560)) | v1_xboole_0(D_1563) | ~m1_subset_1(C_1559, k1_zfmisc_1(A_1560)) | v1_xboole_0(C_1559) | v1_xboole_0(B_1562) | v1_xboole_0(A_1560))), inference(resolution, [status(thm)], [c_64, c_10817])).
% 31.20/20.63  tff(c_20519, plain, (![A_1560, C_1559, E_1561]: (k2_partfun1(k4_subset_1(A_1560, C_1559, '#skF_5'), '#skF_3', k1_tmap_1(A_1560, '#skF_3', C_1559, '#skF_5', E_1561, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1560, '#skF_3', C_1559, '#skF_5', E_1561, '#skF_7')) | k2_partfun1(C_1559, '#skF_3', E_1561, k9_subset_1(A_1560, C_1559, '#skF_5'))!=k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1(A_1560, C_1559, '#skF_5')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_1561, k1_zfmisc_1(k2_zfmisc_1(C_1559, '#skF_3'))) | ~v1_funct_2(E_1561, C_1559, '#skF_3') | ~v1_funct_1(E_1561) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1560)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1559, k1_zfmisc_1(A_1560)) | v1_xboole_0(C_1559) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1560))), inference(resolution, [status(thm)], [c_70, c_20510])).
% 31.20/20.63  tff(c_20527, plain, (![A_1560, C_1559, E_1561]: (k2_partfun1(k4_subset_1(A_1560, C_1559, '#skF_5'), '#skF_3', k1_tmap_1(A_1560, '#skF_3', C_1559, '#skF_5', E_1561, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1560, '#skF_3', C_1559, '#skF_5', E_1561, '#skF_7')) | k2_partfun1(C_1559, '#skF_3', E_1561, k9_subset_1(A_1560, C_1559, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_1560, C_1559, '#skF_5')) | ~m1_subset_1(E_1561, k1_zfmisc_1(k2_zfmisc_1(C_1559, '#skF_3'))) | ~v1_funct_2(E_1561, C_1559, '#skF_3') | ~v1_funct_1(E_1561) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1560)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1559, k1_zfmisc_1(A_1560)) | v1_xboole_0(C_1559) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1560))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_4068, c_20519])).
% 31.20/20.63  tff(c_44928, plain, (![A_2076, C_2077, E_2078]: (k2_partfun1(k4_subset_1(A_2076, C_2077, '#skF_5'), '#skF_3', k1_tmap_1(A_2076, '#skF_3', C_2077, '#skF_5', E_2078, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_2076, '#skF_3', C_2077, '#skF_5', E_2078, '#skF_7')) | k2_partfun1(C_2077, '#skF_3', E_2078, k9_subset_1(A_2076, C_2077, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_2076, C_2077, '#skF_5')) | ~m1_subset_1(E_2078, k1_zfmisc_1(k2_zfmisc_1(C_2077, '#skF_3'))) | ~v1_funct_2(E_2078, C_2077, '#skF_3') | ~v1_funct_1(E_2078) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2076)) | ~m1_subset_1(C_2077, k1_zfmisc_1(A_2076)) | v1_xboole_0(C_2077) | v1_xboole_0(A_2076))), inference(negUnitSimplification, [status(thm)], [c_92, c_86, c_20527])).
% 31.20/20.63  tff(c_44947, plain, (![A_2076]: (k2_partfun1(k4_subset_1(A_2076, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_2076, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_2076, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1(A_2076, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_2076, '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2076)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2076)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_2076))), inference(resolution, [status(thm)], [c_76, c_44928])).
% 31.20/20.63  tff(c_44961, plain, (![A_2076]: (k2_partfun1(k4_subset_1(A_2076, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_2076, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_2076, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_2076, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_2076, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2076)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2076)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_2076))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_4071, c_44947])).
% 31.20/20.63  tff(c_45918, plain, (![A_2083]: (k2_partfun1(k4_subset_1(A_2083, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_2083, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_2083, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_2083, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_2083, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2083)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2083)) | v1_xboole_0(A_2083))), inference(negUnitSimplification, [status(thm)], [c_90, c_44961])).
% 31.20/20.63  tff(c_261, plain, (![C_273, B_274, A_275]: (~v1_xboole_0(C_273) | ~m1_subset_1(B_274, k1_zfmisc_1(C_273)) | ~r2_hidden(A_275, B_274))), inference(cnfTransformation, [status(thm)], [f_76])).
% 31.20/20.63  tff(c_277, plain, (![B_276, A_277, A_278]: (~v1_xboole_0(B_276) | ~r2_hidden(A_277, A_278) | ~r1_tarski(A_278, B_276))), inference(resolution, [status(thm)], [c_26, c_261])).
% 31.20/20.63  tff(c_381, plain, (![B_298, B_299, A_300]: (~v1_xboole_0(B_298) | ~r1_tarski(B_299, B_298) | r1_xboole_0(A_300, B_299))), inference(resolution, [status(thm)], [c_10, c_277])).
% 31.20/20.63  tff(c_396, plain, (![B_9, A_300]: (~v1_xboole_0(B_9) | r1_xboole_0(A_300, B_9))), inference(resolution, [status(thm)], [c_18, c_381])).
% 31.20/20.63  tff(c_127, plain, (![C_247, A_248, B_249]: (v1_relat_1(C_247) | ~m1_subset_1(C_247, k1_zfmisc_1(k2_zfmisc_1(A_248, B_249))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 31.20/20.63  tff(c_139, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_70, c_127])).
% 31.20/20.63  tff(c_305, plain, (![C_284, A_285, B_286]: (v4_relat_1(C_284, A_285) | ~m1_subset_1(C_284, k1_zfmisc_1(k2_zfmisc_1(A_285, B_286))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 31.20/20.63  tff(c_317, plain, (v4_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_70, c_305])).
% 31.20/20.63  tff(c_321, plain, (k7_relat_1('#skF_7', '#skF_5')='#skF_7' | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_317, c_34])).
% 31.20/20.63  tff(c_324, plain, (k7_relat_1('#skF_7', '#skF_5')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_139, c_321])).
% 31.20/20.63  tff(c_1427, plain, (![C_409, A_410, B_411]: (k7_relat_1(k7_relat_1(C_409, A_410), B_411)=k1_xboole_0 | ~r1_xboole_0(A_410, B_411) | ~v1_relat_1(C_409))), inference(cnfTransformation, [status(thm)], [f_86])).
% 31.20/20.63  tff(c_1465, plain, (![B_411]: (k7_relat_1('#skF_7', B_411)=k1_xboole_0 | ~r1_xboole_0('#skF_5', B_411) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_324, c_1427])).
% 31.20/20.63  tff(c_1530, plain, (![B_418]: (k7_relat_1('#skF_7', B_418)=k1_xboole_0 | ~r1_xboole_0('#skF_5', B_418))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_1465])).
% 31.20/20.63  tff(c_1553, plain, (![B_419]: (k7_relat_1('#skF_7', B_419)=k1_xboole_0 | ~v1_xboole_0(B_419))), inference(resolution, [status(thm)], [c_396, c_1530])).
% 31.20/20.63  tff(c_1557, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_1553])).
% 31.20/20.63  tff(c_405, plain, (![A_303, B_304]: (r1_xboole_0(A_303, B_304) | ~r1_subset_1(A_303, B_304) | v1_xboole_0(B_304) | v1_xboole_0(A_303))), inference(cnfTransformation, [status(thm)], [f_102])).
% 31.20/20.63  tff(c_2139, plain, (![A_495, B_496]: (k3_xboole_0(A_495, B_496)=k1_xboole_0 | ~r1_subset_1(A_495, B_496) | v1_xboole_0(B_496) | v1_xboole_0(A_495))), inference(resolution, [status(thm)], [c_405, c_2])).
% 31.20/20.63  tff(c_2145, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0 | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_82, c_2139])).
% 31.20/20.63  tff(c_2149, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_90, c_86, c_2145])).
% 31.20/20.63  tff(c_140, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_127])).
% 31.20/20.63  tff(c_318, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_76, c_305])).
% 31.20/20.63  tff(c_327, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_318, c_34])).
% 31.20/20.63  tff(c_330, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_140, c_327])).
% 31.20/20.63  tff(c_1462, plain, (![B_411]: (k7_relat_1('#skF_6', B_411)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_411) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_330, c_1427])).
% 31.20/20.63  tff(c_1478, plain, (![B_412]: (k7_relat_1('#skF_6', B_412)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_412))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_1462])).
% 31.20/20.63  tff(c_1482, plain, (![B_29]: (k7_relat_1('#skF_6', B_29)=k1_xboole_0 | ~r1_subset_1('#skF_4', B_29) | v1_xboole_0(B_29) | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_38, c_1478])).
% 31.20/20.63  tff(c_1558, plain, (![B_420]: (k7_relat_1('#skF_6', B_420)=k1_xboole_0 | ~r1_subset_1('#skF_4', B_420) | v1_xboole_0(B_420))), inference(negUnitSimplification, [status(thm)], [c_90, c_1482])).
% 31.20/20.63  tff(c_1561, plain, (k7_relat_1('#skF_6', '#skF_5')=k1_xboole_0 | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_82, c_1558])).
% 31.20/20.63  tff(c_1564, plain, (k7_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_86, c_1561])).
% 31.20/20.63  tff(c_585, plain, (![B_339, A_340]: (k1_relat_1(B_339)=A_340 | ~v1_partfun1(B_339, A_340) | ~v4_relat_1(B_339, A_340) | ~v1_relat_1(B_339))), inference(cnfTransformation, [status(thm)], [f_134])).
% 31.20/20.63  tff(c_591, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_318, c_585])).
% 31.20/20.63  tff(c_600, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_591])).
% 31.20/20.63  tff(c_604, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_600])).
% 31.20/20.63  tff(c_1111, plain, (![C_382, A_383, B_384]: (v1_partfun1(C_382, A_383) | ~v1_funct_2(C_382, A_383, B_384) | ~v1_funct_1(C_382) | ~m1_subset_1(C_382, k1_zfmisc_1(k2_zfmisc_1(A_383, B_384))) | v1_xboole_0(B_384))), inference(cnfTransformation, [status(thm)], [f_126])).
% 31.20/20.63  tff(c_1121, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_76, c_1111])).
% 31.20/20.63  tff(c_1129, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_1121])).
% 31.20/20.63  tff(c_1131, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_604, c_1129])).
% 31.20/20.63  tff(c_1132, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_600])).
% 31.20/20.63  tff(c_1137, plain, (![A_21]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_4', A_21))=k7_relat_1('#skF_6', A_21) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1132, c_30])).
% 31.20/20.63  tff(c_1144, plain, (![A_21]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_4', A_21))=k7_relat_1('#skF_6', A_21))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_1137])).
% 31.20/20.63  tff(c_1506, plain, (![A_414, B_415, C_416, D_417]: (k2_partfun1(A_414, B_415, C_416, D_417)=k7_relat_1(C_416, D_417) | ~m1_subset_1(C_416, k1_zfmisc_1(k2_zfmisc_1(A_414, B_415))) | ~v1_funct_1(C_416))), inference(cnfTransformation, [status(thm)], [f_140])).
% 31.20/20.63  tff(c_1513, plain, (![D_417]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_417)=k7_relat_1('#skF_6', D_417) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_76, c_1506])).
% 31.20/20.63  tff(c_1520, plain, (![D_417]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_417)=k7_relat_1('#skF_6', D_417))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1513])).
% 31.20/20.63  tff(c_1511, plain, (![D_417]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_417)=k7_relat_1('#skF_7', D_417) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_70, c_1506])).
% 31.20/20.63  tff(c_1517, plain, (![D_417]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_417)=k7_relat_1('#skF_7', D_417))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1511])).
% 31.20/20.63  tff(c_489, plain, (![A_325, B_326, C_327]: (k9_subset_1(A_325, B_326, C_327)=k3_xboole_0(B_326, C_327) | ~m1_subset_1(C_327, k1_zfmisc_1(A_325)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 31.20/20.63  tff(c_504, plain, (![B_326]: (k9_subset_1('#skF_2', B_326, '#skF_5')=k3_xboole_0(B_326, '#skF_5'))), inference(resolution, [status(thm)], [c_84, c_489])).
% 31.20/20.63  tff(c_68, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')!='#skF_7' | k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')!='#skF_6' | k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_264])).
% 31.20/20.63  tff(c_125, plain, (k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_68])).
% 31.20/20.63  tff(c_514, plain, (k2_partfun1('#skF_5', '#skF_3', '#skF_7', k3_xboole_0('#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_504, c_504, c_125])).
% 31.20/20.63  tff(c_1656, plain, (k2_partfun1('#skF_4', '#skF_3', '#skF_6', k3_xboole_0('#skF_4', '#skF_5'))!=k7_relat_1('#skF_7', k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1517, c_514])).
% 31.20/20.63  tff(c_2360, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1557, c_2149, c_1564, c_1144, c_1520, c_1656])).
% 31.20/20.63  tff(c_2361, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_68])).
% 31.20/20.63  tff(c_2414, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')!='#skF_7'), inference(splitLeft, [status(thm)], [c_2361])).
% 31.20/20.63  tff(c_45935, plain, (~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_45918, c_2414])).
% 31.20/20.63  tff(c_45957, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_84, c_3918, c_4642, c_4230, c_3454, c_3934, c_3934, c_4864, c_45935])).
% 31.20/20.63  tff(c_45959, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_45957])).
% 31.20/20.63  tff(c_45960, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_2361])).
% 31.20/20.63  tff(c_102388, plain, (~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_102368, c_45960])).
% 31.20/20.63  tff(c_102413, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_84, c_47896, c_48518, c_47751, c_47948, c_48518, c_47751, c_48469, c_102388])).
% 31.20/20.63  tff(c_102415, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_102413])).
% 31.20/20.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.20/20.63  
% 31.20/20.63  Inference rules
% 31.20/20.63  ----------------------
% 31.20/20.63  #Ref     : 0
% 31.20/20.63  #Sup     : 21521
% 31.20/20.63  #Fact    : 0
% 31.20/20.63  #Define  : 0
% 31.20/20.63  #Split   : 101
% 31.20/20.63  #Chain   : 0
% 31.20/20.63  #Close   : 0
% 31.20/20.63  
% 31.20/20.63  Ordering : KBO
% 31.20/20.63  
% 31.20/20.63  Simplification rules
% 31.20/20.63  ----------------------
% 31.20/20.63  #Subsume      : 2847
% 31.20/20.63  #Demod        : 36882
% 31.20/20.63  #Tautology    : 12651
% 31.20/20.63  #SimpNegUnit  : 949
% 31.20/20.63  #BackRed      : 13
% 31.20/20.63  
% 31.20/20.63  #Partial instantiations: 0
% 31.20/20.63  #Strategies tried      : 1
% 31.20/20.63  
% 31.20/20.63  Timing (in seconds)
% 31.20/20.63  ----------------------
% 31.20/20.63  Preprocessing        : 0.45
% 31.20/20.63  Parsing              : 0.22
% 31.20/20.63  CNF conversion       : 0.06
% 31.20/20.63  Main loop            : 19.36
% 31.20/20.63  Inferencing          : 3.47
% 31.20/20.63  Reduction            : 7.71
% 31.20/20.63  Demodulation         : 6.22
% 31.20/20.63  BG Simplification    : 0.33
% 31.20/20.63  Subsumption          : 7.15
% 31.20/20.63  Abstraction          : 0.45
% 31.20/20.63  MUC search           : 0.00
% 31.20/20.63  Cooper               : 0.00
% 31.20/20.63  Total                : 19.89
% 31.20/20.63  Index Insertion      : 0.00
% 31.20/20.63  Index Deletion       : 0.00
% 31.20/20.63  Index Matching       : 0.00
% 31.20/20.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
