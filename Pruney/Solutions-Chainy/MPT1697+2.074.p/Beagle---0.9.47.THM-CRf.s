%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:21 EST 2020

% Result     : Theorem 6.38s
% Output     : CNFRefutation 6.63s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 433 expanded)
%              Number of leaves         :   39 ( 177 expanded)
%              Depth                    :   12
%              Number of atoms          :  582 (2516 expanded)
%              Number of equality atoms :   97 ( 444 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_221,negated_conjecture,(
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

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_69,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_179,axiom,(
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

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_145,axiom,(
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

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_60,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_56,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_42,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_650,plain,(
    ! [C_292,A_293,B_294] :
      ( v1_relat_1(C_292)
      | ~ m1_subset_1(C_292,k1_zfmisc_1(k2_zfmisc_1(A_293,B_294))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_658,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_42,c_650])).

tff(c_18,plain,(
    ! [A_15] :
      ( k7_relat_1(A_15,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_666,plain,(
    k7_relat_1('#skF_8',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_658,c_18])).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_54,plain,(
    r1_subset_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_822,plain,(
    ! [A_311,B_312] :
      ( r1_xboole_0(A_311,B_312)
      | ~ r1_subset_1(A_311,B_312)
      | v1_xboole_0(B_312)
      | v1_xboole_0(A_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_75,plain,(
    ! [A_219,B_220,C_221] :
      ( ~ r1_xboole_0(A_219,B_220)
      | ~ r2_hidden(C_221,k3_xboole_0(A_219,B_220)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_675,plain,(
    ! [A_295,B_296,A_297] :
      ( ~ r1_xboole_0(A_295,B_296)
      | r1_xboole_0(A_297,k3_xboole_0(A_295,B_296)) ) ),
    inference(resolution,[status(thm)],[c_4,c_75])).

tff(c_14,plain,(
    ! [A_11] :
      ( ~ r1_xboole_0(A_11,A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_680,plain,(
    ! [A_295,B_296] :
      ( k3_xboole_0(A_295,B_296) = k1_xboole_0
      | ~ r1_xboole_0(A_295,B_296) ) ),
    inference(resolution,[status(thm)],[c_675,c_14])).

tff(c_2319,plain,(
    ! [A_569,B_570] :
      ( k3_xboole_0(A_569,B_570) = k1_xboole_0
      | ~ r1_subset_1(A_569,B_570)
      | v1_xboole_0(B_570)
      | v1_xboole_0(A_569) ) ),
    inference(resolution,[status(thm)],[c_822,c_680])).

tff(c_2322,plain,
    ( k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0
    | v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_2319])).

tff(c_2325,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_58,c_2322])).

tff(c_48,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_657,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_48,c_650])).

tff(c_662,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_657,c_18])).

tff(c_2269,plain,(
    ! [A_562,B_563,C_564] :
      ( k9_subset_1(A_562,B_563,C_564) = k3_xboole_0(B_563,C_564)
      | ~ m1_subset_1(C_564,k1_zfmisc_1(A_562)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2281,plain,(
    ! [B_563] : k9_subset_1('#skF_3',B_563,'#skF_6') = k3_xboole_0(B_563,'#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_2269])).

tff(c_52,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_50,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_46,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_44,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_2615,plain,(
    ! [C_601,A_599,E_604,F_600,B_603,D_602] :
      ( v1_funct_1(k1_tmap_1(A_599,B_603,C_601,D_602,E_604,F_600))
      | ~ m1_subset_1(F_600,k1_zfmisc_1(k2_zfmisc_1(D_602,B_603)))
      | ~ v1_funct_2(F_600,D_602,B_603)
      | ~ v1_funct_1(F_600)
      | ~ m1_subset_1(E_604,k1_zfmisc_1(k2_zfmisc_1(C_601,B_603)))
      | ~ v1_funct_2(E_604,C_601,B_603)
      | ~ v1_funct_1(E_604)
      | ~ m1_subset_1(D_602,k1_zfmisc_1(A_599))
      | v1_xboole_0(D_602)
      | ~ m1_subset_1(C_601,k1_zfmisc_1(A_599))
      | v1_xboole_0(C_601)
      | v1_xboole_0(B_603)
      | v1_xboole_0(A_599) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_2619,plain,(
    ! [A_599,C_601,E_604] :
      ( v1_funct_1(k1_tmap_1(A_599,'#skF_4',C_601,'#skF_6',E_604,'#skF_8'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_604,k1_zfmisc_1(k2_zfmisc_1(C_601,'#skF_4')))
      | ~ v1_funct_2(E_604,C_601,'#skF_4')
      | ~ v1_funct_1(E_604)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_599))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_601,k1_zfmisc_1(A_599))
      | v1_xboole_0(C_601)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_599) ) ),
    inference(resolution,[status(thm)],[c_42,c_2615])).

tff(c_2626,plain,(
    ! [A_599,C_601,E_604] :
      ( v1_funct_1(k1_tmap_1(A_599,'#skF_4',C_601,'#skF_6',E_604,'#skF_8'))
      | ~ m1_subset_1(E_604,k1_zfmisc_1(k2_zfmisc_1(C_601,'#skF_4')))
      | ~ v1_funct_2(E_604,C_601,'#skF_4')
      | ~ v1_funct_1(E_604)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_599))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_601,k1_zfmisc_1(A_599))
      | v1_xboole_0(C_601)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_599) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_2619])).

tff(c_2683,plain,(
    ! [A_611,C_612,E_613] :
      ( v1_funct_1(k1_tmap_1(A_611,'#skF_4',C_612,'#skF_6',E_613,'#skF_8'))
      | ~ m1_subset_1(E_613,k1_zfmisc_1(k2_zfmisc_1(C_612,'#skF_4')))
      | ~ v1_funct_2(E_613,C_612,'#skF_4')
      | ~ v1_funct_1(E_613)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_611))
      | ~ m1_subset_1(C_612,k1_zfmisc_1(A_611))
      | v1_xboole_0(C_612)
      | v1_xboole_0(A_611) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_2626])).

tff(c_2685,plain,(
    ! [A_611] :
      ( v1_funct_1(k1_tmap_1(A_611,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_611))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_611))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_611) ) ),
    inference(resolution,[status(thm)],[c_48,c_2683])).

tff(c_2690,plain,(
    ! [A_611] :
      ( v1_funct_1(k1_tmap_1(A_611,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_611))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_611))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_611) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_2685])).

tff(c_2732,plain,(
    ! [A_630] :
      ( v1_funct_1(k1_tmap_1(A_630,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_630))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_630))
      | v1_xboole_0(A_630) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2690])).

tff(c_2735,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_2732])).

tff(c_2738,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2735])).

tff(c_2739,plain,(
    v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_2738])).

tff(c_2554,plain,(
    ! [A_588,B_589,C_590,D_591] :
      ( k2_partfun1(A_588,B_589,C_590,D_591) = k7_relat_1(C_590,D_591)
      | ~ m1_subset_1(C_590,k1_zfmisc_1(k2_zfmisc_1(A_588,B_589)))
      | ~ v1_funct_1(C_590) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2556,plain,(
    ! [D_591] :
      ( k2_partfun1('#skF_5','#skF_4','#skF_7',D_591) = k7_relat_1('#skF_7',D_591)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_48,c_2554])).

tff(c_2561,plain,(
    ! [D_591] : k2_partfun1('#skF_5','#skF_4','#skF_7',D_591) = k7_relat_1('#skF_7',D_591) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2556])).

tff(c_2558,plain,(
    ! [D_591] :
      ( k2_partfun1('#skF_6','#skF_4','#skF_8',D_591) = k7_relat_1('#skF_8',D_591)
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_42,c_2554])).

tff(c_2564,plain,(
    ! [D_591] : k2_partfun1('#skF_6','#skF_4','#skF_8',D_591) = k7_relat_1('#skF_8',D_591) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2558])).

tff(c_36,plain,(
    ! [A_152,C_154,D_155,F_157,E_156,B_153] :
      ( v1_funct_2(k1_tmap_1(A_152,B_153,C_154,D_155,E_156,F_157),k4_subset_1(A_152,C_154,D_155),B_153)
      | ~ m1_subset_1(F_157,k1_zfmisc_1(k2_zfmisc_1(D_155,B_153)))
      | ~ v1_funct_2(F_157,D_155,B_153)
      | ~ v1_funct_1(F_157)
      | ~ m1_subset_1(E_156,k1_zfmisc_1(k2_zfmisc_1(C_154,B_153)))
      | ~ v1_funct_2(E_156,C_154,B_153)
      | ~ v1_funct_1(E_156)
      | ~ m1_subset_1(D_155,k1_zfmisc_1(A_152))
      | v1_xboole_0(D_155)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(A_152))
      | v1_xboole_0(C_154)
      | v1_xboole_0(B_153)
      | v1_xboole_0(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_34,plain,(
    ! [A_152,C_154,D_155,F_157,E_156,B_153] :
      ( m1_subset_1(k1_tmap_1(A_152,B_153,C_154,D_155,E_156,F_157),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_152,C_154,D_155),B_153)))
      | ~ m1_subset_1(F_157,k1_zfmisc_1(k2_zfmisc_1(D_155,B_153)))
      | ~ v1_funct_2(F_157,D_155,B_153)
      | ~ v1_funct_1(F_157)
      | ~ m1_subset_1(E_156,k1_zfmisc_1(k2_zfmisc_1(C_154,B_153)))
      | ~ v1_funct_2(E_156,C_154,B_153)
      | ~ v1_funct_1(E_156)
      | ~ m1_subset_1(D_155,k1_zfmisc_1(A_152))
      | v1_xboole_0(D_155)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(A_152))
      | v1_xboole_0(C_154)
      | v1_xboole_0(B_153)
      | v1_xboole_0(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_2966,plain,(
    ! [B_670,F_669,E_672,A_668,C_671,D_673] :
      ( k2_partfun1(k4_subset_1(A_668,C_671,D_673),B_670,k1_tmap_1(A_668,B_670,C_671,D_673,E_672,F_669),C_671) = E_672
      | ~ m1_subset_1(k1_tmap_1(A_668,B_670,C_671,D_673,E_672,F_669),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_668,C_671,D_673),B_670)))
      | ~ v1_funct_2(k1_tmap_1(A_668,B_670,C_671,D_673,E_672,F_669),k4_subset_1(A_668,C_671,D_673),B_670)
      | ~ v1_funct_1(k1_tmap_1(A_668,B_670,C_671,D_673,E_672,F_669))
      | k2_partfun1(D_673,B_670,F_669,k9_subset_1(A_668,C_671,D_673)) != k2_partfun1(C_671,B_670,E_672,k9_subset_1(A_668,C_671,D_673))
      | ~ m1_subset_1(F_669,k1_zfmisc_1(k2_zfmisc_1(D_673,B_670)))
      | ~ v1_funct_2(F_669,D_673,B_670)
      | ~ v1_funct_1(F_669)
      | ~ m1_subset_1(E_672,k1_zfmisc_1(k2_zfmisc_1(C_671,B_670)))
      | ~ v1_funct_2(E_672,C_671,B_670)
      | ~ v1_funct_1(E_672)
      | ~ m1_subset_1(D_673,k1_zfmisc_1(A_668))
      | v1_xboole_0(D_673)
      | ~ m1_subset_1(C_671,k1_zfmisc_1(A_668))
      | v1_xboole_0(C_671)
      | v1_xboole_0(B_670)
      | v1_xboole_0(A_668) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_3242,plain,(
    ! [A_737,C_739,F_738,B_741,D_740,E_742] :
      ( k2_partfun1(k4_subset_1(A_737,C_739,D_740),B_741,k1_tmap_1(A_737,B_741,C_739,D_740,E_742,F_738),C_739) = E_742
      | ~ v1_funct_2(k1_tmap_1(A_737,B_741,C_739,D_740,E_742,F_738),k4_subset_1(A_737,C_739,D_740),B_741)
      | ~ v1_funct_1(k1_tmap_1(A_737,B_741,C_739,D_740,E_742,F_738))
      | k2_partfun1(D_740,B_741,F_738,k9_subset_1(A_737,C_739,D_740)) != k2_partfun1(C_739,B_741,E_742,k9_subset_1(A_737,C_739,D_740))
      | ~ m1_subset_1(F_738,k1_zfmisc_1(k2_zfmisc_1(D_740,B_741)))
      | ~ v1_funct_2(F_738,D_740,B_741)
      | ~ v1_funct_1(F_738)
      | ~ m1_subset_1(E_742,k1_zfmisc_1(k2_zfmisc_1(C_739,B_741)))
      | ~ v1_funct_2(E_742,C_739,B_741)
      | ~ v1_funct_1(E_742)
      | ~ m1_subset_1(D_740,k1_zfmisc_1(A_737))
      | v1_xboole_0(D_740)
      | ~ m1_subset_1(C_739,k1_zfmisc_1(A_737))
      | v1_xboole_0(C_739)
      | v1_xboole_0(B_741)
      | v1_xboole_0(A_737) ) ),
    inference(resolution,[status(thm)],[c_34,c_2966])).

tff(c_3425,plain,(
    ! [E_771,F_767,C_768,B_770,A_766,D_769] :
      ( k2_partfun1(k4_subset_1(A_766,C_768,D_769),B_770,k1_tmap_1(A_766,B_770,C_768,D_769,E_771,F_767),C_768) = E_771
      | ~ v1_funct_1(k1_tmap_1(A_766,B_770,C_768,D_769,E_771,F_767))
      | k2_partfun1(D_769,B_770,F_767,k9_subset_1(A_766,C_768,D_769)) != k2_partfun1(C_768,B_770,E_771,k9_subset_1(A_766,C_768,D_769))
      | ~ m1_subset_1(F_767,k1_zfmisc_1(k2_zfmisc_1(D_769,B_770)))
      | ~ v1_funct_2(F_767,D_769,B_770)
      | ~ v1_funct_1(F_767)
      | ~ m1_subset_1(E_771,k1_zfmisc_1(k2_zfmisc_1(C_768,B_770)))
      | ~ v1_funct_2(E_771,C_768,B_770)
      | ~ v1_funct_1(E_771)
      | ~ m1_subset_1(D_769,k1_zfmisc_1(A_766))
      | v1_xboole_0(D_769)
      | ~ m1_subset_1(C_768,k1_zfmisc_1(A_766))
      | v1_xboole_0(C_768)
      | v1_xboole_0(B_770)
      | v1_xboole_0(A_766) ) ),
    inference(resolution,[status(thm)],[c_36,c_3242])).

tff(c_3431,plain,(
    ! [A_766,C_768,E_771] :
      ( k2_partfun1(k4_subset_1(A_766,C_768,'#skF_6'),'#skF_4',k1_tmap_1(A_766,'#skF_4',C_768,'#skF_6',E_771,'#skF_8'),C_768) = E_771
      | ~ v1_funct_1(k1_tmap_1(A_766,'#skF_4',C_768,'#skF_6',E_771,'#skF_8'))
      | k2_partfun1(C_768,'#skF_4',E_771,k9_subset_1(A_766,C_768,'#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1(A_766,C_768,'#skF_6'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_771,k1_zfmisc_1(k2_zfmisc_1(C_768,'#skF_4')))
      | ~ v1_funct_2(E_771,C_768,'#skF_4')
      | ~ v1_funct_1(E_771)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_766))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_768,k1_zfmisc_1(A_766))
      | v1_xboole_0(C_768)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_766) ) ),
    inference(resolution,[status(thm)],[c_42,c_3425])).

tff(c_3439,plain,(
    ! [A_766,C_768,E_771] :
      ( k2_partfun1(k4_subset_1(A_766,C_768,'#skF_6'),'#skF_4',k1_tmap_1(A_766,'#skF_4',C_768,'#skF_6',E_771,'#skF_8'),C_768) = E_771
      | ~ v1_funct_1(k1_tmap_1(A_766,'#skF_4',C_768,'#skF_6',E_771,'#skF_8'))
      | k2_partfun1(C_768,'#skF_4',E_771,k9_subset_1(A_766,C_768,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_766,C_768,'#skF_6'))
      | ~ m1_subset_1(E_771,k1_zfmisc_1(k2_zfmisc_1(C_768,'#skF_4')))
      | ~ v1_funct_2(E_771,C_768,'#skF_4')
      | ~ v1_funct_1(E_771)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_766))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_768,k1_zfmisc_1(A_766))
      | v1_xboole_0(C_768)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_766) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_2564,c_3431])).

tff(c_3488,plain,(
    ! [A_783,C_784,E_785] :
      ( k2_partfun1(k4_subset_1(A_783,C_784,'#skF_6'),'#skF_4',k1_tmap_1(A_783,'#skF_4',C_784,'#skF_6',E_785,'#skF_8'),C_784) = E_785
      | ~ v1_funct_1(k1_tmap_1(A_783,'#skF_4',C_784,'#skF_6',E_785,'#skF_8'))
      | k2_partfun1(C_784,'#skF_4',E_785,k9_subset_1(A_783,C_784,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_783,C_784,'#skF_6'))
      | ~ m1_subset_1(E_785,k1_zfmisc_1(k2_zfmisc_1(C_784,'#skF_4')))
      | ~ v1_funct_2(E_785,C_784,'#skF_4')
      | ~ v1_funct_1(E_785)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_783))
      | ~ m1_subset_1(C_784,k1_zfmisc_1(A_783))
      | v1_xboole_0(C_784)
      | v1_xboole_0(A_783) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_3439])).

tff(c_3493,plain,(
    ! [A_783] :
      ( k2_partfun1(k4_subset_1(A_783,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_783,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_783,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1(A_783,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_783,'#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_783))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_783))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_783) ) ),
    inference(resolution,[status(thm)],[c_48,c_3488])).

tff(c_3501,plain,(
    ! [A_783] :
      ( k2_partfun1(k4_subset_1(A_783,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_783,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_783,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_783,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_783,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_783))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_783))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_783) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_2561,c_3493])).

tff(c_3507,plain,(
    ! [A_786] :
      ( k2_partfun1(k4_subset_1(A_786,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_786,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_786,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_786,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_786,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_786))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_786))
      | v1_xboole_0(A_786) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_3501])).

tff(c_1041,plain,(
    ! [A_331,B_332] :
      ( k3_xboole_0(A_331,B_332) = k1_xboole_0
      | ~ r1_subset_1(A_331,B_332)
      | v1_xboole_0(B_332)
      | v1_xboole_0(A_331) ) ),
    inference(resolution,[status(thm)],[c_822,c_680])).

tff(c_1044,plain,
    ( k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0
    | v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_1041])).

tff(c_1047,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_58,c_1044])).

tff(c_991,plain,(
    ! [A_324,B_325,C_326] :
      ( k9_subset_1(A_324,B_325,C_326) = k3_xboole_0(B_325,C_326)
      | ~ m1_subset_1(C_326,k1_zfmisc_1(A_324)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1003,plain,(
    ! [B_325] : k9_subset_1('#skF_3',B_325,'#skF_6') = k3_xboole_0(B_325,'#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_991])).

tff(c_1297,plain,(
    ! [E_356,C_353,D_354,B_355,F_352,A_351] :
      ( v1_funct_1(k1_tmap_1(A_351,B_355,C_353,D_354,E_356,F_352))
      | ~ m1_subset_1(F_352,k1_zfmisc_1(k2_zfmisc_1(D_354,B_355)))
      | ~ v1_funct_2(F_352,D_354,B_355)
      | ~ v1_funct_1(F_352)
      | ~ m1_subset_1(E_356,k1_zfmisc_1(k2_zfmisc_1(C_353,B_355)))
      | ~ v1_funct_2(E_356,C_353,B_355)
      | ~ v1_funct_1(E_356)
      | ~ m1_subset_1(D_354,k1_zfmisc_1(A_351))
      | v1_xboole_0(D_354)
      | ~ m1_subset_1(C_353,k1_zfmisc_1(A_351))
      | v1_xboole_0(C_353)
      | v1_xboole_0(B_355)
      | v1_xboole_0(A_351) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_1301,plain,(
    ! [A_351,C_353,E_356] :
      ( v1_funct_1(k1_tmap_1(A_351,'#skF_4',C_353,'#skF_6',E_356,'#skF_8'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_356,k1_zfmisc_1(k2_zfmisc_1(C_353,'#skF_4')))
      | ~ v1_funct_2(E_356,C_353,'#skF_4')
      | ~ v1_funct_1(E_356)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_351))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_353,k1_zfmisc_1(A_351))
      | v1_xboole_0(C_353)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_351) ) ),
    inference(resolution,[status(thm)],[c_42,c_1297])).

tff(c_1308,plain,(
    ! [A_351,C_353,E_356] :
      ( v1_funct_1(k1_tmap_1(A_351,'#skF_4',C_353,'#skF_6',E_356,'#skF_8'))
      | ~ m1_subset_1(E_356,k1_zfmisc_1(k2_zfmisc_1(C_353,'#skF_4')))
      | ~ v1_funct_2(E_356,C_353,'#skF_4')
      | ~ v1_funct_1(E_356)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_351))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_353,k1_zfmisc_1(A_351))
      | v1_xboole_0(C_353)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_351) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_1301])).

tff(c_1412,plain,(
    ! [A_382,C_383,E_384] :
      ( v1_funct_1(k1_tmap_1(A_382,'#skF_4',C_383,'#skF_6',E_384,'#skF_8'))
      | ~ m1_subset_1(E_384,k1_zfmisc_1(k2_zfmisc_1(C_383,'#skF_4')))
      | ~ v1_funct_2(E_384,C_383,'#skF_4')
      | ~ v1_funct_1(E_384)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_382))
      | ~ m1_subset_1(C_383,k1_zfmisc_1(A_382))
      | v1_xboole_0(C_383)
      | v1_xboole_0(A_382) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_1308])).

tff(c_1414,plain,(
    ! [A_382] :
      ( v1_funct_1(k1_tmap_1(A_382,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_382))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_382))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_382) ) ),
    inference(resolution,[status(thm)],[c_48,c_1412])).

tff(c_1419,plain,(
    ! [A_382] :
      ( v1_funct_1(k1_tmap_1(A_382,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_382))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_382))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_382) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1414])).

tff(c_1450,plain,(
    ! [A_392] :
      ( v1_funct_1(k1_tmap_1(A_392,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_392))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_392))
      | v1_xboole_0(A_392) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1419])).

tff(c_1453,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_1450])).

tff(c_1456,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1453])).

tff(c_1457,plain,(
    v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1456])).

tff(c_1254,plain,(
    ! [A_345,B_346,C_347,D_348] :
      ( k2_partfun1(A_345,B_346,C_347,D_348) = k7_relat_1(C_347,D_348)
      | ~ m1_subset_1(C_347,k1_zfmisc_1(k2_zfmisc_1(A_345,B_346)))
      | ~ v1_funct_1(C_347) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1256,plain,(
    ! [D_348] :
      ( k2_partfun1('#skF_5','#skF_4','#skF_7',D_348) = k7_relat_1('#skF_7',D_348)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_48,c_1254])).

tff(c_1261,plain,(
    ! [D_348] : k2_partfun1('#skF_5','#skF_4','#skF_7',D_348) = k7_relat_1('#skF_7',D_348) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1256])).

tff(c_1258,plain,(
    ! [D_348] :
      ( k2_partfun1('#skF_6','#skF_4','#skF_8',D_348) = k7_relat_1('#skF_8',D_348)
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_42,c_1254])).

tff(c_1264,plain,(
    ! [D_348] : k2_partfun1('#skF_6','#skF_4','#skF_8',D_348) = k7_relat_1('#skF_8',D_348) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1258])).

tff(c_1573,plain,(
    ! [C_412,E_413,A_409,B_411,F_410,D_414] :
      ( k2_partfun1(k4_subset_1(A_409,C_412,D_414),B_411,k1_tmap_1(A_409,B_411,C_412,D_414,E_413,F_410),D_414) = F_410
      | ~ m1_subset_1(k1_tmap_1(A_409,B_411,C_412,D_414,E_413,F_410),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_409,C_412,D_414),B_411)))
      | ~ v1_funct_2(k1_tmap_1(A_409,B_411,C_412,D_414,E_413,F_410),k4_subset_1(A_409,C_412,D_414),B_411)
      | ~ v1_funct_1(k1_tmap_1(A_409,B_411,C_412,D_414,E_413,F_410))
      | k2_partfun1(D_414,B_411,F_410,k9_subset_1(A_409,C_412,D_414)) != k2_partfun1(C_412,B_411,E_413,k9_subset_1(A_409,C_412,D_414))
      | ~ m1_subset_1(F_410,k1_zfmisc_1(k2_zfmisc_1(D_414,B_411)))
      | ~ v1_funct_2(F_410,D_414,B_411)
      | ~ v1_funct_1(F_410)
      | ~ m1_subset_1(E_413,k1_zfmisc_1(k2_zfmisc_1(C_412,B_411)))
      | ~ v1_funct_2(E_413,C_412,B_411)
      | ~ v1_funct_1(E_413)
      | ~ m1_subset_1(D_414,k1_zfmisc_1(A_409))
      | v1_xboole_0(D_414)
      | ~ m1_subset_1(C_412,k1_zfmisc_1(A_409))
      | v1_xboole_0(C_412)
      | v1_xboole_0(B_411)
      | v1_xboole_0(A_409) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_1987,plain,(
    ! [A_510,B_514,D_513,E_515,F_511,C_512] :
      ( k2_partfun1(k4_subset_1(A_510,C_512,D_513),B_514,k1_tmap_1(A_510,B_514,C_512,D_513,E_515,F_511),D_513) = F_511
      | ~ v1_funct_2(k1_tmap_1(A_510,B_514,C_512,D_513,E_515,F_511),k4_subset_1(A_510,C_512,D_513),B_514)
      | ~ v1_funct_1(k1_tmap_1(A_510,B_514,C_512,D_513,E_515,F_511))
      | k2_partfun1(D_513,B_514,F_511,k9_subset_1(A_510,C_512,D_513)) != k2_partfun1(C_512,B_514,E_515,k9_subset_1(A_510,C_512,D_513))
      | ~ m1_subset_1(F_511,k1_zfmisc_1(k2_zfmisc_1(D_513,B_514)))
      | ~ v1_funct_2(F_511,D_513,B_514)
      | ~ v1_funct_1(F_511)
      | ~ m1_subset_1(E_515,k1_zfmisc_1(k2_zfmisc_1(C_512,B_514)))
      | ~ v1_funct_2(E_515,C_512,B_514)
      | ~ v1_funct_1(E_515)
      | ~ m1_subset_1(D_513,k1_zfmisc_1(A_510))
      | v1_xboole_0(D_513)
      | ~ m1_subset_1(C_512,k1_zfmisc_1(A_510))
      | v1_xboole_0(C_512)
      | v1_xboole_0(B_514)
      | v1_xboole_0(A_510) ) ),
    inference(resolution,[status(thm)],[c_34,c_1573])).

tff(c_2102,plain,(
    ! [E_539,F_535,C_536,D_537,A_534,B_538] :
      ( k2_partfun1(k4_subset_1(A_534,C_536,D_537),B_538,k1_tmap_1(A_534,B_538,C_536,D_537,E_539,F_535),D_537) = F_535
      | ~ v1_funct_1(k1_tmap_1(A_534,B_538,C_536,D_537,E_539,F_535))
      | k2_partfun1(D_537,B_538,F_535,k9_subset_1(A_534,C_536,D_537)) != k2_partfun1(C_536,B_538,E_539,k9_subset_1(A_534,C_536,D_537))
      | ~ m1_subset_1(F_535,k1_zfmisc_1(k2_zfmisc_1(D_537,B_538)))
      | ~ v1_funct_2(F_535,D_537,B_538)
      | ~ v1_funct_1(F_535)
      | ~ m1_subset_1(E_539,k1_zfmisc_1(k2_zfmisc_1(C_536,B_538)))
      | ~ v1_funct_2(E_539,C_536,B_538)
      | ~ v1_funct_1(E_539)
      | ~ m1_subset_1(D_537,k1_zfmisc_1(A_534))
      | v1_xboole_0(D_537)
      | ~ m1_subset_1(C_536,k1_zfmisc_1(A_534))
      | v1_xboole_0(C_536)
      | v1_xboole_0(B_538)
      | v1_xboole_0(A_534) ) ),
    inference(resolution,[status(thm)],[c_36,c_1987])).

tff(c_2108,plain,(
    ! [A_534,C_536,E_539] :
      ( k2_partfun1(k4_subset_1(A_534,C_536,'#skF_6'),'#skF_4',k1_tmap_1(A_534,'#skF_4',C_536,'#skF_6',E_539,'#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_534,'#skF_4',C_536,'#skF_6',E_539,'#skF_8'))
      | k2_partfun1(C_536,'#skF_4',E_539,k9_subset_1(A_534,C_536,'#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1(A_534,C_536,'#skF_6'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_539,k1_zfmisc_1(k2_zfmisc_1(C_536,'#skF_4')))
      | ~ v1_funct_2(E_539,C_536,'#skF_4')
      | ~ v1_funct_1(E_539)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_534))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_536,k1_zfmisc_1(A_534))
      | v1_xboole_0(C_536)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_534) ) ),
    inference(resolution,[status(thm)],[c_42,c_2102])).

tff(c_2116,plain,(
    ! [A_534,C_536,E_539] :
      ( k2_partfun1(k4_subset_1(A_534,C_536,'#skF_6'),'#skF_4',k1_tmap_1(A_534,'#skF_4',C_536,'#skF_6',E_539,'#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_534,'#skF_4',C_536,'#skF_6',E_539,'#skF_8'))
      | k2_partfun1(C_536,'#skF_4',E_539,k9_subset_1(A_534,C_536,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_534,C_536,'#skF_6'))
      | ~ m1_subset_1(E_539,k1_zfmisc_1(k2_zfmisc_1(C_536,'#skF_4')))
      | ~ v1_funct_2(E_539,C_536,'#skF_4')
      | ~ v1_funct_1(E_539)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_534))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_536,k1_zfmisc_1(A_534))
      | v1_xboole_0(C_536)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_534) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_1264,c_2108])).

tff(c_2174,plain,(
    ! [A_554,C_555,E_556] :
      ( k2_partfun1(k4_subset_1(A_554,C_555,'#skF_6'),'#skF_4',k1_tmap_1(A_554,'#skF_4',C_555,'#skF_6',E_556,'#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_554,'#skF_4',C_555,'#skF_6',E_556,'#skF_8'))
      | k2_partfun1(C_555,'#skF_4',E_556,k9_subset_1(A_554,C_555,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_554,C_555,'#skF_6'))
      | ~ m1_subset_1(E_556,k1_zfmisc_1(k2_zfmisc_1(C_555,'#skF_4')))
      | ~ v1_funct_2(E_556,C_555,'#skF_4')
      | ~ v1_funct_1(E_556)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_554))
      | ~ m1_subset_1(C_555,k1_zfmisc_1(A_554))
      | v1_xboole_0(C_555)
      | v1_xboole_0(A_554) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_2116])).

tff(c_2179,plain,(
    ! [A_554] :
      ( k2_partfun1(k4_subset_1(A_554,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_554,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_554,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1(A_554,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_554,'#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_554))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_554))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_554) ) ),
    inference(resolution,[status(thm)],[c_48,c_2174])).

tff(c_2187,plain,(
    ! [A_554] :
      ( k2_partfun1(k4_subset_1(A_554,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_554,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_554,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_554,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_554,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_554))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_554))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_554) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1261,c_2179])).

tff(c_2193,plain,(
    ! [A_557] :
      ( k2_partfun1(k4_subset_1(A_557,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_557,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_557,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_557,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_557,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_557))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_557))
      | v1_xboole_0(A_557) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2187])).

tff(c_88,plain,(
    ! [C_224,A_225,B_226] :
      ( v1_relat_1(C_224)
      | ~ m1_subset_1(C_224,k1_zfmisc_1(k2_zfmisc_1(A_225,B_226))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_96,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_42,c_88])).

tff(c_104,plain,(
    k7_relat_1('#skF_8',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_96,c_18])).

tff(c_236,plain,(
    ! [A_243,B_244] :
      ( r1_xboole_0(A_243,B_244)
      | ~ r1_subset_1(A_243,B_244)
      | v1_xboole_0(B_244)
      | v1_xboole_0(A_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_81,plain,(
    ! [A_222,B_223] :
      ( r2_hidden('#skF_1'(A_222,B_223),A_222)
      | r1_xboole_0(A_222,B_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_149,plain,(
    ! [A_233,B_234,B_235] :
      ( ~ r1_xboole_0(A_233,B_234)
      | r1_xboole_0(k3_xboole_0(A_233,B_234),B_235) ) ),
    inference(resolution,[status(thm)],[c_81,c_10])).

tff(c_157,plain,(
    ! [A_233,B_234] :
      ( k3_xboole_0(A_233,B_234) = k1_xboole_0
      | ~ r1_xboole_0(A_233,B_234) ) ),
    inference(resolution,[status(thm)],[c_149,c_14])).

tff(c_483,plain,(
    ! [A_269,B_270] :
      ( k3_xboole_0(A_269,B_270) = k1_xboole_0
      | ~ r1_subset_1(A_269,B_270)
      | v1_xboole_0(B_270)
      | v1_xboole_0(A_269) ) ),
    inference(resolution,[status(thm)],[c_236,c_157])).

tff(c_486,plain,
    ( k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0
    | v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_483])).

tff(c_489,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_58,c_486])).

tff(c_95,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_48,c_88])).

tff(c_100,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_95,c_18])).

tff(c_417,plain,(
    ! [A_259,B_260,C_261,D_262] :
      ( k2_partfun1(A_259,B_260,C_261,D_262) = k7_relat_1(C_261,D_262)
      | ~ m1_subset_1(C_261,k1_zfmisc_1(k2_zfmisc_1(A_259,B_260)))
      | ~ v1_funct_1(C_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_419,plain,(
    ! [D_262] :
      ( k2_partfun1('#skF_5','#skF_4','#skF_7',D_262) = k7_relat_1('#skF_7',D_262)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_48,c_417])).

tff(c_424,plain,(
    ! [D_262] : k2_partfun1('#skF_5','#skF_4','#skF_7',D_262) = k7_relat_1('#skF_7',D_262) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_419])).

tff(c_421,plain,(
    ! [D_262] :
      ( k2_partfun1('#skF_6','#skF_4','#skF_8',D_262) = k7_relat_1('#skF_8',D_262)
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_42,c_417])).

tff(c_427,plain,(
    ! [D_262] : k2_partfun1('#skF_6','#skF_4','#skF_8',D_262) = k7_relat_1('#skF_8',D_262) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_421])).

tff(c_404,plain,(
    ! [A_256,B_257,C_258] :
      ( k9_subset_1(A_256,B_257,C_258) = k3_xboole_0(B_257,C_258)
      | ~ m1_subset_1(C_258,k1_zfmisc_1(A_256)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_416,plain,(
    ! [B_257] : k9_subset_1('#skF_3',B_257,'#skF_6') = k3_xboole_0(B_257,'#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_404])).

tff(c_40,plain,
    ( k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') != '#skF_8'
    | k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') != '#skF_7'
    | k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_87,plain,(
    k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_437,plain,(
    k2_partfun1('#skF_5','#skF_4','#skF_7',k3_xboole_0('#skF_5','#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_416,c_416,c_87])).

tff(c_647,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_489,c_100,c_489,c_424,c_427,c_437])).

tff(c_648,plain,
    ( k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') != '#skF_7'
    | k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_944,plain,(
    k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_648])).

tff(c_2204,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2193,c_944])).

tff(c_2218,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_666,c_1047,c_662,c_1047,c_1003,c_1003,c_1457,c_2204])).

tff(c_2220,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_2218])).

tff(c_2221,plain,(
    k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_648])).

tff(c_3516,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3507,c_2221])).

tff(c_3527,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_666,c_2325,c_662,c_2325,c_2281,c_2281,c_2739,c_3516])).

tff(c_3529,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_3527])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:42:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.38/2.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.63/2.29  
% 6.63/2.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.63/2.29  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2 > #skF_1
% 6.63/2.29  
% 6.63/2.29  %Foreground sorts:
% 6.63/2.29  
% 6.63/2.29  
% 6.63/2.29  %Background operators:
% 6.63/2.29  
% 6.63/2.29  
% 6.63/2.29  %Foreground operators:
% 6.63/2.29  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 6.63/2.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.63/2.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.63/2.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.63/2.29  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.63/2.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.63/2.29  tff('#skF_7', type, '#skF_7': $i).
% 6.63/2.29  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 6.63/2.29  tff('#skF_5', type, '#skF_5': $i).
% 6.63/2.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.63/2.29  tff('#skF_6', type, '#skF_6': $i).
% 6.63/2.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.63/2.29  tff('#skF_3', type, '#skF_3': $i).
% 6.63/2.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.63/2.29  tff('#skF_8', type, '#skF_8': $i).
% 6.63/2.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.63/2.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.63/2.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.63/2.29  tff('#skF_4', type, '#skF_4': $i).
% 6.63/2.29  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.63/2.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.63/2.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.63/2.29  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 6.63/2.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.63/2.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.63/2.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.63/2.29  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 6.63/2.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.63/2.29  
% 6.63/2.32  tff(f_221, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 6.63/2.32  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.63/2.32  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_relat_1)).
% 6.63/2.32  tff(f_87, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 6.63/2.32  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.63/2.32  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.63/2.32  tff(f_69, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 6.63/2.32  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 6.63/2.32  tff(f_179, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 6.63/2.32  tff(f_97, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 6.63/2.32  tff(f_145, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 6.63/2.32  tff(c_66, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_221])).
% 6.63/2.32  tff(c_60, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_221])).
% 6.63/2.32  tff(c_56, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_221])).
% 6.63/2.32  tff(c_42, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_221])).
% 6.63/2.32  tff(c_650, plain, (![C_292, A_293, B_294]: (v1_relat_1(C_292) | ~m1_subset_1(C_292, k1_zfmisc_1(k2_zfmisc_1(A_293, B_294))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.63/2.32  tff(c_658, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_42, c_650])).
% 6.63/2.32  tff(c_18, plain, (![A_15]: (k7_relat_1(A_15, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.63/2.32  tff(c_666, plain, (k7_relat_1('#skF_8', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_658, c_18])).
% 6.63/2.32  tff(c_62, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_221])).
% 6.63/2.32  tff(c_58, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_221])).
% 6.63/2.32  tff(c_54, plain, (r1_subset_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_221])).
% 6.63/2.32  tff(c_822, plain, (![A_311, B_312]: (r1_xboole_0(A_311, B_312) | ~r1_subset_1(A_311, B_312) | v1_xboole_0(B_312) | v1_xboole_0(A_311))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.63/2.32  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.63/2.32  tff(c_75, plain, (![A_219, B_220, C_221]: (~r1_xboole_0(A_219, B_220) | ~r2_hidden(C_221, k3_xboole_0(A_219, B_220)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.63/2.32  tff(c_675, plain, (![A_295, B_296, A_297]: (~r1_xboole_0(A_295, B_296) | r1_xboole_0(A_297, k3_xboole_0(A_295, B_296)))), inference(resolution, [status(thm)], [c_4, c_75])).
% 6.63/2.32  tff(c_14, plain, (![A_11]: (~r1_xboole_0(A_11, A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.63/2.32  tff(c_680, plain, (![A_295, B_296]: (k3_xboole_0(A_295, B_296)=k1_xboole_0 | ~r1_xboole_0(A_295, B_296))), inference(resolution, [status(thm)], [c_675, c_14])).
% 6.63/2.32  tff(c_2319, plain, (![A_569, B_570]: (k3_xboole_0(A_569, B_570)=k1_xboole_0 | ~r1_subset_1(A_569, B_570) | v1_xboole_0(B_570) | v1_xboole_0(A_569))), inference(resolution, [status(thm)], [c_822, c_680])).
% 6.63/2.32  tff(c_2322, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0 | v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_54, c_2319])).
% 6.63/2.32  tff(c_2325, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_62, c_58, c_2322])).
% 6.63/2.32  tff(c_48, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_221])).
% 6.63/2.32  tff(c_657, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_48, c_650])).
% 6.63/2.32  tff(c_662, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_657, c_18])).
% 6.63/2.32  tff(c_2269, plain, (![A_562, B_563, C_564]: (k9_subset_1(A_562, B_563, C_564)=k3_xboole_0(B_563, C_564) | ~m1_subset_1(C_564, k1_zfmisc_1(A_562)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.63/2.32  tff(c_2281, plain, (![B_563]: (k9_subset_1('#skF_3', B_563, '#skF_6')=k3_xboole_0(B_563, '#skF_6'))), inference(resolution, [status(thm)], [c_56, c_2269])).
% 6.63/2.32  tff(c_52, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_221])).
% 6.63/2.32  tff(c_50, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_221])).
% 6.63/2.32  tff(c_64, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_221])).
% 6.63/2.32  tff(c_46, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_221])).
% 6.63/2.32  tff(c_44, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_221])).
% 6.63/2.32  tff(c_2615, plain, (![C_601, A_599, E_604, F_600, B_603, D_602]: (v1_funct_1(k1_tmap_1(A_599, B_603, C_601, D_602, E_604, F_600)) | ~m1_subset_1(F_600, k1_zfmisc_1(k2_zfmisc_1(D_602, B_603))) | ~v1_funct_2(F_600, D_602, B_603) | ~v1_funct_1(F_600) | ~m1_subset_1(E_604, k1_zfmisc_1(k2_zfmisc_1(C_601, B_603))) | ~v1_funct_2(E_604, C_601, B_603) | ~v1_funct_1(E_604) | ~m1_subset_1(D_602, k1_zfmisc_1(A_599)) | v1_xboole_0(D_602) | ~m1_subset_1(C_601, k1_zfmisc_1(A_599)) | v1_xboole_0(C_601) | v1_xboole_0(B_603) | v1_xboole_0(A_599))), inference(cnfTransformation, [status(thm)], [f_179])).
% 6.63/2.32  tff(c_2619, plain, (![A_599, C_601, E_604]: (v1_funct_1(k1_tmap_1(A_599, '#skF_4', C_601, '#skF_6', E_604, '#skF_8')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_604, k1_zfmisc_1(k2_zfmisc_1(C_601, '#skF_4'))) | ~v1_funct_2(E_604, C_601, '#skF_4') | ~v1_funct_1(E_604) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_599)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_601, k1_zfmisc_1(A_599)) | v1_xboole_0(C_601) | v1_xboole_0('#skF_4') | v1_xboole_0(A_599))), inference(resolution, [status(thm)], [c_42, c_2615])).
% 6.63/2.32  tff(c_2626, plain, (![A_599, C_601, E_604]: (v1_funct_1(k1_tmap_1(A_599, '#skF_4', C_601, '#skF_6', E_604, '#skF_8')) | ~m1_subset_1(E_604, k1_zfmisc_1(k2_zfmisc_1(C_601, '#skF_4'))) | ~v1_funct_2(E_604, C_601, '#skF_4') | ~v1_funct_1(E_604) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_599)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_601, k1_zfmisc_1(A_599)) | v1_xboole_0(C_601) | v1_xboole_0('#skF_4') | v1_xboole_0(A_599))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_2619])).
% 6.63/2.32  tff(c_2683, plain, (![A_611, C_612, E_613]: (v1_funct_1(k1_tmap_1(A_611, '#skF_4', C_612, '#skF_6', E_613, '#skF_8')) | ~m1_subset_1(E_613, k1_zfmisc_1(k2_zfmisc_1(C_612, '#skF_4'))) | ~v1_funct_2(E_613, C_612, '#skF_4') | ~v1_funct_1(E_613) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_611)) | ~m1_subset_1(C_612, k1_zfmisc_1(A_611)) | v1_xboole_0(C_612) | v1_xboole_0(A_611))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_2626])).
% 6.63/2.32  tff(c_2685, plain, (![A_611]: (v1_funct_1(k1_tmap_1(A_611, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_611)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_611)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_611))), inference(resolution, [status(thm)], [c_48, c_2683])).
% 6.63/2.32  tff(c_2690, plain, (![A_611]: (v1_funct_1(k1_tmap_1(A_611, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_611)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_611)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_611))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_2685])).
% 6.63/2.32  tff(c_2732, plain, (![A_630]: (v1_funct_1(k1_tmap_1(A_630, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_630)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_630)) | v1_xboole_0(A_630))), inference(negUnitSimplification, [status(thm)], [c_62, c_2690])).
% 6.63/2.32  tff(c_2735, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_2732])).
% 6.63/2.32  tff(c_2738, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2735])).
% 6.63/2.32  tff(c_2739, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_66, c_2738])).
% 6.63/2.32  tff(c_2554, plain, (![A_588, B_589, C_590, D_591]: (k2_partfun1(A_588, B_589, C_590, D_591)=k7_relat_1(C_590, D_591) | ~m1_subset_1(C_590, k1_zfmisc_1(k2_zfmisc_1(A_588, B_589))) | ~v1_funct_1(C_590))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.63/2.32  tff(c_2556, plain, (![D_591]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_591)=k7_relat_1('#skF_7', D_591) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_48, c_2554])).
% 6.63/2.32  tff(c_2561, plain, (![D_591]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_591)=k7_relat_1('#skF_7', D_591))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2556])).
% 6.63/2.32  tff(c_2558, plain, (![D_591]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_591)=k7_relat_1('#skF_8', D_591) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_42, c_2554])).
% 6.63/2.32  tff(c_2564, plain, (![D_591]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_591)=k7_relat_1('#skF_8', D_591))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2558])).
% 6.63/2.32  tff(c_36, plain, (![A_152, C_154, D_155, F_157, E_156, B_153]: (v1_funct_2(k1_tmap_1(A_152, B_153, C_154, D_155, E_156, F_157), k4_subset_1(A_152, C_154, D_155), B_153) | ~m1_subset_1(F_157, k1_zfmisc_1(k2_zfmisc_1(D_155, B_153))) | ~v1_funct_2(F_157, D_155, B_153) | ~v1_funct_1(F_157) | ~m1_subset_1(E_156, k1_zfmisc_1(k2_zfmisc_1(C_154, B_153))) | ~v1_funct_2(E_156, C_154, B_153) | ~v1_funct_1(E_156) | ~m1_subset_1(D_155, k1_zfmisc_1(A_152)) | v1_xboole_0(D_155) | ~m1_subset_1(C_154, k1_zfmisc_1(A_152)) | v1_xboole_0(C_154) | v1_xboole_0(B_153) | v1_xboole_0(A_152))), inference(cnfTransformation, [status(thm)], [f_179])).
% 6.63/2.32  tff(c_34, plain, (![A_152, C_154, D_155, F_157, E_156, B_153]: (m1_subset_1(k1_tmap_1(A_152, B_153, C_154, D_155, E_156, F_157), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_152, C_154, D_155), B_153))) | ~m1_subset_1(F_157, k1_zfmisc_1(k2_zfmisc_1(D_155, B_153))) | ~v1_funct_2(F_157, D_155, B_153) | ~v1_funct_1(F_157) | ~m1_subset_1(E_156, k1_zfmisc_1(k2_zfmisc_1(C_154, B_153))) | ~v1_funct_2(E_156, C_154, B_153) | ~v1_funct_1(E_156) | ~m1_subset_1(D_155, k1_zfmisc_1(A_152)) | v1_xboole_0(D_155) | ~m1_subset_1(C_154, k1_zfmisc_1(A_152)) | v1_xboole_0(C_154) | v1_xboole_0(B_153) | v1_xboole_0(A_152))), inference(cnfTransformation, [status(thm)], [f_179])).
% 6.63/2.32  tff(c_2966, plain, (![B_670, F_669, E_672, A_668, C_671, D_673]: (k2_partfun1(k4_subset_1(A_668, C_671, D_673), B_670, k1_tmap_1(A_668, B_670, C_671, D_673, E_672, F_669), C_671)=E_672 | ~m1_subset_1(k1_tmap_1(A_668, B_670, C_671, D_673, E_672, F_669), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_668, C_671, D_673), B_670))) | ~v1_funct_2(k1_tmap_1(A_668, B_670, C_671, D_673, E_672, F_669), k4_subset_1(A_668, C_671, D_673), B_670) | ~v1_funct_1(k1_tmap_1(A_668, B_670, C_671, D_673, E_672, F_669)) | k2_partfun1(D_673, B_670, F_669, k9_subset_1(A_668, C_671, D_673))!=k2_partfun1(C_671, B_670, E_672, k9_subset_1(A_668, C_671, D_673)) | ~m1_subset_1(F_669, k1_zfmisc_1(k2_zfmisc_1(D_673, B_670))) | ~v1_funct_2(F_669, D_673, B_670) | ~v1_funct_1(F_669) | ~m1_subset_1(E_672, k1_zfmisc_1(k2_zfmisc_1(C_671, B_670))) | ~v1_funct_2(E_672, C_671, B_670) | ~v1_funct_1(E_672) | ~m1_subset_1(D_673, k1_zfmisc_1(A_668)) | v1_xboole_0(D_673) | ~m1_subset_1(C_671, k1_zfmisc_1(A_668)) | v1_xboole_0(C_671) | v1_xboole_0(B_670) | v1_xboole_0(A_668))), inference(cnfTransformation, [status(thm)], [f_145])).
% 6.63/2.32  tff(c_3242, plain, (![A_737, C_739, F_738, B_741, D_740, E_742]: (k2_partfun1(k4_subset_1(A_737, C_739, D_740), B_741, k1_tmap_1(A_737, B_741, C_739, D_740, E_742, F_738), C_739)=E_742 | ~v1_funct_2(k1_tmap_1(A_737, B_741, C_739, D_740, E_742, F_738), k4_subset_1(A_737, C_739, D_740), B_741) | ~v1_funct_1(k1_tmap_1(A_737, B_741, C_739, D_740, E_742, F_738)) | k2_partfun1(D_740, B_741, F_738, k9_subset_1(A_737, C_739, D_740))!=k2_partfun1(C_739, B_741, E_742, k9_subset_1(A_737, C_739, D_740)) | ~m1_subset_1(F_738, k1_zfmisc_1(k2_zfmisc_1(D_740, B_741))) | ~v1_funct_2(F_738, D_740, B_741) | ~v1_funct_1(F_738) | ~m1_subset_1(E_742, k1_zfmisc_1(k2_zfmisc_1(C_739, B_741))) | ~v1_funct_2(E_742, C_739, B_741) | ~v1_funct_1(E_742) | ~m1_subset_1(D_740, k1_zfmisc_1(A_737)) | v1_xboole_0(D_740) | ~m1_subset_1(C_739, k1_zfmisc_1(A_737)) | v1_xboole_0(C_739) | v1_xboole_0(B_741) | v1_xboole_0(A_737))), inference(resolution, [status(thm)], [c_34, c_2966])).
% 6.63/2.32  tff(c_3425, plain, (![E_771, F_767, C_768, B_770, A_766, D_769]: (k2_partfun1(k4_subset_1(A_766, C_768, D_769), B_770, k1_tmap_1(A_766, B_770, C_768, D_769, E_771, F_767), C_768)=E_771 | ~v1_funct_1(k1_tmap_1(A_766, B_770, C_768, D_769, E_771, F_767)) | k2_partfun1(D_769, B_770, F_767, k9_subset_1(A_766, C_768, D_769))!=k2_partfun1(C_768, B_770, E_771, k9_subset_1(A_766, C_768, D_769)) | ~m1_subset_1(F_767, k1_zfmisc_1(k2_zfmisc_1(D_769, B_770))) | ~v1_funct_2(F_767, D_769, B_770) | ~v1_funct_1(F_767) | ~m1_subset_1(E_771, k1_zfmisc_1(k2_zfmisc_1(C_768, B_770))) | ~v1_funct_2(E_771, C_768, B_770) | ~v1_funct_1(E_771) | ~m1_subset_1(D_769, k1_zfmisc_1(A_766)) | v1_xboole_0(D_769) | ~m1_subset_1(C_768, k1_zfmisc_1(A_766)) | v1_xboole_0(C_768) | v1_xboole_0(B_770) | v1_xboole_0(A_766))), inference(resolution, [status(thm)], [c_36, c_3242])).
% 6.63/2.32  tff(c_3431, plain, (![A_766, C_768, E_771]: (k2_partfun1(k4_subset_1(A_766, C_768, '#skF_6'), '#skF_4', k1_tmap_1(A_766, '#skF_4', C_768, '#skF_6', E_771, '#skF_8'), C_768)=E_771 | ~v1_funct_1(k1_tmap_1(A_766, '#skF_4', C_768, '#skF_6', E_771, '#skF_8')) | k2_partfun1(C_768, '#skF_4', E_771, k9_subset_1(A_766, C_768, '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1(A_766, C_768, '#skF_6')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_771, k1_zfmisc_1(k2_zfmisc_1(C_768, '#skF_4'))) | ~v1_funct_2(E_771, C_768, '#skF_4') | ~v1_funct_1(E_771) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_766)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_768, k1_zfmisc_1(A_766)) | v1_xboole_0(C_768) | v1_xboole_0('#skF_4') | v1_xboole_0(A_766))), inference(resolution, [status(thm)], [c_42, c_3425])).
% 6.63/2.32  tff(c_3439, plain, (![A_766, C_768, E_771]: (k2_partfun1(k4_subset_1(A_766, C_768, '#skF_6'), '#skF_4', k1_tmap_1(A_766, '#skF_4', C_768, '#skF_6', E_771, '#skF_8'), C_768)=E_771 | ~v1_funct_1(k1_tmap_1(A_766, '#skF_4', C_768, '#skF_6', E_771, '#skF_8')) | k2_partfun1(C_768, '#skF_4', E_771, k9_subset_1(A_766, C_768, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_766, C_768, '#skF_6')) | ~m1_subset_1(E_771, k1_zfmisc_1(k2_zfmisc_1(C_768, '#skF_4'))) | ~v1_funct_2(E_771, C_768, '#skF_4') | ~v1_funct_1(E_771) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_766)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_768, k1_zfmisc_1(A_766)) | v1_xboole_0(C_768) | v1_xboole_0('#skF_4') | v1_xboole_0(A_766))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_2564, c_3431])).
% 6.63/2.32  tff(c_3488, plain, (![A_783, C_784, E_785]: (k2_partfun1(k4_subset_1(A_783, C_784, '#skF_6'), '#skF_4', k1_tmap_1(A_783, '#skF_4', C_784, '#skF_6', E_785, '#skF_8'), C_784)=E_785 | ~v1_funct_1(k1_tmap_1(A_783, '#skF_4', C_784, '#skF_6', E_785, '#skF_8')) | k2_partfun1(C_784, '#skF_4', E_785, k9_subset_1(A_783, C_784, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_783, C_784, '#skF_6')) | ~m1_subset_1(E_785, k1_zfmisc_1(k2_zfmisc_1(C_784, '#skF_4'))) | ~v1_funct_2(E_785, C_784, '#skF_4') | ~v1_funct_1(E_785) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_783)) | ~m1_subset_1(C_784, k1_zfmisc_1(A_783)) | v1_xboole_0(C_784) | v1_xboole_0(A_783))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_3439])).
% 6.63/2.32  tff(c_3493, plain, (![A_783]: (k2_partfun1(k4_subset_1(A_783, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_783, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_783, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1(A_783, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_783, '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_783)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_783)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_783))), inference(resolution, [status(thm)], [c_48, c_3488])).
% 6.63/2.32  tff(c_3501, plain, (![A_783]: (k2_partfun1(k4_subset_1(A_783, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_783, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_783, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_783, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_783, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_783)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_783)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_783))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_2561, c_3493])).
% 6.63/2.32  tff(c_3507, plain, (![A_786]: (k2_partfun1(k4_subset_1(A_786, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_786, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_786, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_786, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_786, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_786)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_786)) | v1_xboole_0(A_786))), inference(negUnitSimplification, [status(thm)], [c_62, c_3501])).
% 6.63/2.32  tff(c_1041, plain, (![A_331, B_332]: (k3_xboole_0(A_331, B_332)=k1_xboole_0 | ~r1_subset_1(A_331, B_332) | v1_xboole_0(B_332) | v1_xboole_0(A_331))), inference(resolution, [status(thm)], [c_822, c_680])).
% 6.63/2.32  tff(c_1044, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0 | v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_54, c_1041])).
% 6.63/2.32  tff(c_1047, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_62, c_58, c_1044])).
% 6.63/2.32  tff(c_991, plain, (![A_324, B_325, C_326]: (k9_subset_1(A_324, B_325, C_326)=k3_xboole_0(B_325, C_326) | ~m1_subset_1(C_326, k1_zfmisc_1(A_324)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.63/2.32  tff(c_1003, plain, (![B_325]: (k9_subset_1('#skF_3', B_325, '#skF_6')=k3_xboole_0(B_325, '#skF_6'))), inference(resolution, [status(thm)], [c_56, c_991])).
% 6.63/2.32  tff(c_1297, plain, (![E_356, C_353, D_354, B_355, F_352, A_351]: (v1_funct_1(k1_tmap_1(A_351, B_355, C_353, D_354, E_356, F_352)) | ~m1_subset_1(F_352, k1_zfmisc_1(k2_zfmisc_1(D_354, B_355))) | ~v1_funct_2(F_352, D_354, B_355) | ~v1_funct_1(F_352) | ~m1_subset_1(E_356, k1_zfmisc_1(k2_zfmisc_1(C_353, B_355))) | ~v1_funct_2(E_356, C_353, B_355) | ~v1_funct_1(E_356) | ~m1_subset_1(D_354, k1_zfmisc_1(A_351)) | v1_xboole_0(D_354) | ~m1_subset_1(C_353, k1_zfmisc_1(A_351)) | v1_xboole_0(C_353) | v1_xboole_0(B_355) | v1_xboole_0(A_351))), inference(cnfTransformation, [status(thm)], [f_179])).
% 6.63/2.32  tff(c_1301, plain, (![A_351, C_353, E_356]: (v1_funct_1(k1_tmap_1(A_351, '#skF_4', C_353, '#skF_6', E_356, '#skF_8')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_356, k1_zfmisc_1(k2_zfmisc_1(C_353, '#skF_4'))) | ~v1_funct_2(E_356, C_353, '#skF_4') | ~v1_funct_1(E_356) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_351)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_353, k1_zfmisc_1(A_351)) | v1_xboole_0(C_353) | v1_xboole_0('#skF_4') | v1_xboole_0(A_351))), inference(resolution, [status(thm)], [c_42, c_1297])).
% 6.63/2.32  tff(c_1308, plain, (![A_351, C_353, E_356]: (v1_funct_1(k1_tmap_1(A_351, '#skF_4', C_353, '#skF_6', E_356, '#skF_8')) | ~m1_subset_1(E_356, k1_zfmisc_1(k2_zfmisc_1(C_353, '#skF_4'))) | ~v1_funct_2(E_356, C_353, '#skF_4') | ~v1_funct_1(E_356) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_351)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_353, k1_zfmisc_1(A_351)) | v1_xboole_0(C_353) | v1_xboole_0('#skF_4') | v1_xboole_0(A_351))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_1301])).
% 6.63/2.32  tff(c_1412, plain, (![A_382, C_383, E_384]: (v1_funct_1(k1_tmap_1(A_382, '#skF_4', C_383, '#skF_6', E_384, '#skF_8')) | ~m1_subset_1(E_384, k1_zfmisc_1(k2_zfmisc_1(C_383, '#skF_4'))) | ~v1_funct_2(E_384, C_383, '#skF_4') | ~v1_funct_1(E_384) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_382)) | ~m1_subset_1(C_383, k1_zfmisc_1(A_382)) | v1_xboole_0(C_383) | v1_xboole_0(A_382))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_1308])).
% 6.63/2.32  tff(c_1414, plain, (![A_382]: (v1_funct_1(k1_tmap_1(A_382, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_382)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_382)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_382))), inference(resolution, [status(thm)], [c_48, c_1412])).
% 6.63/2.32  tff(c_1419, plain, (![A_382]: (v1_funct_1(k1_tmap_1(A_382, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_382)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_382)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_382))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1414])).
% 6.63/2.32  tff(c_1450, plain, (![A_392]: (v1_funct_1(k1_tmap_1(A_392, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_392)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_392)) | v1_xboole_0(A_392))), inference(negUnitSimplification, [status(thm)], [c_62, c_1419])).
% 6.63/2.32  tff(c_1453, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_1450])).
% 6.63/2.32  tff(c_1456, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1453])).
% 6.63/2.32  tff(c_1457, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_66, c_1456])).
% 6.63/2.32  tff(c_1254, plain, (![A_345, B_346, C_347, D_348]: (k2_partfun1(A_345, B_346, C_347, D_348)=k7_relat_1(C_347, D_348) | ~m1_subset_1(C_347, k1_zfmisc_1(k2_zfmisc_1(A_345, B_346))) | ~v1_funct_1(C_347))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.63/2.32  tff(c_1256, plain, (![D_348]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_348)=k7_relat_1('#skF_7', D_348) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_48, c_1254])).
% 6.63/2.32  tff(c_1261, plain, (![D_348]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_348)=k7_relat_1('#skF_7', D_348))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1256])).
% 6.63/2.32  tff(c_1258, plain, (![D_348]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_348)=k7_relat_1('#skF_8', D_348) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_42, c_1254])).
% 6.63/2.32  tff(c_1264, plain, (![D_348]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_348)=k7_relat_1('#skF_8', D_348))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1258])).
% 6.63/2.32  tff(c_1573, plain, (![C_412, E_413, A_409, B_411, F_410, D_414]: (k2_partfun1(k4_subset_1(A_409, C_412, D_414), B_411, k1_tmap_1(A_409, B_411, C_412, D_414, E_413, F_410), D_414)=F_410 | ~m1_subset_1(k1_tmap_1(A_409, B_411, C_412, D_414, E_413, F_410), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_409, C_412, D_414), B_411))) | ~v1_funct_2(k1_tmap_1(A_409, B_411, C_412, D_414, E_413, F_410), k4_subset_1(A_409, C_412, D_414), B_411) | ~v1_funct_1(k1_tmap_1(A_409, B_411, C_412, D_414, E_413, F_410)) | k2_partfun1(D_414, B_411, F_410, k9_subset_1(A_409, C_412, D_414))!=k2_partfun1(C_412, B_411, E_413, k9_subset_1(A_409, C_412, D_414)) | ~m1_subset_1(F_410, k1_zfmisc_1(k2_zfmisc_1(D_414, B_411))) | ~v1_funct_2(F_410, D_414, B_411) | ~v1_funct_1(F_410) | ~m1_subset_1(E_413, k1_zfmisc_1(k2_zfmisc_1(C_412, B_411))) | ~v1_funct_2(E_413, C_412, B_411) | ~v1_funct_1(E_413) | ~m1_subset_1(D_414, k1_zfmisc_1(A_409)) | v1_xboole_0(D_414) | ~m1_subset_1(C_412, k1_zfmisc_1(A_409)) | v1_xboole_0(C_412) | v1_xboole_0(B_411) | v1_xboole_0(A_409))), inference(cnfTransformation, [status(thm)], [f_145])).
% 6.63/2.32  tff(c_1987, plain, (![A_510, B_514, D_513, E_515, F_511, C_512]: (k2_partfun1(k4_subset_1(A_510, C_512, D_513), B_514, k1_tmap_1(A_510, B_514, C_512, D_513, E_515, F_511), D_513)=F_511 | ~v1_funct_2(k1_tmap_1(A_510, B_514, C_512, D_513, E_515, F_511), k4_subset_1(A_510, C_512, D_513), B_514) | ~v1_funct_1(k1_tmap_1(A_510, B_514, C_512, D_513, E_515, F_511)) | k2_partfun1(D_513, B_514, F_511, k9_subset_1(A_510, C_512, D_513))!=k2_partfun1(C_512, B_514, E_515, k9_subset_1(A_510, C_512, D_513)) | ~m1_subset_1(F_511, k1_zfmisc_1(k2_zfmisc_1(D_513, B_514))) | ~v1_funct_2(F_511, D_513, B_514) | ~v1_funct_1(F_511) | ~m1_subset_1(E_515, k1_zfmisc_1(k2_zfmisc_1(C_512, B_514))) | ~v1_funct_2(E_515, C_512, B_514) | ~v1_funct_1(E_515) | ~m1_subset_1(D_513, k1_zfmisc_1(A_510)) | v1_xboole_0(D_513) | ~m1_subset_1(C_512, k1_zfmisc_1(A_510)) | v1_xboole_0(C_512) | v1_xboole_0(B_514) | v1_xboole_0(A_510))), inference(resolution, [status(thm)], [c_34, c_1573])).
% 6.63/2.32  tff(c_2102, plain, (![E_539, F_535, C_536, D_537, A_534, B_538]: (k2_partfun1(k4_subset_1(A_534, C_536, D_537), B_538, k1_tmap_1(A_534, B_538, C_536, D_537, E_539, F_535), D_537)=F_535 | ~v1_funct_1(k1_tmap_1(A_534, B_538, C_536, D_537, E_539, F_535)) | k2_partfun1(D_537, B_538, F_535, k9_subset_1(A_534, C_536, D_537))!=k2_partfun1(C_536, B_538, E_539, k9_subset_1(A_534, C_536, D_537)) | ~m1_subset_1(F_535, k1_zfmisc_1(k2_zfmisc_1(D_537, B_538))) | ~v1_funct_2(F_535, D_537, B_538) | ~v1_funct_1(F_535) | ~m1_subset_1(E_539, k1_zfmisc_1(k2_zfmisc_1(C_536, B_538))) | ~v1_funct_2(E_539, C_536, B_538) | ~v1_funct_1(E_539) | ~m1_subset_1(D_537, k1_zfmisc_1(A_534)) | v1_xboole_0(D_537) | ~m1_subset_1(C_536, k1_zfmisc_1(A_534)) | v1_xboole_0(C_536) | v1_xboole_0(B_538) | v1_xboole_0(A_534))), inference(resolution, [status(thm)], [c_36, c_1987])).
% 6.63/2.32  tff(c_2108, plain, (![A_534, C_536, E_539]: (k2_partfun1(k4_subset_1(A_534, C_536, '#skF_6'), '#skF_4', k1_tmap_1(A_534, '#skF_4', C_536, '#skF_6', E_539, '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_534, '#skF_4', C_536, '#skF_6', E_539, '#skF_8')) | k2_partfun1(C_536, '#skF_4', E_539, k9_subset_1(A_534, C_536, '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1(A_534, C_536, '#skF_6')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_539, k1_zfmisc_1(k2_zfmisc_1(C_536, '#skF_4'))) | ~v1_funct_2(E_539, C_536, '#skF_4') | ~v1_funct_1(E_539) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_534)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_536, k1_zfmisc_1(A_534)) | v1_xboole_0(C_536) | v1_xboole_0('#skF_4') | v1_xboole_0(A_534))), inference(resolution, [status(thm)], [c_42, c_2102])).
% 6.63/2.32  tff(c_2116, plain, (![A_534, C_536, E_539]: (k2_partfun1(k4_subset_1(A_534, C_536, '#skF_6'), '#skF_4', k1_tmap_1(A_534, '#skF_4', C_536, '#skF_6', E_539, '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_534, '#skF_4', C_536, '#skF_6', E_539, '#skF_8')) | k2_partfun1(C_536, '#skF_4', E_539, k9_subset_1(A_534, C_536, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_534, C_536, '#skF_6')) | ~m1_subset_1(E_539, k1_zfmisc_1(k2_zfmisc_1(C_536, '#skF_4'))) | ~v1_funct_2(E_539, C_536, '#skF_4') | ~v1_funct_1(E_539) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_534)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_536, k1_zfmisc_1(A_534)) | v1_xboole_0(C_536) | v1_xboole_0('#skF_4') | v1_xboole_0(A_534))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_1264, c_2108])).
% 6.63/2.32  tff(c_2174, plain, (![A_554, C_555, E_556]: (k2_partfun1(k4_subset_1(A_554, C_555, '#skF_6'), '#skF_4', k1_tmap_1(A_554, '#skF_4', C_555, '#skF_6', E_556, '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_554, '#skF_4', C_555, '#skF_6', E_556, '#skF_8')) | k2_partfun1(C_555, '#skF_4', E_556, k9_subset_1(A_554, C_555, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_554, C_555, '#skF_6')) | ~m1_subset_1(E_556, k1_zfmisc_1(k2_zfmisc_1(C_555, '#skF_4'))) | ~v1_funct_2(E_556, C_555, '#skF_4') | ~v1_funct_1(E_556) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_554)) | ~m1_subset_1(C_555, k1_zfmisc_1(A_554)) | v1_xboole_0(C_555) | v1_xboole_0(A_554))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_2116])).
% 6.63/2.32  tff(c_2179, plain, (![A_554]: (k2_partfun1(k4_subset_1(A_554, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_554, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_554, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1(A_554, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_554, '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_554)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_554)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_554))), inference(resolution, [status(thm)], [c_48, c_2174])).
% 6.63/2.32  tff(c_2187, plain, (![A_554]: (k2_partfun1(k4_subset_1(A_554, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_554, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_554, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_554, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_554, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_554)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_554)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_554))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1261, c_2179])).
% 6.63/2.32  tff(c_2193, plain, (![A_557]: (k2_partfun1(k4_subset_1(A_557, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_557, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_557, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_557, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_557, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_557)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_557)) | v1_xboole_0(A_557))), inference(negUnitSimplification, [status(thm)], [c_62, c_2187])).
% 6.63/2.32  tff(c_88, plain, (![C_224, A_225, B_226]: (v1_relat_1(C_224) | ~m1_subset_1(C_224, k1_zfmisc_1(k2_zfmisc_1(A_225, B_226))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.63/2.32  tff(c_96, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_42, c_88])).
% 6.63/2.32  tff(c_104, plain, (k7_relat_1('#skF_8', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_96, c_18])).
% 6.63/2.32  tff(c_236, plain, (![A_243, B_244]: (r1_xboole_0(A_243, B_244) | ~r1_subset_1(A_243, B_244) | v1_xboole_0(B_244) | v1_xboole_0(A_243))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.63/2.32  tff(c_81, plain, (![A_222, B_223]: (r2_hidden('#skF_1'(A_222, B_223), A_222) | r1_xboole_0(A_222, B_223))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.63/2.32  tff(c_10, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.63/2.32  tff(c_149, plain, (![A_233, B_234, B_235]: (~r1_xboole_0(A_233, B_234) | r1_xboole_0(k3_xboole_0(A_233, B_234), B_235))), inference(resolution, [status(thm)], [c_81, c_10])).
% 6.63/2.32  tff(c_157, plain, (![A_233, B_234]: (k3_xboole_0(A_233, B_234)=k1_xboole_0 | ~r1_xboole_0(A_233, B_234))), inference(resolution, [status(thm)], [c_149, c_14])).
% 6.63/2.32  tff(c_483, plain, (![A_269, B_270]: (k3_xboole_0(A_269, B_270)=k1_xboole_0 | ~r1_subset_1(A_269, B_270) | v1_xboole_0(B_270) | v1_xboole_0(A_269))), inference(resolution, [status(thm)], [c_236, c_157])).
% 6.63/2.32  tff(c_486, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0 | v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_54, c_483])).
% 6.63/2.32  tff(c_489, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_62, c_58, c_486])).
% 6.63/2.32  tff(c_95, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_48, c_88])).
% 6.63/2.32  tff(c_100, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_95, c_18])).
% 6.63/2.32  tff(c_417, plain, (![A_259, B_260, C_261, D_262]: (k2_partfun1(A_259, B_260, C_261, D_262)=k7_relat_1(C_261, D_262) | ~m1_subset_1(C_261, k1_zfmisc_1(k2_zfmisc_1(A_259, B_260))) | ~v1_funct_1(C_261))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.63/2.32  tff(c_419, plain, (![D_262]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_262)=k7_relat_1('#skF_7', D_262) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_48, c_417])).
% 6.63/2.32  tff(c_424, plain, (![D_262]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_262)=k7_relat_1('#skF_7', D_262))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_419])).
% 6.63/2.32  tff(c_421, plain, (![D_262]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_262)=k7_relat_1('#skF_8', D_262) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_42, c_417])).
% 6.63/2.32  tff(c_427, plain, (![D_262]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_262)=k7_relat_1('#skF_8', D_262))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_421])).
% 6.63/2.32  tff(c_404, plain, (![A_256, B_257, C_258]: (k9_subset_1(A_256, B_257, C_258)=k3_xboole_0(B_257, C_258) | ~m1_subset_1(C_258, k1_zfmisc_1(A_256)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.63/2.32  tff(c_416, plain, (![B_257]: (k9_subset_1('#skF_3', B_257, '#skF_6')=k3_xboole_0(B_257, '#skF_6'))), inference(resolution, [status(thm)], [c_56, c_404])).
% 6.63/2.32  tff(c_40, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')!='#skF_8' | k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')!='#skF_7' | k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_221])).
% 6.63/2.32  tff(c_87, plain, (k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_40])).
% 6.63/2.32  tff(c_437, plain, (k2_partfun1('#skF_5', '#skF_4', '#skF_7', k3_xboole_0('#skF_5', '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k3_xboole_0('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_416, c_416, c_87])).
% 6.63/2.32  tff(c_647, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_489, c_100, c_489, c_424, c_427, c_437])).
% 6.63/2.32  tff(c_648, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')!='#skF_7' | k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')!='#skF_8'), inference(splitRight, [status(thm)], [c_40])).
% 6.63/2.32  tff(c_944, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')!='#skF_8'), inference(splitLeft, [status(thm)], [c_648])).
% 6.63/2.32  tff(c_2204, plain, (~v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2193, c_944])).
% 6.63/2.32  tff(c_2218, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_666, c_1047, c_662, c_1047, c_1003, c_1003, c_1457, c_2204])).
% 6.63/2.32  tff(c_2220, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_2218])).
% 6.63/2.32  tff(c_2221, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_648])).
% 6.63/2.32  tff(c_3516, plain, (~v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3507, c_2221])).
% 6.63/2.32  tff(c_3527, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_666, c_2325, c_662, c_2325, c_2281, c_2281, c_2739, c_3516])).
% 6.63/2.32  tff(c_3529, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_3527])).
% 6.63/2.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.63/2.32  
% 6.63/2.32  Inference rules
% 6.63/2.32  ----------------------
% 6.63/2.32  #Ref     : 0
% 6.63/2.32  #Sup     : 755
% 6.63/2.32  #Fact    : 0
% 6.63/2.32  #Define  : 0
% 6.63/2.32  #Split   : 9
% 6.63/2.32  #Chain   : 0
% 6.63/2.32  #Close   : 0
% 6.63/2.32  
% 6.63/2.32  Ordering : KBO
% 6.63/2.32  
% 6.63/2.32  Simplification rules
% 6.63/2.32  ----------------------
% 6.63/2.32  #Subsume      : 106
% 6.63/2.32  #Demod        : 682
% 6.63/2.32  #Tautology    : 367
% 6.63/2.32  #SimpNegUnit  : 173
% 6.63/2.32  #BackRed      : 5
% 6.63/2.32  
% 6.63/2.32  #Partial instantiations: 0
% 6.63/2.32  #Strategies tried      : 1
% 6.63/2.32  
% 6.63/2.32  Timing (in seconds)
% 6.63/2.32  ----------------------
% 6.63/2.32  Preprocessing        : 0.42
% 6.63/2.32  Parsing              : 0.21
% 6.63/2.32  CNF conversion       : 0.06
% 6.63/2.32  Main loop            : 1.11
% 6.63/2.32  Inferencing          : 0.43
% 6.63/2.32  Reduction            : 0.36
% 6.63/2.32  Demodulation         : 0.26
% 6.63/2.32  BG Simplification    : 0.05
% 6.63/2.32  Subsumption          : 0.21
% 6.63/2.32  Abstraction          : 0.06
% 6.63/2.32  MUC search           : 0.00
% 6.63/2.32  Cooper               : 0.00
% 6.63/2.32  Total                : 1.59
% 6.63/2.32  Index Insertion      : 0.00
% 6.63/2.32  Index Deletion       : 0.00
% 6.63/2.32  Index Matching       : 0.00
% 6.63/2.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
