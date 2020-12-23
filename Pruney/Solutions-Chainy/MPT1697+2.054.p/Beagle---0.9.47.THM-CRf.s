%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:17 EST 2020

% Result     : Theorem 7.61s
% Output     : CNFRefutation 7.72s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 453 expanded)
%              Number of leaves         :   41 ( 185 expanded)
%              Depth                    :   12
%              Number of atoms          :  578 (2504 expanded)
%              Number of equality atoms :  108 ( 480 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_218,negated_conjecture,(
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

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_176,axiom,(
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

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_142,axiom,(
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

tff(c_72,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_92,plain,(
    ! [C_228,A_229,B_230] :
      ( v1_relat_1(C_228)
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1(A_229,B_230))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_99,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_92])).

tff(c_8,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_80,plain,(
    ! [A_225,B_226] :
      ( k3_xboole_0(A_225,B_226) = A_225
      | ~ r1_tarski(A_225,B_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_84,plain,(
    ! [A_5] : k3_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_80])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_319,plain,(
    ! [A_276,B_277] :
      ( k7_relat_1(A_276,B_277) = k1_xboole_0
      | ~ r1_xboole_0(B_277,k1_relat_1(A_276))
      | ~ v1_relat_1(A_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2279,plain,(
    ! [A_629,A_630] :
      ( k7_relat_1(A_629,A_630) = k1_xboole_0
      | ~ v1_relat_1(A_629)
      | k3_xboole_0(A_630,k1_relat_1(A_629)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_319])).

tff(c_2295,plain,(
    ! [A_631] :
      ( k7_relat_1(A_631,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_631) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_2279])).

tff(c_2303,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_99,c_2295])).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_60,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_310,plain,(
    ! [A_274,B_275] :
      ( r1_xboole_0(A_274,B_275)
      | ~ r1_subset_1(A_274,B_275)
      | v1_xboole_0(B_275)
      | v1_xboole_0(A_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2340,plain,(
    ! [A_632,B_633] :
      ( k3_xboole_0(A_632,B_633) = k1_xboole_0
      | ~ r1_subset_1(A_632,B_633)
      | v1_xboole_0(B_633)
      | v1_xboole_0(A_632) ) ),
    inference(resolution,[status(thm)],[c_310,c_2])).

tff(c_2346,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_2340])).

tff(c_2350,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_64,c_2346])).

tff(c_331,plain,(
    ! [A_279,B_280,C_281] :
      ( k9_subset_1(A_279,B_280,C_281) = k3_xboole_0(B_280,C_281)
      | ~ m1_subset_1(C_281,k1_zfmisc_1(A_279)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_342,plain,(
    ! [B_280] : k9_subset_1('#skF_1',B_280,'#skF_4') = k3_xboole_0(B_280,'#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_331])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_100,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_92])).

tff(c_2302,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_100,c_2295])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_56,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_52,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_50,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_2436,plain,(
    ! [F_649,E_645,C_648,B_650,A_647,D_646] :
      ( v1_funct_1(k1_tmap_1(A_647,B_650,C_648,D_646,E_645,F_649))
      | ~ m1_subset_1(F_649,k1_zfmisc_1(k2_zfmisc_1(D_646,B_650)))
      | ~ v1_funct_2(F_649,D_646,B_650)
      | ~ v1_funct_1(F_649)
      | ~ m1_subset_1(E_645,k1_zfmisc_1(k2_zfmisc_1(C_648,B_650)))
      | ~ v1_funct_2(E_645,C_648,B_650)
      | ~ v1_funct_1(E_645)
      | ~ m1_subset_1(D_646,k1_zfmisc_1(A_647))
      | v1_xboole_0(D_646)
      | ~ m1_subset_1(C_648,k1_zfmisc_1(A_647))
      | v1_xboole_0(C_648)
      | v1_xboole_0(B_650)
      | v1_xboole_0(A_647) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_2438,plain,(
    ! [A_647,C_648,E_645] :
      ( v1_funct_1(k1_tmap_1(A_647,'#skF_2',C_648,'#skF_4',E_645,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_645,k1_zfmisc_1(k2_zfmisc_1(C_648,'#skF_2')))
      | ~ v1_funct_2(E_645,C_648,'#skF_2')
      | ~ v1_funct_1(E_645)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_647))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_648,k1_zfmisc_1(A_647))
      | v1_xboole_0(C_648)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_647) ) ),
    inference(resolution,[status(thm)],[c_48,c_2436])).

tff(c_2443,plain,(
    ! [A_647,C_648,E_645] :
      ( v1_funct_1(k1_tmap_1(A_647,'#skF_2',C_648,'#skF_4',E_645,'#skF_6'))
      | ~ m1_subset_1(E_645,k1_zfmisc_1(k2_zfmisc_1(C_648,'#skF_2')))
      | ~ v1_funct_2(E_645,C_648,'#skF_2')
      | ~ v1_funct_1(E_645)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_647))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_648,k1_zfmisc_1(A_647))
      | v1_xboole_0(C_648)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_647) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_2438])).

tff(c_2449,plain,(
    ! [A_651,C_652,E_653] :
      ( v1_funct_1(k1_tmap_1(A_651,'#skF_2',C_652,'#skF_4',E_653,'#skF_6'))
      | ~ m1_subset_1(E_653,k1_zfmisc_1(k2_zfmisc_1(C_652,'#skF_2')))
      | ~ v1_funct_2(E_653,C_652,'#skF_2')
      | ~ v1_funct_1(E_653)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_651))
      | ~ m1_subset_1(C_652,k1_zfmisc_1(A_651))
      | v1_xboole_0(C_652)
      | v1_xboole_0(A_651) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_2443])).

tff(c_2453,plain,(
    ! [A_651] :
      ( v1_funct_1(k1_tmap_1(A_651,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_651))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_651))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_651) ) ),
    inference(resolution,[status(thm)],[c_54,c_2449])).

tff(c_2460,plain,(
    ! [A_651] :
      ( v1_funct_1(k1_tmap_1(A_651,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_651))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_651))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_651) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_2453])).

tff(c_2469,plain,(
    ! [A_655] :
      ( v1_funct_1(k1_tmap_1(A_655,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_655))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_655))
      | v1_xboole_0(A_655) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2460])).

tff(c_2472,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_2469])).

tff(c_2475,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2472])).

tff(c_2476,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2475])).

tff(c_2378,plain,(
    ! [A_636,B_637,C_638,D_639] :
      ( k2_partfun1(A_636,B_637,C_638,D_639) = k7_relat_1(C_638,D_639)
      | ~ m1_subset_1(C_638,k1_zfmisc_1(k2_zfmisc_1(A_636,B_637)))
      | ~ v1_funct_1(C_638) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2382,plain,(
    ! [D_639] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_639) = k7_relat_1('#skF_5',D_639)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_2378])).

tff(c_2388,plain,(
    ! [D_639] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_639) = k7_relat_1('#skF_5',D_639) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2382])).

tff(c_2380,plain,(
    ! [D_639] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_639) = k7_relat_1('#skF_6',D_639)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_48,c_2378])).

tff(c_2385,plain,(
    ! [D_639] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_639) = k7_relat_1('#skF_6',D_639) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2380])).

tff(c_42,plain,(
    ! [C_159,D_160,F_162,A_157,B_158,E_161] :
      ( v1_funct_2(k1_tmap_1(A_157,B_158,C_159,D_160,E_161,F_162),k4_subset_1(A_157,C_159,D_160),B_158)
      | ~ m1_subset_1(F_162,k1_zfmisc_1(k2_zfmisc_1(D_160,B_158)))
      | ~ v1_funct_2(F_162,D_160,B_158)
      | ~ v1_funct_1(F_162)
      | ~ m1_subset_1(E_161,k1_zfmisc_1(k2_zfmisc_1(C_159,B_158)))
      | ~ v1_funct_2(E_161,C_159,B_158)
      | ~ v1_funct_1(E_161)
      | ~ m1_subset_1(D_160,k1_zfmisc_1(A_157))
      | v1_xboole_0(D_160)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(A_157))
      | v1_xboole_0(C_159)
      | v1_xboole_0(B_158)
      | v1_xboole_0(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_40,plain,(
    ! [C_159,D_160,F_162,A_157,B_158,E_161] :
      ( m1_subset_1(k1_tmap_1(A_157,B_158,C_159,D_160,E_161,F_162),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_157,C_159,D_160),B_158)))
      | ~ m1_subset_1(F_162,k1_zfmisc_1(k2_zfmisc_1(D_160,B_158)))
      | ~ v1_funct_2(F_162,D_160,B_158)
      | ~ v1_funct_1(F_162)
      | ~ m1_subset_1(E_161,k1_zfmisc_1(k2_zfmisc_1(C_159,B_158)))
      | ~ v1_funct_2(E_161,C_159,B_158)
      | ~ v1_funct_1(E_161)
      | ~ m1_subset_1(D_160,k1_zfmisc_1(A_157))
      | v1_xboole_0(D_160)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(A_157))
      | v1_xboole_0(C_159)
      | v1_xboole_0(B_158)
      | v1_xboole_0(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_2661,plain,(
    ! [C_705,E_702,F_706,B_701,D_704,A_703] :
      ( k2_partfun1(k4_subset_1(A_703,C_705,D_704),B_701,k1_tmap_1(A_703,B_701,C_705,D_704,E_702,F_706),C_705) = E_702
      | ~ m1_subset_1(k1_tmap_1(A_703,B_701,C_705,D_704,E_702,F_706),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_703,C_705,D_704),B_701)))
      | ~ v1_funct_2(k1_tmap_1(A_703,B_701,C_705,D_704,E_702,F_706),k4_subset_1(A_703,C_705,D_704),B_701)
      | ~ v1_funct_1(k1_tmap_1(A_703,B_701,C_705,D_704,E_702,F_706))
      | k2_partfun1(D_704,B_701,F_706,k9_subset_1(A_703,C_705,D_704)) != k2_partfun1(C_705,B_701,E_702,k9_subset_1(A_703,C_705,D_704))
      | ~ m1_subset_1(F_706,k1_zfmisc_1(k2_zfmisc_1(D_704,B_701)))
      | ~ v1_funct_2(F_706,D_704,B_701)
      | ~ v1_funct_1(F_706)
      | ~ m1_subset_1(E_702,k1_zfmisc_1(k2_zfmisc_1(C_705,B_701)))
      | ~ v1_funct_2(E_702,C_705,B_701)
      | ~ v1_funct_1(E_702)
      | ~ m1_subset_1(D_704,k1_zfmisc_1(A_703))
      | v1_xboole_0(D_704)
      | ~ m1_subset_1(C_705,k1_zfmisc_1(A_703))
      | v1_xboole_0(C_705)
      | v1_xboole_0(B_701)
      | v1_xboole_0(A_703) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_2989,plain,(
    ! [C_797,D_795,E_794,B_799,A_796,F_798] :
      ( k2_partfun1(k4_subset_1(A_796,C_797,D_795),B_799,k1_tmap_1(A_796,B_799,C_797,D_795,E_794,F_798),C_797) = E_794
      | ~ v1_funct_2(k1_tmap_1(A_796,B_799,C_797,D_795,E_794,F_798),k4_subset_1(A_796,C_797,D_795),B_799)
      | ~ v1_funct_1(k1_tmap_1(A_796,B_799,C_797,D_795,E_794,F_798))
      | k2_partfun1(D_795,B_799,F_798,k9_subset_1(A_796,C_797,D_795)) != k2_partfun1(C_797,B_799,E_794,k9_subset_1(A_796,C_797,D_795))
      | ~ m1_subset_1(F_798,k1_zfmisc_1(k2_zfmisc_1(D_795,B_799)))
      | ~ v1_funct_2(F_798,D_795,B_799)
      | ~ v1_funct_1(F_798)
      | ~ m1_subset_1(E_794,k1_zfmisc_1(k2_zfmisc_1(C_797,B_799)))
      | ~ v1_funct_2(E_794,C_797,B_799)
      | ~ v1_funct_1(E_794)
      | ~ m1_subset_1(D_795,k1_zfmisc_1(A_796))
      | v1_xboole_0(D_795)
      | ~ m1_subset_1(C_797,k1_zfmisc_1(A_796))
      | v1_xboole_0(C_797)
      | v1_xboole_0(B_799)
      | v1_xboole_0(A_796) ) ),
    inference(resolution,[status(thm)],[c_40,c_2661])).

tff(c_3238,plain,(
    ! [D_851,B_855,F_854,C_853,A_852,E_850] :
      ( k2_partfun1(k4_subset_1(A_852,C_853,D_851),B_855,k1_tmap_1(A_852,B_855,C_853,D_851,E_850,F_854),C_853) = E_850
      | ~ v1_funct_1(k1_tmap_1(A_852,B_855,C_853,D_851,E_850,F_854))
      | k2_partfun1(D_851,B_855,F_854,k9_subset_1(A_852,C_853,D_851)) != k2_partfun1(C_853,B_855,E_850,k9_subset_1(A_852,C_853,D_851))
      | ~ m1_subset_1(F_854,k1_zfmisc_1(k2_zfmisc_1(D_851,B_855)))
      | ~ v1_funct_2(F_854,D_851,B_855)
      | ~ v1_funct_1(F_854)
      | ~ m1_subset_1(E_850,k1_zfmisc_1(k2_zfmisc_1(C_853,B_855)))
      | ~ v1_funct_2(E_850,C_853,B_855)
      | ~ v1_funct_1(E_850)
      | ~ m1_subset_1(D_851,k1_zfmisc_1(A_852))
      | v1_xboole_0(D_851)
      | ~ m1_subset_1(C_853,k1_zfmisc_1(A_852))
      | v1_xboole_0(C_853)
      | v1_xboole_0(B_855)
      | v1_xboole_0(A_852) ) ),
    inference(resolution,[status(thm)],[c_42,c_2989])).

tff(c_3242,plain,(
    ! [A_852,C_853,E_850] :
      ( k2_partfun1(k4_subset_1(A_852,C_853,'#skF_4'),'#skF_2',k1_tmap_1(A_852,'#skF_2',C_853,'#skF_4',E_850,'#skF_6'),C_853) = E_850
      | ~ v1_funct_1(k1_tmap_1(A_852,'#skF_2',C_853,'#skF_4',E_850,'#skF_6'))
      | k2_partfun1(C_853,'#skF_2',E_850,k9_subset_1(A_852,C_853,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_852,C_853,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_850,k1_zfmisc_1(k2_zfmisc_1(C_853,'#skF_2')))
      | ~ v1_funct_2(E_850,C_853,'#skF_2')
      | ~ v1_funct_1(E_850)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_852))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_853,k1_zfmisc_1(A_852))
      | v1_xboole_0(C_853)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_852) ) ),
    inference(resolution,[status(thm)],[c_48,c_3238])).

tff(c_3248,plain,(
    ! [A_852,C_853,E_850] :
      ( k2_partfun1(k4_subset_1(A_852,C_853,'#skF_4'),'#skF_2',k1_tmap_1(A_852,'#skF_2',C_853,'#skF_4',E_850,'#skF_6'),C_853) = E_850
      | ~ v1_funct_1(k1_tmap_1(A_852,'#skF_2',C_853,'#skF_4',E_850,'#skF_6'))
      | k2_partfun1(C_853,'#skF_2',E_850,k9_subset_1(A_852,C_853,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_852,C_853,'#skF_4'))
      | ~ m1_subset_1(E_850,k1_zfmisc_1(k2_zfmisc_1(C_853,'#skF_2')))
      | ~ v1_funct_2(E_850,C_853,'#skF_2')
      | ~ v1_funct_1(E_850)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_852))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_853,k1_zfmisc_1(A_852))
      | v1_xboole_0(C_853)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_852) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_2385,c_3242])).

tff(c_3620,plain,(
    ! [A_902,C_903,E_904] :
      ( k2_partfun1(k4_subset_1(A_902,C_903,'#skF_4'),'#skF_2',k1_tmap_1(A_902,'#skF_2',C_903,'#skF_4',E_904,'#skF_6'),C_903) = E_904
      | ~ v1_funct_1(k1_tmap_1(A_902,'#skF_2',C_903,'#skF_4',E_904,'#skF_6'))
      | k2_partfun1(C_903,'#skF_2',E_904,k9_subset_1(A_902,C_903,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_902,C_903,'#skF_4'))
      | ~ m1_subset_1(E_904,k1_zfmisc_1(k2_zfmisc_1(C_903,'#skF_2')))
      | ~ v1_funct_2(E_904,C_903,'#skF_2')
      | ~ v1_funct_1(E_904)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_902))
      | ~ m1_subset_1(C_903,k1_zfmisc_1(A_902))
      | v1_xboole_0(C_903)
      | v1_xboole_0(A_902) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_3248])).

tff(c_3627,plain,(
    ! [A_902] :
      ( k2_partfun1(k4_subset_1(A_902,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_902,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_902,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_902,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_902,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_902))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_902))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_902) ) ),
    inference(resolution,[status(thm)],[c_54,c_3620])).

tff(c_3637,plain,(
    ! [A_902] :
      ( k2_partfun1(k4_subset_1(A_902,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_902,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_902,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_902,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_902,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_902))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_902))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_902) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_2388,c_3627])).

tff(c_3640,plain,(
    ! [A_911] :
      ( k2_partfun1(k4_subset_1(A_911,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_911,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_911,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_911,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_911,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_911))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_911))
      | v1_xboole_0(A_911) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3637])).

tff(c_774,plain,(
    ! [A_336,A_337] :
      ( k7_relat_1(A_336,A_337) = k1_xboole_0
      | ~ v1_relat_1(A_336)
      | k3_xboole_0(A_337,k1_relat_1(A_336)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_319])).

tff(c_790,plain,(
    ! [A_338] :
      ( k7_relat_1(A_338,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_338) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_774])).

tff(c_798,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_99,c_790])).

tff(c_884,plain,(
    ! [A_347,B_348] :
      ( k3_xboole_0(A_347,B_348) = k1_xboole_0
      | ~ r1_subset_1(A_347,B_348)
      | v1_xboole_0(B_348)
      | v1_xboole_0(A_347) ) ),
    inference(resolution,[status(thm)],[c_310,c_2])).

tff(c_890,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_884])).

tff(c_894,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_64,c_890])).

tff(c_797,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_100,c_790])).

tff(c_938,plain,(
    ! [C_357,F_358,D_355,A_356,B_359,E_354] :
      ( v1_funct_1(k1_tmap_1(A_356,B_359,C_357,D_355,E_354,F_358))
      | ~ m1_subset_1(F_358,k1_zfmisc_1(k2_zfmisc_1(D_355,B_359)))
      | ~ v1_funct_2(F_358,D_355,B_359)
      | ~ v1_funct_1(F_358)
      | ~ m1_subset_1(E_354,k1_zfmisc_1(k2_zfmisc_1(C_357,B_359)))
      | ~ v1_funct_2(E_354,C_357,B_359)
      | ~ v1_funct_1(E_354)
      | ~ m1_subset_1(D_355,k1_zfmisc_1(A_356))
      | v1_xboole_0(D_355)
      | ~ m1_subset_1(C_357,k1_zfmisc_1(A_356))
      | v1_xboole_0(C_357)
      | v1_xboole_0(B_359)
      | v1_xboole_0(A_356) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_940,plain,(
    ! [A_356,C_357,E_354] :
      ( v1_funct_1(k1_tmap_1(A_356,'#skF_2',C_357,'#skF_4',E_354,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_354,k1_zfmisc_1(k2_zfmisc_1(C_357,'#skF_2')))
      | ~ v1_funct_2(E_354,C_357,'#skF_2')
      | ~ v1_funct_1(E_354)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_356))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_357,k1_zfmisc_1(A_356))
      | v1_xboole_0(C_357)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_356) ) ),
    inference(resolution,[status(thm)],[c_48,c_938])).

tff(c_945,plain,(
    ! [A_356,C_357,E_354] :
      ( v1_funct_1(k1_tmap_1(A_356,'#skF_2',C_357,'#skF_4',E_354,'#skF_6'))
      | ~ m1_subset_1(E_354,k1_zfmisc_1(k2_zfmisc_1(C_357,'#skF_2')))
      | ~ v1_funct_2(E_354,C_357,'#skF_2')
      | ~ v1_funct_1(E_354)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_356))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_357,k1_zfmisc_1(A_356))
      | v1_xboole_0(C_357)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_356) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_940])).

tff(c_951,plain,(
    ! [A_360,C_361,E_362] :
      ( v1_funct_1(k1_tmap_1(A_360,'#skF_2',C_361,'#skF_4',E_362,'#skF_6'))
      | ~ m1_subset_1(E_362,k1_zfmisc_1(k2_zfmisc_1(C_361,'#skF_2')))
      | ~ v1_funct_2(E_362,C_361,'#skF_2')
      | ~ v1_funct_1(E_362)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_360))
      | ~ m1_subset_1(C_361,k1_zfmisc_1(A_360))
      | v1_xboole_0(C_361)
      | v1_xboole_0(A_360) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_945])).

tff(c_955,plain,(
    ! [A_360] :
      ( v1_funct_1(k1_tmap_1(A_360,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_360))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_360))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_360) ) ),
    inference(resolution,[status(thm)],[c_54,c_951])).

tff(c_962,plain,(
    ! [A_360] :
      ( v1_funct_1(k1_tmap_1(A_360,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_360))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_360))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_360) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_955])).

tff(c_971,plain,(
    ! [A_364] :
      ( v1_funct_1(k1_tmap_1(A_364,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_364))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_364))
      | v1_xboole_0(A_364) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_962])).

tff(c_974,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_971])).

tff(c_977,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_974])).

tff(c_978,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_977])).

tff(c_831,plain,(
    ! [A_339,B_340,C_341,D_342] :
      ( k2_partfun1(A_339,B_340,C_341,D_342) = k7_relat_1(C_341,D_342)
      | ~ m1_subset_1(C_341,k1_zfmisc_1(k2_zfmisc_1(A_339,B_340)))
      | ~ v1_funct_1(C_341) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_835,plain,(
    ! [D_342] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_342) = k7_relat_1('#skF_5',D_342)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_831])).

tff(c_841,plain,(
    ! [D_342] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_342) = k7_relat_1('#skF_5',D_342) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_835])).

tff(c_833,plain,(
    ! [D_342] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_342) = k7_relat_1('#skF_6',D_342)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_48,c_831])).

tff(c_838,plain,(
    ! [D_342] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_342) = k7_relat_1('#skF_6',D_342) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_833])).

tff(c_1163,plain,(
    ! [B_410,D_413,C_414,E_411,A_412,F_415] :
      ( k2_partfun1(k4_subset_1(A_412,C_414,D_413),B_410,k1_tmap_1(A_412,B_410,C_414,D_413,E_411,F_415),D_413) = F_415
      | ~ m1_subset_1(k1_tmap_1(A_412,B_410,C_414,D_413,E_411,F_415),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_412,C_414,D_413),B_410)))
      | ~ v1_funct_2(k1_tmap_1(A_412,B_410,C_414,D_413,E_411,F_415),k4_subset_1(A_412,C_414,D_413),B_410)
      | ~ v1_funct_1(k1_tmap_1(A_412,B_410,C_414,D_413,E_411,F_415))
      | k2_partfun1(D_413,B_410,F_415,k9_subset_1(A_412,C_414,D_413)) != k2_partfun1(C_414,B_410,E_411,k9_subset_1(A_412,C_414,D_413))
      | ~ m1_subset_1(F_415,k1_zfmisc_1(k2_zfmisc_1(D_413,B_410)))
      | ~ v1_funct_2(F_415,D_413,B_410)
      | ~ v1_funct_1(F_415)
      | ~ m1_subset_1(E_411,k1_zfmisc_1(k2_zfmisc_1(C_414,B_410)))
      | ~ v1_funct_2(E_411,C_414,B_410)
      | ~ v1_funct_1(E_411)
      | ~ m1_subset_1(D_413,k1_zfmisc_1(A_412))
      | v1_xboole_0(D_413)
      | ~ m1_subset_1(C_414,k1_zfmisc_1(A_412))
      | v1_xboole_0(C_414)
      | v1_xboole_0(B_410)
      | v1_xboole_0(A_412) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_1629,plain,(
    ! [D_518,F_521,B_522,A_519,C_520,E_517] :
      ( k2_partfun1(k4_subset_1(A_519,C_520,D_518),B_522,k1_tmap_1(A_519,B_522,C_520,D_518,E_517,F_521),D_518) = F_521
      | ~ v1_funct_2(k1_tmap_1(A_519,B_522,C_520,D_518,E_517,F_521),k4_subset_1(A_519,C_520,D_518),B_522)
      | ~ v1_funct_1(k1_tmap_1(A_519,B_522,C_520,D_518,E_517,F_521))
      | k2_partfun1(D_518,B_522,F_521,k9_subset_1(A_519,C_520,D_518)) != k2_partfun1(C_520,B_522,E_517,k9_subset_1(A_519,C_520,D_518))
      | ~ m1_subset_1(F_521,k1_zfmisc_1(k2_zfmisc_1(D_518,B_522)))
      | ~ v1_funct_2(F_521,D_518,B_522)
      | ~ v1_funct_1(F_521)
      | ~ m1_subset_1(E_517,k1_zfmisc_1(k2_zfmisc_1(C_520,B_522)))
      | ~ v1_funct_2(E_517,C_520,B_522)
      | ~ v1_funct_1(E_517)
      | ~ m1_subset_1(D_518,k1_zfmisc_1(A_519))
      | v1_xboole_0(D_518)
      | ~ m1_subset_1(C_520,k1_zfmisc_1(A_519))
      | v1_xboole_0(C_520)
      | v1_xboole_0(B_522)
      | v1_xboole_0(A_519) ) ),
    inference(resolution,[status(thm)],[c_40,c_1163])).

tff(c_1664,plain,(
    ! [B_549,C_547,E_544,A_546,F_548,D_545] :
      ( k2_partfun1(k4_subset_1(A_546,C_547,D_545),B_549,k1_tmap_1(A_546,B_549,C_547,D_545,E_544,F_548),D_545) = F_548
      | ~ v1_funct_1(k1_tmap_1(A_546,B_549,C_547,D_545,E_544,F_548))
      | k2_partfun1(D_545,B_549,F_548,k9_subset_1(A_546,C_547,D_545)) != k2_partfun1(C_547,B_549,E_544,k9_subset_1(A_546,C_547,D_545))
      | ~ m1_subset_1(F_548,k1_zfmisc_1(k2_zfmisc_1(D_545,B_549)))
      | ~ v1_funct_2(F_548,D_545,B_549)
      | ~ v1_funct_1(F_548)
      | ~ m1_subset_1(E_544,k1_zfmisc_1(k2_zfmisc_1(C_547,B_549)))
      | ~ v1_funct_2(E_544,C_547,B_549)
      | ~ v1_funct_1(E_544)
      | ~ m1_subset_1(D_545,k1_zfmisc_1(A_546))
      | v1_xboole_0(D_545)
      | ~ m1_subset_1(C_547,k1_zfmisc_1(A_546))
      | v1_xboole_0(C_547)
      | v1_xboole_0(B_549)
      | v1_xboole_0(A_546) ) ),
    inference(resolution,[status(thm)],[c_42,c_1629])).

tff(c_1668,plain,(
    ! [A_546,C_547,E_544] :
      ( k2_partfun1(k4_subset_1(A_546,C_547,'#skF_4'),'#skF_2',k1_tmap_1(A_546,'#skF_2',C_547,'#skF_4',E_544,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_546,'#skF_2',C_547,'#skF_4',E_544,'#skF_6'))
      | k2_partfun1(C_547,'#skF_2',E_544,k9_subset_1(A_546,C_547,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_546,C_547,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_544,k1_zfmisc_1(k2_zfmisc_1(C_547,'#skF_2')))
      | ~ v1_funct_2(E_544,C_547,'#skF_2')
      | ~ v1_funct_1(E_544)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_546))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_547,k1_zfmisc_1(A_546))
      | v1_xboole_0(C_547)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_546) ) ),
    inference(resolution,[status(thm)],[c_48,c_1664])).

tff(c_1674,plain,(
    ! [A_546,C_547,E_544] :
      ( k2_partfun1(k4_subset_1(A_546,C_547,'#skF_4'),'#skF_2',k1_tmap_1(A_546,'#skF_2',C_547,'#skF_4',E_544,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_546,'#skF_2',C_547,'#skF_4',E_544,'#skF_6'))
      | k2_partfun1(C_547,'#skF_2',E_544,k9_subset_1(A_546,C_547,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_546,C_547,'#skF_4'))
      | ~ m1_subset_1(E_544,k1_zfmisc_1(k2_zfmisc_1(C_547,'#skF_2')))
      | ~ v1_funct_2(E_544,C_547,'#skF_2')
      | ~ v1_funct_1(E_544)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_546))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_547,k1_zfmisc_1(A_546))
      | v1_xboole_0(C_547)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_546) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_838,c_1668])).

tff(c_1935,plain,(
    ! [A_586,C_587,E_588] :
      ( k2_partfun1(k4_subset_1(A_586,C_587,'#skF_4'),'#skF_2',k1_tmap_1(A_586,'#skF_2',C_587,'#skF_4',E_588,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_586,'#skF_2',C_587,'#skF_4',E_588,'#skF_6'))
      | k2_partfun1(C_587,'#skF_2',E_588,k9_subset_1(A_586,C_587,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_586,C_587,'#skF_4'))
      | ~ m1_subset_1(E_588,k1_zfmisc_1(k2_zfmisc_1(C_587,'#skF_2')))
      | ~ v1_funct_2(E_588,C_587,'#skF_2')
      | ~ v1_funct_1(E_588)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_586))
      | ~ m1_subset_1(C_587,k1_zfmisc_1(A_586))
      | v1_xboole_0(C_587)
      | v1_xboole_0(A_586) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_1674])).

tff(c_1942,plain,(
    ! [A_586] :
      ( k2_partfun1(k4_subset_1(A_586,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_586,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_586,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_586,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_586,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_586))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_586))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_586) ) ),
    inference(resolution,[status(thm)],[c_54,c_1935])).

tff(c_1952,plain,(
    ! [A_586] :
      ( k2_partfun1(k4_subset_1(A_586,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_586,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_586,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_586,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_586,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_586))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_586))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_586) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_841,c_1942])).

tff(c_2005,plain,(
    ! [A_601] :
      ( k2_partfun1(k4_subset_1(A_601,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_601,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_601,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_601,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_601,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_601))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_601))
      | v1_xboole_0(A_601) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1952])).

tff(c_135,plain,(
    ! [A_242,B_243] :
      ( k7_relat_1(A_242,B_243) = k1_xboole_0
      | ~ r1_xboole_0(B_243,k1_relat_1(A_242))
      | ~ v1_relat_1(A_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_211,plain,(
    ! [A_253,A_254] :
      ( k7_relat_1(A_253,A_254) = k1_xboole_0
      | ~ v1_relat_1(A_253)
      | k3_xboole_0(A_254,k1_relat_1(A_253)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_135])).

tff(c_217,plain,(
    ! [A_255] :
      ( k7_relat_1(A_255,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_255) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_211])).

tff(c_225,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_99,c_217])).

tff(c_126,plain,(
    ! [A_240,B_241] :
      ( r1_xboole_0(A_240,B_241)
      | ~ r1_subset_1(A_240,B_241)
      | v1_xboole_0(B_241)
      | v1_xboole_0(A_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_264,plain,(
    ! [A_264,B_265] :
      ( k3_xboole_0(A_264,B_265) = k1_xboole_0
      | ~ r1_subset_1(A_264,B_265)
      | v1_xboole_0(B_265)
      | v1_xboole_0(A_264) ) ),
    inference(resolution,[status(thm)],[c_126,c_2])).

tff(c_270,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_264])).

tff(c_274,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_64,c_270])).

tff(c_224,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_100,c_217])).

tff(c_226,plain,(
    ! [A_256,B_257,C_258,D_259] :
      ( k2_partfun1(A_256,B_257,C_258,D_259) = k7_relat_1(C_258,D_259)
      | ~ m1_subset_1(C_258,k1_zfmisc_1(k2_zfmisc_1(A_256,B_257)))
      | ~ v1_funct_1(C_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_228,plain,(
    ! [D_259] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_259) = k7_relat_1('#skF_6',D_259)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_48,c_226])).

tff(c_233,plain,(
    ! [D_259] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_259) = k7_relat_1('#skF_6',D_259) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_228])).

tff(c_230,plain,(
    ! [D_259] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_259) = k7_relat_1('#skF_5',D_259)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_226])).

tff(c_236,plain,(
    ! [D_259] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_259) = k7_relat_1('#skF_5',D_259) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_230])).

tff(c_160,plain,(
    ! [A_246,B_247,C_248] :
      ( k9_subset_1(A_246,B_247,C_248) = k3_xboole_0(B_247,C_248)
      | ~ m1_subset_1(C_248,k1_zfmisc_1(A_246)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_171,plain,(
    ! [B_247] : k9_subset_1('#skF_1',B_247,'#skF_4') = k3_xboole_0(B_247,'#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_160])).

tff(c_46,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_101,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_174,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_171,c_101])).

tff(c_280,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_274,c_224,c_274,c_233,c_236,c_174])).

tff(c_281,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_534,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_281])).

tff(c_2016,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2005,c_534])).

tff(c_2030,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_798,c_894,c_342,c_797,c_894,c_342,c_978,c_2016])).

tff(c_2032,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2030])).

tff(c_2033,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_281])).

tff(c_3649,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3640,c_2033])).

tff(c_3660,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_2303,c_2350,c_342,c_2302,c_2350,c_342,c_2476,c_3649])).

tff(c_3662,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3660])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:55:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.61/2.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.72/2.65  
% 7.72/2.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.72/2.66  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.72/2.66  
% 7.72/2.66  %Foreground sorts:
% 7.72/2.66  
% 7.72/2.66  
% 7.72/2.66  %Background operators:
% 7.72/2.66  
% 7.72/2.66  
% 7.72/2.66  %Foreground operators:
% 7.72/2.66  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 7.72/2.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.72/2.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.72/2.66  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.72/2.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.72/2.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.72/2.66  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 7.72/2.66  tff('#skF_5', type, '#skF_5': $i).
% 7.72/2.66  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.72/2.66  tff('#skF_6', type, '#skF_6': $i).
% 7.72/2.66  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.72/2.66  tff('#skF_2', type, '#skF_2': $i).
% 7.72/2.66  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.72/2.66  tff('#skF_3', type, '#skF_3': $i).
% 7.72/2.66  tff('#skF_1', type, '#skF_1': $i).
% 7.72/2.66  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.72/2.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.72/2.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.72/2.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.72/2.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.72/2.66  tff('#skF_4', type, '#skF_4': $i).
% 7.72/2.66  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.72/2.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.72/2.66  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 7.72/2.66  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.72/2.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.72/2.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.72/2.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.72/2.66  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.72/2.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.72/2.66  
% 7.72/2.68  tff(f_218, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 7.72/2.68  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.72/2.68  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.72/2.68  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.72/2.68  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 7.72/2.68  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 7.72/2.68  tff(f_56, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 7.72/2.68  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 7.72/2.68  tff(f_176, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 7.72/2.68  tff(f_94, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 7.72/2.68  tff(f_142, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 7.72/2.68  tff(c_72, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_218])).
% 7.72/2.68  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_218])).
% 7.72/2.68  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_218])).
% 7.72/2.68  tff(c_48, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_218])).
% 7.72/2.68  tff(c_92, plain, (![C_228, A_229, B_230]: (v1_relat_1(C_228) | ~m1_subset_1(C_228, k1_zfmisc_1(k2_zfmisc_1(A_229, B_230))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.72/2.68  tff(c_99, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_48, c_92])).
% 7.72/2.68  tff(c_8, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.72/2.68  tff(c_80, plain, (![A_225, B_226]: (k3_xboole_0(A_225, B_226)=A_225 | ~r1_tarski(A_225, B_226))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.72/2.68  tff(c_84, plain, (![A_5]: (k3_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_80])).
% 7.72/2.68  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.72/2.68  tff(c_319, plain, (![A_276, B_277]: (k7_relat_1(A_276, B_277)=k1_xboole_0 | ~r1_xboole_0(B_277, k1_relat_1(A_276)) | ~v1_relat_1(A_276))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.72/2.68  tff(c_2279, plain, (![A_629, A_630]: (k7_relat_1(A_629, A_630)=k1_xboole_0 | ~v1_relat_1(A_629) | k3_xboole_0(A_630, k1_relat_1(A_629))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_319])).
% 7.72/2.68  tff(c_2295, plain, (![A_631]: (k7_relat_1(A_631, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_631))), inference(superposition, [status(thm), theory('equality')], [c_84, c_2279])).
% 7.72/2.68  tff(c_2303, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_99, c_2295])).
% 7.72/2.68  tff(c_68, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_218])).
% 7.72/2.68  tff(c_64, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_218])).
% 7.72/2.68  tff(c_60, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_218])).
% 7.72/2.68  tff(c_310, plain, (![A_274, B_275]: (r1_xboole_0(A_274, B_275) | ~r1_subset_1(A_274, B_275) | v1_xboole_0(B_275) | v1_xboole_0(A_274))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.72/2.68  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.72/2.68  tff(c_2340, plain, (![A_632, B_633]: (k3_xboole_0(A_632, B_633)=k1_xboole_0 | ~r1_subset_1(A_632, B_633) | v1_xboole_0(B_633) | v1_xboole_0(A_632))), inference(resolution, [status(thm)], [c_310, c_2])).
% 7.72/2.68  tff(c_2346, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_2340])).
% 7.72/2.68  tff(c_2350, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_68, c_64, c_2346])).
% 7.72/2.68  tff(c_331, plain, (![A_279, B_280, C_281]: (k9_subset_1(A_279, B_280, C_281)=k3_xboole_0(B_280, C_281) | ~m1_subset_1(C_281, k1_zfmisc_1(A_279)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.72/2.68  tff(c_342, plain, (![B_280]: (k9_subset_1('#skF_1', B_280, '#skF_4')=k3_xboole_0(B_280, '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_331])).
% 7.72/2.68  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_218])).
% 7.72/2.68  tff(c_100, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_92])).
% 7.72/2.68  tff(c_2302, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_100, c_2295])).
% 7.72/2.68  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_218])).
% 7.72/2.68  tff(c_56, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_218])).
% 7.72/2.68  tff(c_70, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_218])).
% 7.72/2.68  tff(c_52, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_218])).
% 7.72/2.68  tff(c_50, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_218])).
% 7.72/2.68  tff(c_2436, plain, (![F_649, E_645, C_648, B_650, A_647, D_646]: (v1_funct_1(k1_tmap_1(A_647, B_650, C_648, D_646, E_645, F_649)) | ~m1_subset_1(F_649, k1_zfmisc_1(k2_zfmisc_1(D_646, B_650))) | ~v1_funct_2(F_649, D_646, B_650) | ~v1_funct_1(F_649) | ~m1_subset_1(E_645, k1_zfmisc_1(k2_zfmisc_1(C_648, B_650))) | ~v1_funct_2(E_645, C_648, B_650) | ~v1_funct_1(E_645) | ~m1_subset_1(D_646, k1_zfmisc_1(A_647)) | v1_xboole_0(D_646) | ~m1_subset_1(C_648, k1_zfmisc_1(A_647)) | v1_xboole_0(C_648) | v1_xboole_0(B_650) | v1_xboole_0(A_647))), inference(cnfTransformation, [status(thm)], [f_176])).
% 7.72/2.68  tff(c_2438, plain, (![A_647, C_648, E_645]: (v1_funct_1(k1_tmap_1(A_647, '#skF_2', C_648, '#skF_4', E_645, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_645, k1_zfmisc_1(k2_zfmisc_1(C_648, '#skF_2'))) | ~v1_funct_2(E_645, C_648, '#skF_2') | ~v1_funct_1(E_645) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_647)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_648, k1_zfmisc_1(A_647)) | v1_xboole_0(C_648) | v1_xboole_0('#skF_2') | v1_xboole_0(A_647))), inference(resolution, [status(thm)], [c_48, c_2436])).
% 7.72/2.68  tff(c_2443, plain, (![A_647, C_648, E_645]: (v1_funct_1(k1_tmap_1(A_647, '#skF_2', C_648, '#skF_4', E_645, '#skF_6')) | ~m1_subset_1(E_645, k1_zfmisc_1(k2_zfmisc_1(C_648, '#skF_2'))) | ~v1_funct_2(E_645, C_648, '#skF_2') | ~v1_funct_1(E_645) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_647)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_648, k1_zfmisc_1(A_647)) | v1_xboole_0(C_648) | v1_xboole_0('#skF_2') | v1_xboole_0(A_647))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_2438])).
% 7.72/2.68  tff(c_2449, plain, (![A_651, C_652, E_653]: (v1_funct_1(k1_tmap_1(A_651, '#skF_2', C_652, '#skF_4', E_653, '#skF_6')) | ~m1_subset_1(E_653, k1_zfmisc_1(k2_zfmisc_1(C_652, '#skF_2'))) | ~v1_funct_2(E_653, C_652, '#skF_2') | ~v1_funct_1(E_653) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_651)) | ~m1_subset_1(C_652, k1_zfmisc_1(A_651)) | v1_xboole_0(C_652) | v1_xboole_0(A_651))), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_2443])).
% 7.72/2.68  tff(c_2453, plain, (![A_651]: (v1_funct_1(k1_tmap_1(A_651, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_651)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_651)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_651))), inference(resolution, [status(thm)], [c_54, c_2449])).
% 7.72/2.68  tff(c_2460, plain, (![A_651]: (v1_funct_1(k1_tmap_1(A_651, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_651)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_651)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_651))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_2453])).
% 7.72/2.68  tff(c_2469, plain, (![A_655]: (v1_funct_1(k1_tmap_1(A_655, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_655)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_655)) | v1_xboole_0(A_655))), inference(negUnitSimplification, [status(thm)], [c_68, c_2460])).
% 7.72/2.68  tff(c_2472, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_66, c_2469])).
% 7.72/2.68  tff(c_2475, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2472])).
% 7.72/2.68  tff(c_2476, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_72, c_2475])).
% 7.72/2.68  tff(c_2378, plain, (![A_636, B_637, C_638, D_639]: (k2_partfun1(A_636, B_637, C_638, D_639)=k7_relat_1(C_638, D_639) | ~m1_subset_1(C_638, k1_zfmisc_1(k2_zfmisc_1(A_636, B_637))) | ~v1_funct_1(C_638))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.72/2.68  tff(c_2382, plain, (![D_639]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_639)=k7_relat_1('#skF_5', D_639) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_2378])).
% 7.72/2.68  tff(c_2388, plain, (![D_639]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_639)=k7_relat_1('#skF_5', D_639))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2382])).
% 7.72/2.68  tff(c_2380, plain, (![D_639]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_639)=k7_relat_1('#skF_6', D_639) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_48, c_2378])).
% 7.72/2.68  tff(c_2385, plain, (![D_639]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_639)=k7_relat_1('#skF_6', D_639))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2380])).
% 7.72/2.68  tff(c_42, plain, (![C_159, D_160, F_162, A_157, B_158, E_161]: (v1_funct_2(k1_tmap_1(A_157, B_158, C_159, D_160, E_161, F_162), k4_subset_1(A_157, C_159, D_160), B_158) | ~m1_subset_1(F_162, k1_zfmisc_1(k2_zfmisc_1(D_160, B_158))) | ~v1_funct_2(F_162, D_160, B_158) | ~v1_funct_1(F_162) | ~m1_subset_1(E_161, k1_zfmisc_1(k2_zfmisc_1(C_159, B_158))) | ~v1_funct_2(E_161, C_159, B_158) | ~v1_funct_1(E_161) | ~m1_subset_1(D_160, k1_zfmisc_1(A_157)) | v1_xboole_0(D_160) | ~m1_subset_1(C_159, k1_zfmisc_1(A_157)) | v1_xboole_0(C_159) | v1_xboole_0(B_158) | v1_xboole_0(A_157))), inference(cnfTransformation, [status(thm)], [f_176])).
% 7.72/2.68  tff(c_40, plain, (![C_159, D_160, F_162, A_157, B_158, E_161]: (m1_subset_1(k1_tmap_1(A_157, B_158, C_159, D_160, E_161, F_162), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_157, C_159, D_160), B_158))) | ~m1_subset_1(F_162, k1_zfmisc_1(k2_zfmisc_1(D_160, B_158))) | ~v1_funct_2(F_162, D_160, B_158) | ~v1_funct_1(F_162) | ~m1_subset_1(E_161, k1_zfmisc_1(k2_zfmisc_1(C_159, B_158))) | ~v1_funct_2(E_161, C_159, B_158) | ~v1_funct_1(E_161) | ~m1_subset_1(D_160, k1_zfmisc_1(A_157)) | v1_xboole_0(D_160) | ~m1_subset_1(C_159, k1_zfmisc_1(A_157)) | v1_xboole_0(C_159) | v1_xboole_0(B_158) | v1_xboole_0(A_157))), inference(cnfTransformation, [status(thm)], [f_176])).
% 7.72/2.68  tff(c_2661, plain, (![C_705, E_702, F_706, B_701, D_704, A_703]: (k2_partfun1(k4_subset_1(A_703, C_705, D_704), B_701, k1_tmap_1(A_703, B_701, C_705, D_704, E_702, F_706), C_705)=E_702 | ~m1_subset_1(k1_tmap_1(A_703, B_701, C_705, D_704, E_702, F_706), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_703, C_705, D_704), B_701))) | ~v1_funct_2(k1_tmap_1(A_703, B_701, C_705, D_704, E_702, F_706), k4_subset_1(A_703, C_705, D_704), B_701) | ~v1_funct_1(k1_tmap_1(A_703, B_701, C_705, D_704, E_702, F_706)) | k2_partfun1(D_704, B_701, F_706, k9_subset_1(A_703, C_705, D_704))!=k2_partfun1(C_705, B_701, E_702, k9_subset_1(A_703, C_705, D_704)) | ~m1_subset_1(F_706, k1_zfmisc_1(k2_zfmisc_1(D_704, B_701))) | ~v1_funct_2(F_706, D_704, B_701) | ~v1_funct_1(F_706) | ~m1_subset_1(E_702, k1_zfmisc_1(k2_zfmisc_1(C_705, B_701))) | ~v1_funct_2(E_702, C_705, B_701) | ~v1_funct_1(E_702) | ~m1_subset_1(D_704, k1_zfmisc_1(A_703)) | v1_xboole_0(D_704) | ~m1_subset_1(C_705, k1_zfmisc_1(A_703)) | v1_xboole_0(C_705) | v1_xboole_0(B_701) | v1_xboole_0(A_703))), inference(cnfTransformation, [status(thm)], [f_142])).
% 7.72/2.68  tff(c_2989, plain, (![C_797, D_795, E_794, B_799, A_796, F_798]: (k2_partfun1(k4_subset_1(A_796, C_797, D_795), B_799, k1_tmap_1(A_796, B_799, C_797, D_795, E_794, F_798), C_797)=E_794 | ~v1_funct_2(k1_tmap_1(A_796, B_799, C_797, D_795, E_794, F_798), k4_subset_1(A_796, C_797, D_795), B_799) | ~v1_funct_1(k1_tmap_1(A_796, B_799, C_797, D_795, E_794, F_798)) | k2_partfun1(D_795, B_799, F_798, k9_subset_1(A_796, C_797, D_795))!=k2_partfun1(C_797, B_799, E_794, k9_subset_1(A_796, C_797, D_795)) | ~m1_subset_1(F_798, k1_zfmisc_1(k2_zfmisc_1(D_795, B_799))) | ~v1_funct_2(F_798, D_795, B_799) | ~v1_funct_1(F_798) | ~m1_subset_1(E_794, k1_zfmisc_1(k2_zfmisc_1(C_797, B_799))) | ~v1_funct_2(E_794, C_797, B_799) | ~v1_funct_1(E_794) | ~m1_subset_1(D_795, k1_zfmisc_1(A_796)) | v1_xboole_0(D_795) | ~m1_subset_1(C_797, k1_zfmisc_1(A_796)) | v1_xboole_0(C_797) | v1_xboole_0(B_799) | v1_xboole_0(A_796))), inference(resolution, [status(thm)], [c_40, c_2661])).
% 7.72/2.68  tff(c_3238, plain, (![D_851, B_855, F_854, C_853, A_852, E_850]: (k2_partfun1(k4_subset_1(A_852, C_853, D_851), B_855, k1_tmap_1(A_852, B_855, C_853, D_851, E_850, F_854), C_853)=E_850 | ~v1_funct_1(k1_tmap_1(A_852, B_855, C_853, D_851, E_850, F_854)) | k2_partfun1(D_851, B_855, F_854, k9_subset_1(A_852, C_853, D_851))!=k2_partfun1(C_853, B_855, E_850, k9_subset_1(A_852, C_853, D_851)) | ~m1_subset_1(F_854, k1_zfmisc_1(k2_zfmisc_1(D_851, B_855))) | ~v1_funct_2(F_854, D_851, B_855) | ~v1_funct_1(F_854) | ~m1_subset_1(E_850, k1_zfmisc_1(k2_zfmisc_1(C_853, B_855))) | ~v1_funct_2(E_850, C_853, B_855) | ~v1_funct_1(E_850) | ~m1_subset_1(D_851, k1_zfmisc_1(A_852)) | v1_xboole_0(D_851) | ~m1_subset_1(C_853, k1_zfmisc_1(A_852)) | v1_xboole_0(C_853) | v1_xboole_0(B_855) | v1_xboole_0(A_852))), inference(resolution, [status(thm)], [c_42, c_2989])).
% 7.72/2.68  tff(c_3242, plain, (![A_852, C_853, E_850]: (k2_partfun1(k4_subset_1(A_852, C_853, '#skF_4'), '#skF_2', k1_tmap_1(A_852, '#skF_2', C_853, '#skF_4', E_850, '#skF_6'), C_853)=E_850 | ~v1_funct_1(k1_tmap_1(A_852, '#skF_2', C_853, '#skF_4', E_850, '#skF_6')) | k2_partfun1(C_853, '#skF_2', E_850, k9_subset_1(A_852, C_853, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_852, C_853, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_850, k1_zfmisc_1(k2_zfmisc_1(C_853, '#skF_2'))) | ~v1_funct_2(E_850, C_853, '#skF_2') | ~v1_funct_1(E_850) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_852)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_853, k1_zfmisc_1(A_852)) | v1_xboole_0(C_853) | v1_xboole_0('#skF_2') | v1_xboole_0(A_852))), inference(resolution, [status(thm)], [c_48, c_3238])).
% 7.72/2.68  tff(c_3248, plain, (![A_852, C_853, E_850]: (k2_partfun1(k4_subset_1(A_852, C_853, '#skF_4'), '#skF_2', k1_tmap_1(A_852, '#skF_2', C_853, '#skF_4', E_850, '#skF_6'), C_853)=E_850 | ~v1_funct_1(k1_tmap_1(A_852, '#skF_2', C_853, '#skF_4', E_850, '#skF_6')) | k2_partfun1(C_853, '#skF_2', E_850, k9_subset_1(A_852, C_853, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_852, C_853, '#skF_4')) | ~m1_subset_1(E_850, k1_zfmisc_1(k2_zfmisc_1(C_853, '#skF_2'))) | ~v1_funct_2(E_850, C_853, '#skF_2') | ~v1_funct_1(E_850) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_852)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_853, k1_zfmisc_1(A_852)) | v1_xboole_0(C_853) | v1_xboole_0('#skF_2') | v1_xboole_0(A_852))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_2385, c_3242])).
% 7.72/2.68  tff(c_3620, plain, (![A_902, C_903, E_904]: (k2_partfun1(k4_subset_1(A_902, C_903, '#skF_4'), '#skF_2', k1_tmap_1(A_902, '#skF_2', C_903, '#skF_4', E_904, '#skF_6'), C_903)=E_904 | ~v1_funct_1(k1_tmap_1(A_902, '#skF_2', C_903, '#skF_4', E_904, '#skF_6')) | k2_partfun1(C_903, '#skF_2', E_904, k9_subset_1(A_902, C_903, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_902, C_903, '#skF_4')) | ~m1_subset_1(E_904, k1_zfmisc_1(k2_zfmisc_1(C_903, '#skF_2'))) | ~v1_funct_2(E_904, C_903, '#skF_2') | ~v1_funct_1(E_904) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_902)) | ~m1_subset_1(C_903, k1_zfmisc_1(A_902)) | v1_xboole_0(C_903) | v1_xboole_0(A_902))), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_3248])).
% 7.72/2.68  tff(c_3627, plain, (![A_902]: (k2_partfun1(k4_subset_1(A_902, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_902, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_902, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_902, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_902, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_902)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_902)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_902))), inference(resolution, [status(thm)], [c_54, c_3620])).
% 7.72/2.68  tff(c_3637, plain, (![A_902]: (k2_partfun1(k4_subset_1(A_902, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_902, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_902, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_902, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_902, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_902)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_902)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_902))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_2388, c_3627])).
% 7.72/2.68  tff(c_3640, plain, (![A_911]: (k2_partfun1(k4_subset_1(A_911, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_911, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_911, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_911, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_911, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_911)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_911)) | v1_xboole_0(A_911))), inference(negUnitSimplification, [status(thm)], [c_68, c_3637])).
% 7.72/2.68  tff(c_774, plain, (![A_336, A_337]: (k7_relat_1(A_336, A_337)=k1_xboole_0 | ~v1_relat_1(A_336) | k3_xboole_0(A_337, k1_relat_1(A_336))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_319])).
% 7.72/2.68  tff(c_790, plain, (![A_338]: (k7_relat_1(A_338, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_338))), inference(superposition, [status(thm), theory('equality')], [c_84, c_774])).
% 7.72/2.68  tff(c_798, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_99, c_790])).
% 7.72/2.68  tff(c_884, plain, (![A_347, B_348]: (k3_xboole_0(A_347, B_348)=k1_xboole_0 | ~r1_subset_1(A_347, B_348) | v1_xboole_0(B_348) | v1_xboole_0(A_347))), inference(resolution, [status(thm)], [c_310, c_2])).
% 7.72/2.68  tff(c_890, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_884])).
% 7.72/2.68  tff(c_894, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_68, c_64, c_890])).
% 7.72/2.68  tff(c_797, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_100, c_790])).
% 7.72/2.68  tff(c_938, plain, (![C_357, F_358, D_355, A_356, B_359, E_354]: (v1_funct_1(k1_tmap_1(A_356, B_359, C_357, D_355, E_354, F_358)) | ~m1_subset_1(F_358, k1_zfmisc_1(k2_zfmisc_1(D_355, B_359))) | ~v1_funct_2(F_358, D_355, B_359) | ~v1_funct_1(F_358) | ~m1_subset_1(E_354, k1_zfmisc_1(k2_zfmisc_1(C_357, B_359))) | ~v1_funct_2(E_354, C_357, B_359) | ~v1_funct_1(E_354) | ~m1_subset_1(D_355, k1_zfmisc_1(A_356)) | v1_xboole_0(D_355) | ~m1_subset_1(C_357, k1_zfmisc_1(A_356)) | v1_xboole_0(C_357) | v1_xboole_0(B_359) | v1_xboole_0(A_356))), inference(cnfTransformation, [status(thm)], [f_176])).
% 7.72/2.68  tff(c_940, plain, (![A_356, C_357, E_354]: (v1_funct_1(k1_tmap_1(A_356, '#skF_2', C_357, '#skF_4', E_354, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_354, k1_zfmisc_1(k2_zfmisc_1(C_357, '#skF_2'))) | ~v1_funct_2(E_354, C_357, '#skF_2') | ~v1_funct_1(E_354) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_356)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_357, k1_zfmisc_1(A_356)) | v1_xboole_0(C_357) | v1_xboole_0('#skF_2') | v1_xboole_0(A_356))), inference(resolution, [status(thm)], [c_48, c_938])).
% 7.72/2.68  tff(c_945, plain, (![A_356, C_357, E_354]: (v1_funct_1(k1_tmap_1(A_356, '#skF_2', C_357, '#skF_4', E_354, '#skF_6')) | ~m1_subset_1(E_354, k1_zfmisc_1(k2_zfmisc_1(C_357, '#skF_2'))) | ~v1_funct_2(E_354, C_357, '#skF_2') | ~v1_funct_1(E_354) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_356)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_357, k1_zfmisc_1(A_356)) | v1_xboole_0(C_357) | v1_xboole_0('#skF_2') | v1_xboole_0(A_356))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_940])).
% 7.72/2.68  tff(c_951, plain, (![A_360, C_361, E_362]: (v1_funct_1(k1_tmap_1(A_360, '#skF_2', C_361, '#skF_4', E_362, '#skF_6')) | ~m1_subset_1(E_362, k1_zfmisc_1(k2_zfmisc_1(C_361, '#skF_2'))) | ~v1_funct_2(E_362, C_361, '#skF_2') | ~v1_funct_1(E_362) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_360)) | ~m1_subset_1(C_361, k1_zfmisc_1(A_360)) | v1_xboole_0(C_361) | v1_xboole_0(A_360))), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_945])).
% 7.72/2.68  tff(c_955, plain, (![A_360]: (v1_funct_1(k1_tmap_1(A_360, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_360)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_360)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_360))), inference(resolution, [status(thm)], [c_54, c_951])).
% 7.72/2.68  tff(c_962, plain, (![A_360]: (v1_funct_1(k1_tmap_1(A_360, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_360)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_360)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_360))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_955])).
% 7.72/2.68  tff(c_971, plain, (![A_364]: (v1_funct_1(k1_tmap_1(A_364, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_364)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_364)) | v1_xboole_0(A_364))), inference(negUnitSimplification, [status(thm)], [c_68, c_962])).
% 7.72/2.68  tff(c_974, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_66, c_971])).
% 7.72/2.68  tff(c_977, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_974])).
% 7.72/2.68  tff(c_978, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_72, c_977])).
% 7.72/2.68  tff(c_831, plain, (![A_339, B_340, C_341, D_342]: (k2_partfun1(A_339, B_340, C_341, D_342)=k7_relat_1(C_341, D_342) | ~m1_subset_1(C_341, k1_zfmisc_1(k2_zfmisc_1(A_339, B_340))) | ~v1_funct_1(C_341))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.72/2.68  tff(c_835, plain, (![D_342]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_342)=k7_relat_1('#skF_5', D_342) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_831])).
% 7.72/2.68  tff(c_841, plain, (![D_342]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_342)=k7_relat_1('#skF_5', D_342))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_835])).
% 7.72/2.68  tff(c_833, plain, (![D_342]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_342)=k7_relat_1('#skF_6', D_342) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_48, c_831])).
% 7.72/2.68  tff(c_838, plain, (![D_342]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_342)=k7_relat_1('#skF_6', D_342))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_833])).
% 7.72/2.68  tff(c_1163, plain, (![B_410, D_413, C_414, E_411, A_412, F_415]: (k2_partfun1(k4_subset_1(A_412, C_414, D_413), B_410, k1_tmap_1(A_412, B_410, C_414, D_413, E_411, F_415), D_413)=F_415 | ~m1_subset_1(k1_tmap_1(A_412, B_410, C_414, D_413, E_411, F_415), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_412, C_414, D_413), B_410))) | ~v1_funct_2(k1_tmap_1(A_412, B_410, C_414, D_413, E_411, F_415), k4_subset_1(A_412, C_414, D_413), B_410) | ~v1_funct_1(k1_tmap_1(A_412, B_410, C_414, D_413, E_411, F_415)) | k2_partfun1(D_413, B_410, F_415, k9_subset_1(A_412, C_414, D_413))!=k2_partfun1(C_414, B_410, E_411, k9_subset_1(A_412, C_414, D_413)) | ~m1_subset_1(F_415, k1_zfmisc_1(k2_zfmisc_1(D_413, B_410))) | ~v1_funct_2(F_415, D_413, B_410) | ~v1_funct_1(F_415) | ~m1_subset_1(E_411, k1_zfmisc_1(k2_zfmisc_1(C_414, B_410))) | ~v1_funct_2(E_411, C_414, B_410) | ~v1_funct_1(E_411) | ~m1_subset_1(D_413, k1_zfmisc_1(A_412)) | v1_xboole_0(D_413) | ~m1_subset_1(C_414, k1_zfmisc_1(A_412)) | v1_xboole_0(C_414) | v1_xboole_0(B_410) | v1_xboole_0(A_412))), inference(cnfTransformation, [status(thm)], [f_142])).
% 7.72/2.68  tff(c_1629, plain, (![D_518, F_521, B_522, A_519, C_520, E_517]: (k2_partfun1(k4_subset_1(A_519, C_520, D_518), B_522, k1_tmap_1(A_519, B_522, C_520, D_518, E_517, F_521), D_518)=F_521 | ~v1_funct_2(k1_tmap_1(A_519, B_522, C_520, D_518, E_517, F_521), k4_subset_1(A_519, C_520, D_518), B_522) | ~v1_funct_1(k1_tmap_1(A_519, B_522, C_520, D_518, E_517, F_521)) | k2_partfun1(D_518, B_522, F_521, k9_subset_1(A_519, C_520, D_518))!=k2_partfun1(C_520, B_522, E_517, k9_subset_1(A_519, C_520, D_518)) | ~m1_subset_1(F_521, k1_zfmisc_1(k2_zfmisc_1(D_518, B_522))) | ~v1_funct_2(F_521, D_518, B_522) | ~v1_funct_1(F_521) | ~m1_subset_1(E_517, k1_zfmisc_1(k2_zfmisc_1(C_520, B_522))) | ~v1_funct_2(E_517, C_520, B_522) | ~v1_funct_1(E_517) | ~m1_subset_1(D_518, k1_zfmisc_1(A_519)) | v1_xboole_0(D_518) | ~m1_subset_1(C_520, k1_zfmisc_1(A_519)) | v1_xboole_0(C_520) | v1_xboole_0(B_522) | v1_xboole_0(A_519))), inference(resolution, [status(thm)], [c_40, c_1163])).
% 7.72/2.68  tff(c_1664, plain, (![B_549, C_547, E_544, A_546, F_548, D_545]: (k2_partfun1(k4_subset_1(A_546, C_547, D_545), B_549, k1_tmap_1(A_546, B_549, C_547, D_545, E_544, F_548), D_545)=F_548 | ~v1_funct_1(k1_tmap_1(A_546, B_549, C_547, D_545, E_544, F_548)) | k2_partfun1(D_545, B_549, F_548, k9_subset_1(A_546, C_547, D_545))!=k2_partfun1(C_547, B_549, E_544, k9_subset_1(A_546, C_547, D_545)) | ~m1_subset_1(F_548, k1_zfmisc_1(k2_zfmisc_1(D_545, B_549))) | ~v1_funct_2(F_548, D_545, B_549) | ~v1_funct_1(F_548) | ~m1_subset_1(E_544, k1_zfmisc_1(k2_zfmisc_1(C_547, B_549))) | ~v1_funct_2(E_544, C_547, B_549) | ~v1_funct_1(E_544) | ~m1_subset_1(D_545, k1_zfmisc_1(A_546)) | v1_xboole_0(D_545) | ~m1_subset_1(C_547, k1_zfmisc_1(A_546)) | v1_xboole_0(C_547) | v1_xboole_0(B_549) | v1_xboole_0(A_546))), inference(resolution, [status(thm)], [c_42, c_1629])).
% 7.72/2.68  tff(c_1668, plain, (![A_546, C_547, E_544]: (k2_partfun1(k4_subset_1(A_546, C_547, '#skF_4'), '#skF_2', k1_tmap_1(A_546, '#skF_2', C_547, '#skF_4', E_544, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_546, '#skF_2', C_547, '#skF_4', E_544, '#skF_6')) | k2_partfun1(C_547, '#skF_2', E_544, k9_subset_1(A_546, C_547, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_546, C_547, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_544, k1_zfmisc_1(k2_zfmisc_1(C_547, '#skF_2'))) | ~v1_funct_2(E_544, C_547, '#skF_2') | ~v1_funct_1(E_544) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_546)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_547, k1_zfmisc_1(A_546)) | v1_xboole_0(C_547) | v1_xboole_0('#skF_2') | v1_xboole_0(A_546))), inference(resolution, [status(thm)], [c_48, c_1664])).
% 7.72/2.68  tff(c_1674, plain, (![A_546, C_547, E_544]: (k2_partfun1(k4_subset_1(A_546, C_547, '#skF_4'), '#skF_2', k1_tmap_1(A_546, '#skF_2', C_547, '#skF_4', E_544, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_546, '#skF_2', C_547, '#skF_4', E_544, '#skF_6')) | k2_partfun1(C_547, '#skF_2', E_544, k9_subset_1(A_546, C_547, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_546, C_547, '#skF_4')) | ~m1_subset_1(E_544, k1_zfmisc_1(k2_zfmisc_1(C_547, '#skF_2'))) | ~v1_funct_2(E_544, C_547, '#skF_2') | ~v1_funct_1(E_544) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_546)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_547, k1_zfmisc_1(A_546)) | v1_xboole_0(C_547) | v1_xboole_0('#skF_2') | v1_xboole_0(A_546))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_838, c_1668])).
% 7.72/2.68  tff(c_1935, plain, (![A_586, C_587, E_588]: (k2_partfun1(k4_subset_1(A_586, C_587, '#skF_4'), '#skF_2', k1_tmap_1(A_586, '#skF_2', C_587, '#skF_4', E_588, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_586, '#skF_2', C_587, '#skF_4', E_588, '#skF_6')) | k2_partfun1(C_587, '#skF_2', E_588, k9_subset_1(A_586, C_587, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_586, C_587, '#skF_4')) | ~m1_subset_1(E_588, k1_zfmisc_1(k2_zfmisc_1(C_587, '#skF_2'))) | ~v1_funct_2(E_588, C_587, '#skF_2') | ~v1_funct_1(E_588) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_586)) | ~m1_subset_1(C_587, k1_zfmisc_1(A_586)) | v1_xboole_0(C_587) | v1_xboole_0(A_586))), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_1674])).
% 7.72/2.68  tff(c_1942, plain, (![A_586]: (k2_partfun1(k4_subset_1(A_586, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_586, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_586, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_586, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_586, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_586)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_586)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_586))), inference(resolution, [status(thm)], [c_54, c_1935])).
% 7.72/2.68  tff(c_1952, plain, (![A_586]: (k2_partfun1(k4_subset_1(A_586, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_586, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_586, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_586, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_586, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_586)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_586)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_586))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_841, c_1942])).
% 7.72/2.68  tff(c_2005, plain, (![A_601]: (k2_partfun1(k4_subset_1(A_601, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_601, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_601, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_601, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_601, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_601)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_601)) | v1_xboole_0(A_601))), inference(negUnitSimplification, [status(thm)], [c_68, c_1952])).
% 7.72/2.68  tff(c_135, plain, (![A_242, B_243]: (k7_relat_1(A_242, B_243)=k1_xboole_0 | ~r1_xboole_0(B_243, k1_relat_1(A_242)) | ~v1_relat_1(A_242))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.72/2.68  tff(c_211, plain, (![A_253, A_254]: (k7_relat_1(A_253, A_254)=k1_xboole_0 | ~v1_relat_1(A_253) | k3_xboole_0(A_254, k1_relat_1(A_253))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_135])).
% 7.72/2.68  tff(c_217, plain, (![A_255]: (k7_relat_1(A_255, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_255))), inference(superposition, [status(thm), theory('equality')], [c_84, c_211])).
% 7.72/2.68  tff(c_225, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_99, c_217])).
% 7.72/2.68  tff(c_126, plain, (![A_240, B_241]: (r1_xboole_0(A_240, B_241) | ~r1_subset_1(A_240, B_241) | v1_xboole_0(B_241) | v1_xboole_0(A_240))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.72/2.68  tff(c_264, plain, (![A_264, B_265]: (k3_xboole_0(A_264, B_265)=k1_xboole_0 | ~r1_subset_1(A_264, B_265) | v1_xboole_0(B_265) | v1_xboole_0(A_264))), inference(resolution, [status(thm)], [c_126, c_2])).
% 7.72/2.68  tff(c_270, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_264])).
% 7.72/2.68  tff(c_274, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_68, c_64, c_270])).
% 7.72/2.68  tff(c_224, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_100, c_217])).
% 7.72/2.68  tff(c_226, plain, (![A_256, B_257, C_258, D_259]: (k2_partfun1(A_256, B_257, C_258, D_259)=k7_relat_1(C_258, D_259) | ~m1_subset_1(C_258, k1_zfmisc_1(k2_zfmisc_1(A_256, B_257))) | ~v1_funct_1(C_258))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.72/2.68  tff(c_228, plain, (![D_259]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_259)=k7_relat_1('#skF_6', D_259) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_48, c_226])).
% 7.72/2.68  tff(c_233, plain, (![D_259]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_259)=k7_relat_1('#skF_6', D_259))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_228])).
% 7.72/2.68  tff(c_230, plain, (![D_259]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_259)=k7_relat_1('#skF_5', D_259) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_226])).
% 7.72/2.68  tff(c_236, plain, (![D_259]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_259)=k7_relat_1('#skF_5', D_259))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_230])).
% 7.72/2.68  tff(c_160, plain, (![A_246, B_247, C_248]: (k9_subset_1(A_246, B_247, C_248)=k3_xboole_0(B_247, C_248) | ~m1_subset_1(C_248, k1_zfmisc_1(A_246)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.72/2.68  tff(c_171, plain, (![B_247]: (k9_subset_1('#skF_1', B_247, '#skF_4')=k3_xboole_0(B_247, '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_160])).
% 7.72/2.68  tff(c_46, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_218])).
% 7.72/2.68  tff(c_101, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_46])).
% 7.72/2.68  tff(c_174, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_171, c_101])).
% 7.72/2.68  tff(c_280, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_225, c_274, c_224, c_274, c_233, c_236, c_174])).
% 7.72/2.68  tff(c_281, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_46])).
% 7.72/2.68  tff(c_534, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_281])).
% 7.72/2.68  tff(c_2016, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2005, c_534])).
% 7.72/2.68  tff(c_2030, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_798, c_894, c_342, c_797, c_894, c_342, c_978, c_2016])).
% 7.72/2.68  tff(c_2032, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_2030])).
% 7.72/2.68  tff(c_2033, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_281])).
% 7.72/2.68  tff(c_3649, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3640, c_2033])).
% 7.72/2.68  tff(c_3660, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_2303, c_2350, c_342, c_2302, c_2350, c_342, c_2476, c_3649])).
% 7.72/2.68  tff(c_3662, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_3660])).
% 7.72/2.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.72/2.68  
% 7.72/2.68  Inference rules
% 7.72/2.68  ----------------------
% 7.72/2.68  #Ref     : 0
% 7.72/2.68  #Sup     : 726
% 7.72/2.68  #Fact    : 0
% 7.72/2.68  #Define  : 0
% 7.72/2.68  #Split   : 35
% 7.72/2.68  #Chain   : 0
% 7.72/2.68  #Close   : 0
% 7.72/2.68  
% 7.72/2.68  Ordering : KBO
% 7.72/2.68  
% 7.72/2.68  Simplification rules
% 7.72/2.69  ----------------------
% 7.72/2.69  #Subsume      : 56
% 7.72/2.69  #Demod        : 694
% 7.72/2.69  #Tautology    : 317
% 7.72/2.69  #SimpNegUnit  : 207
% 7.72/2.69  #BackRed      : 6
% 7.72/2.69  
% 7.72/2.69  #Partial instantiations: 0
% 7.72/2.69  #Strategies tried      : 1
% 7.72/2.69  
% 7.72/2.69  Timing (in seconds)
% 7.72/2.69  ----------------------
% 7.72/2.69  Preprocessing        : 0.44
% 7.72/2.69  Parsing              : 0.22
% 7.72/2.69  CNF conversion       : 0.06
% 7.72/2.69  Main loop            : 1.41
% 7.72/2.69  Inferencing          : 0.54
% 7.72/2.69  Reduction            : 0.48
% 7.72/2.69  Demodulation         : 0.35
% 7.72/2.69  BG Simplification    : 0.05
% 7.72/2.69  Subsumption          : 0.25
% 7.72/2.69  Abstraction          : 0.06
% 7.72/2.69  MUC search           : 0.00
% 7.72/2.69  Cooper               : 0.00
% 7.72/2.69  Total                : 1.91
% 7.72/2.69  Index Insertion      : 0.00
% 7.72/2.69  Index Deletion       : 0.00
% 7.72/2.69  Index Matching       : 0.00
% 7.72/2.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
