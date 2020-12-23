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
% DateTime   : Thu Dec  3 10:26:21 EST 2020

% Result     : Theorem 8.06s
% Output     : CNFRefutation 8.20s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 454 expanded)
%              Number of leaves         :   41 ( 184 expanded)
%              Depth                    :   12
%              Number of atoms          :  592 (2500 expanded)
%              Number of equality atoms :  103 ( 440 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_55,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_35,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_72,axiom,(
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

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

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

tff(c_76,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_70,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_16,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_460,plain,(
    ! [B_287,A_288] :
      ( v1_relat_1(B_287)
      | ~ m1_subset_1(B_287,k1_zfmisc_1(A_288))
      | ~ v1_relat_1(A_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_466,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_460])).

tff(c_478,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_466])).

tff(c_8,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_79,plain,(
    ! [B_228,A_229] :
      ( r1_xboole_0(B_228,A_229)
      | ~ r1_xboole_0(A_229,B_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_82,plain,(
    ! [A_5] : r1_xboole_0(k1_xboole_0,A_5) ),
    inference(resolution,[status(thm)],[c_8,c_79])).

tff(c_3273,plain,(
    ! [A_702,B_703] :
      ( k7_relat_1(A_702,B_703) = k1_xboole_0
      | ~ r1_xboole_0(B_703,k1_relat_1(A_702))
      | ~ v1_relat_1(A_702) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3294,plain,(
    ! [A_704] :
      ( k7_relat_1(A_704,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_704) ) ),
    inference(resolution,[status(thm)],[c_82,c_3273])).

tff(c_3304,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_478,c_3294])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_463,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_58,c_460])).

tff(c_475,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_463])).

tff(c_3305,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_475,c_3294])).

tff(c_72,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_64,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_535,plain,(
    ! [A_299,B_300] :
      ( r1_xboole_0(A_299,B_300)
      | ~ r1_subset_1(A_299,B_300)
      | v1_xboole_0(B_300)
      | v1_xboole_0(A_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4607,plain,(
    ! [A_845,B_846] :
      ( k3_xboole_0(A_845,B_846) = k1_xboole_0
      | ~ r1_subset_1(A_845,B_846)
      | v1_xboole_0(B_846)
      | v1_xboole_0(A_845) ) ),
    inference(resolution,[status(thm)],[c_535,c_2])).

tff(c_4616,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_4607])).

tff(c_4623,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_68,c_4616])).

tff(c_4330,plain,(
    ! [A_816,B_817,C_818] :
      ( k9_subset_1(A_816,B_817,C_818) = k3_xboole_0(B_817,C_818)
      | ~ m1_subset_1(C_818,k1_zfmisc_1(A_816)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4342,plain,(
    ! [B_817] : k9_subset_1('#skF_1',B_817,'#skF_4') = k3_xboole_0(B_817,'#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_4330])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_60,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_56,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_54,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_4710,plain,(
    ! [E_857,A_856,F_854,D_855,C_858,B_853] :
      ( v1_funct_1(k1_tmap_1(A_856,B_853,C_858,D_855,E_857,F_854))
      | ~ m1_subset_1(F_854,k1_zfmisc_1(k2_zfmisc_1(D_855,B_853)))
      | ~ v1_funct_2(F_854,D_855,B_853)
      | ~ v1_funct_1(F_854)
      | ~ m1_subset_1(E_857,k1_zfmisc_1(k2_zfmisc_1(C_858,B_853)))
      | ~ v1_funct_2(E_857,C_858,B_853)
      | ~ v1_funct_1(E_857)
      | ~ m1_subset_1(D_855,k1_zfmisc_1(A_856))
      | v1_xboole_0(D_855)
      | ~ m1_subset_1(C_858,k1_zfmisc_1(A_856))
      | v1_xboole_0(C_858)
      | v1_xboole_0(B_853)
      | v1_xboole_0(A_856) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_4714,plain,(
    ! [A_856,C_858,E_857] :
      ( v1_funct_1(k1_tmap_1(A_856,'#skF_2',C_858,'#skF_4',E_857,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_857,k1_zfmisc_1(k2_zfmisc_1(C_858,'#skF_2')))
      | ~ v1_funct_2(E_857,C_858,'#skF_2')
      | ~ v1_funct_1(E_857)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_856))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_858,k1_zfmisc_1(A_856))
      | v1_xboole_0(C_858)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_856) ) ),
    inference(resolution,[status(thm)],[c_52,c_4710])).

tff(c_4721,plain,(
    ! [A_856,C_858,E_857] :
      ( v1_funct_1(k1_tmap_1(A_856,'#skF_2',C_858,'#skF_4',E_857,'#skF_6'))
      | ~ m1_subset_1(E_857,k1_zfmisc_1(k2_zfmisc_1(C_858,'#skF_2')))
      | ~ v1_funct_2(E_857,C_858,'#skF_2')
      | ~ v1_funct_1(E_857)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_856))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_858,k1_zfmisc_1(A_856))
      | v1_xboole_0(C_858)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_856) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4714])).

tff(c_4797,plain,(
    ! [A_868,C_869,E_870] :
      ( v1_funct_1(k1_tmap_1(A_868,'#skF_2',C_869,'#skF_4',E_870,'#skF_6'))
      | ~ m1_subset_1(E_870,k1_zfmisc_1(k2_zfmisc_1(C_869,'#skF_2')))
      | ~ v1_funct_2(E_870,C_869,'#skF_2')
      | ~ v1_funct_1(E_870)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_868))
      | ~ m1_subset_1(C_869,k1_zfmisc_1(A_868))
      | v1_xboole_0(C_869)
      | v1_xboole_0(A_868) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_4721])).

tff(c_4799,plain,(
    ! [A_868] :
      ( v1_funct_1(k1_tmap_1(A_868,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_868))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_868))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_868) ) ),
    inference(resolution,[status(thm)],[c_58,c_4797])).

tff(c_4804,plain,(
    ! [A_868] :
      ( v1_funct_1(k1_tmap_1(A_868,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_868))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_868))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_868) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_4799])).

tff(c_4818,plain,(
    ! [A_878] :
      ( v1_funct_1(k1_tmap_1(A_878,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_878))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_878))
      | v1_xboole_0(A_878) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_4804])).

tff(c_4821,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_4818])).

tff(c_4824,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_4821])).

tff(c_4825,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_4824])).

tff(c_4468,plain,(
    ! [A_828,B_829,C_830,D_831] :
      ( k2_partfun1(A_828,B_829,C_830,D_831) = k7_relat_1(C_830,D_831)
      | ~ m1_subset_1(C_830,k1_zfmisc_1(k2_zfmisc_1(A_828,B_829)))
      | ~ v1_funct_1(C_830) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_4470,plain,(
    ! [D_831] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_831) = k7_relat_1('#skF_5',D_831)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_58,c_4468])).

tff(c_4475,plain,(
    ! [D_831] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_831) = k7_relat_1('#skF_5',D_831) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_4470])).

tff(c_4472,plain,(
    ! [D_831] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_831) = k7_relat_1('#skF_6',D_831)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_52,c_4468])).

tff(c_4478,plain,(
    ! [D_831] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_831) = k7_relat_1('#skF_6',D_831) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_4472])).

tff(c_46,plain,(
    ! [E_166,F_167,B_163,D_165,A_162,C_164] :
      ( v1_funct_2(k1_tmap_1(A_162,B_163,C_164,D_165,E_166,F_167),k4_subset_1(A_162,C_164,D_165),B_163)
      | ~ m1_subset_1(F_167,k1_zfmisc_1(k2_zfmisc_1(D_165,B_163)))
      | ~ v1_funct_2(F_167,D_165,B_163)
      | ~ v1_funct_1(F_167)
      | ~ m1_subset_1(E_166,k1_zfmisc_1(k2_zfmisc_1(C_164,B_163)))
      | ~ v1_funct_2(E_166,C_164,B_163)
      | ~ v1_funct_1(E_166)
      | ~ m1_subset_1(D_165,k1_zfmisc_1(A_162))
      | v1_xboole_0(D_165)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(A_162))
      | v1_xboole_0(C_164)
      | v1_xboole_0(B_163)
      | v1_xboole_0(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_44,plain,(
    ! [E_166,F_167,B_163,D_165,A_162,C_164] :
      ( m1_subset_1(k1_tmap_1(A_162,B_163,C_164,D_165,E_166,F_167),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_162,C_164,D_165),B_163)))
      | ~ m1_subset_1(F_167,k1_zfmisc_1(k2_zfmisc_1(D_165,B_163)))
      | ~ v1_funct_2(F_167,D_165,B_163)
      | ~ v1_funct_1(F_167)
      | ~ m1_subset_1(E_166,k1_zfmisc_1(k2_zfmisc_1(C_164,B_163)))
      | ~ v1_funct_2(E_166,C_164,B_163)
      | ~ v1_funct_1(E_166)
      | ~ m1_subset_1(D_165,k1_zfmisc_1(A_162))
      | v1_xboole_0(D_165)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(A_162))
      | v1_xboole_0(C_164)
      | v1_xboole_0(B_163)
      | v1_xboole_0(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_4920,plain,(
    ! [E_897,C_900,A_896,B_898,F_895,D_899] :
      ( k2_partfun1(k4_subset_1(A_896,C_900,D_899),B_898,k1_tmap_1(A_896,B_898,C_900,D_899,E_897,F_895),C_900) = E_897
      | ~ m1_subset_1(k1_tmap_1(A_896,B_898,C_900,D_899,E_897,F_895),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_896,C_900,D_899),B_898)))
      | ~ v1_funct_2(k1_tmap_1(A_896,B_898,C_900,D_899,E_897,F_895),k4_subset_1(A_896,C_900,D_899),B_898)
      | ~ v1_funct_1(k1_tmap_1(A_896,B_898,C_900,D_899,E_897,F_895))
      | k2_partfun1(D_899,B_898,F_895,k9_subset_1(A_896,C_900,D_899)) != k2_partfun1(C_900,B_898,E_897,k9_subset_1(A_896,C_900,D_899))
      | ~ m1_subset_1(F_895,k1_zfmisc_1(k2_zfmisc_1(D_899,B_898)))
      | ~ v1_funct_2(F_895,D_899,B_898)
      | ~ v1_funct_1(F_895)
      | ~ m1_subset_1(E_897,k1_zfmisc_1(k2_zfmisc_1(C_900,B_898)))
      | ~ v1_funct_2(E_897,C_900,B_898)
      | ~ v1_funct_1(E_897)
      | ~ m1_subset_1(D_899,k1_zfmisc_1(A_896))
      | v1_xboole_0(D_899)
      | ~ m1_subset_1(C_900,k1_zfmisc_1(A_896))
      | v1_xboole_0(C_900)
      | v1_xboole_0(B_898)
      | v1_xboole_0(A_896) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_5311,plain,(
    ! [D_1008,B_1006,F_1007,E_1010,A_1009,C_1011] :
      ( k2_partfun1(k4_subset_1(A_1009,C_1011,D_1008),B_1006,k1_tmap_1(A_1009,B_1006,C_1011,D_1008,E_1010,F_1007),C_1011) = E_1010
      | ~ v1_funct_2(k1_tmap_1(A_1009,B_1006,C_1011,D_1008,E_1010,F_1007),k4_subset_1(A_1009,C_1011,D_1008),B_1006)
      | ~ v1_funct_1(k1_tmap_1(A_1009,B_1006,C_1011,D_1008,E_1010,F_1007))
      | k2_partfun1(D_1008,B_1006,F_1007,k9_subset_1(A_1009,C_1011,D_1008)) != k2_partfun1(C_1011,B_1006,E_1010,k9_subset_1(A_1009,C_1011,D_1008))
      | ~ m1_subset_1(F_1007,k1_zfmisc_1(k2_zfmisc_1(D_1008,B_1006)))
      | ~ v1_funct_2(F_1007,D_1008,B_1006)
      | ~ v1_funct_1(F_1007)
      | ~ m1_subset_1(E_1010,k1_zfmisc_1(k2_zfmisc_1(C_1011,B_1006)))
      | ~ v1_funct_2(E_1010,C_1011,B_1006)
      | ~ v1_funct_1(E_1010)
      | ~ m1_subset_1(D_1008,k1_zfmisc_1(A_1009))
      | v1_xboole_0(D_1008)
      | ~ m1_subset_1(C_1011,k1_zfmisc_1(A_1009))
      | v1_xboole_0(C_1011)
      | v1_xboole_0(B_1006)
      | v1_xboole_0(A_1009) ) ),
    inference(resolution,[status(thm)],[c_44,c_4920])).

tff(c_5741,plain,(
    ! [A_1060,C_1062,E_1061,B_1057,D_1059,F_1058] :
      ( k2_partfun1(k4_subset_1(A_1060,C_1062,D_1059),B_1057,k1_tmap_1(A_1060,B_1057,C_1062,D_1059,E_1061,F_1058),C_1062) = E_1061
      | ~ v1_funct_1(k1_tmap_1(A_1060,B_1057,C_1062,D_1059,E_1061,F_1058))
      | k2_partfun1(D_1059,B_1057,F_1058,k9_subset_1(A_1060,C_1062,D_1059)) != k2_partfun1(C_1062,B_1057,E_1061,k9_subset_1(A_1060,C_1062,D_1059))
      | ~ m1_subset_1(F_1058,k1_zfmisc_1(k2_zfmisc_1(D_1059,B_1057)))
      | ~ v1_funct_2(F_1058,D_1059,B_1057)
      | ~ v1_funct_1(F_1058)
      | ~ m1_subset_1(E_1061,k1_zfmisc_1(k2_zfmisc_1(C_1062,B_1057)))
      | ~ v1_funct_2(E_1061,C_1062,B_1057)
      | ~ v1_funct_1(E_1061)
      | ~ m1_subset_1(D_1059,k1_zfmisc_1(A_1060))
      | v1_xboole_0(D_1059)
      | ~ m1_subset_1(C_1062,k1_zfmisc_1(A_1060))
      | v1_xboole_0(C_1062)
      | v1_xboole_0(B_1057)
      | v1_xboole_0(A_1060) ) ),
    inference(resolution,[status(thm)],[c_46,c_5311])).

tff(c_5747,plain,(
    ! [A_1060,C_1062,E_1061] :
      ( k2_partfun1(k4_subset_1(A_1060,C_1062,'#skF_4'),'#skF_2',k1_tmap_1(A_1060,'#skF_2',C_1062,'#skF_4',E_1061,'#skF_6'),C_1062) = E_1061
      | ~ v1_funct_1(k1_tmap_1(A_1060,'#skF_2',C_1062,'#skF_4',E_1061,'#skF_6'))
      | k2_partfun1(C_1062,'#skF_2',E_1061,k9_subset_1(A_1060,C_1062,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_1060,C_1062,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1061,k1_zfmisc_1(k2_zfmisc_1(C_1062,'#skF_2')))
      | ~ v1_funct_2(E_1061,C_1062,'#skF_2')
      | ~ v1_funct_1(E_1061)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1060))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1062,k1_zfmisc_1(A_1060))
      | v1_xboole_0(C_1062)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1060) ) ),
    inference(resolution,[status(thm)],[c_52,c_5741])).

tff(c_5755,plain,(
    ! [A_1060,C_1062,E_1061] :
      ( k2_partfun1(k4_subset_1(A_1060,C_1062,'#skF_4'),'#skF_2',k1_tmap_1(A_1060,'#skF_2',C_1062,'#skF_4',E_1061,'#skF_6'),C_1062) = E_1061
      | ~ v1_funct_1(k1_tmap_1(A_1060,'#skF_2',C_1062,'#skF_4',E_1061,'#skF_6'))
      | k2_partfun1(C_1062,'#skF_2',E_1061,k9_subset_1(A_1060,C_1062,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1060,C_1062,'#skF_4'))
      | ~ m1_subset_1(E_1061,k1_zfmisc_1(k2_zfmisc_1(C_1062,'#skF_2')))
      | ~ v1_funct_2(E_1061,C_1062,'#skF_2')
      | ~ v1_funct_1(E_1061)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1060))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1062,k1_zfmisc_1(A_1060))
      | v1_xboole_0(C_1062)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1060) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4478,c_5747])).

tff(c_5854,plain,(
    ! [A_1092,C_1093,E_1094] :
      ( k2_partfun1(k4_subset_1(A_1092,C_1093,'#skF_4'),'#skF_2',k1_tmap_1(A_1092,'#skF_2',C_1093,'#skF_4',E_1094,'#skF_6'),C_1093) = E_1094
      | ~ v1_funct_1(k1_tmap_1(A_1092,'#skF_2',C_1093,'#skF_4',E_1094,'#skF_6'))
      | k2_partfun1(C_1093,'#skF_2',E_1094,k9_subset_1(A_1092,C_1093,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1092,C_1093,'#skF_4'))
      | ~ m1_subset_1(E_1094,k1_zfmisc_1(k2_zfmisc_1(C_1093,'#skF_2')))
      | ~ v1_funct_2(E_1094,C_1093,'#skF_2')
      | ~ v1_funct_1(E_1094)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1092))
      | ~ m1_subset_1(C_1093,k1_zfmisc_1(A_1092))
      | v1_xboole_0(C_1093)
      | v1_xboole_0(A_1092) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_5755])).

tff(c_5859,plain,(
    ! [A_1092] :
      ( k2_partfun1(k4_subset_1(A_1092,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1092,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1092,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1092,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1092,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1092))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1092))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1092) ) ),
    inference(resolution,[status(thm)],[c_58,c_5854])).

tff(c_5867,plain,(
    ! [A_1092] :
      ( k2_partfun1(k4_subset_1(A_1092,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1092,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1092,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1092,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1092,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1092))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1092))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1092) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_4475,c_5859])).

tff(c_6149,plain,(
    ! [A_1122] :
      ( k2_partfun1(k4_subset_1(A_1122,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1122,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1122,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1122,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1122,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1122))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1122))
      | v1_xboole_0(A_1122) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_5867])).

tff(c_568,plain,(
    ! [A_304,B_305] :
      ( k7_relat_1(A_304,B_305) = k1_xboole_0
      | ~ r1_xboole_0(B_305,k1_relat_1(A_304))
      | ~ v1_relat_1(A_304) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_589,plain,(
    ! [A_306] :
      ( k7_relat_1(A_306,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_306) ) ),
    inference(resolution,[status(thm)],[c_82,c_568])).

tff(c_599,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_478,c_589])).

tff(c_600,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_475,c_589])).

tff(c_1661,plain,(
    ! [A_399,B_400] :
      ( k3_xboole_0(A_399,B_400) = k1_xboole_0
      | ~ r1_subset_1(A_399,B_400)
      | v1_xboole_0(B_400)
      | v1_xboole_0(A_399) ) ),
    inference(resolution,[status(thm)],[c_535,c_2])).

tff(c_1667,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_1661])).

tff(c_1673,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_68,c_1667])).

tff(c_606,plain,(
    ! [A_307,B_308,C_309] :
      ( k9_subset_1(A_307,B_308,C_309) = k3_xboole_0(B_308,C_309)
      | ~ m1_subset_1(C_309,k1_zfmisc_1(A_307)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_618,plain,(
    ! [B_308] : k9_subset_1('#skF_1',B_308,'#skF_4') = k3_xboole_0(B_308,'#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_606])).

tff(c_1876,plain,(
    ! [F_423,C_427,D_424,B_422,A_425,E_426] :
      ( v1_funct_1(k1_tmap_1(A_425,B_422,C_427,D_424,E_426,F_423))
      | ~ m1_subset_1(F_423,k1_zfmisc_1(k2_zfmisc_1(D_424,B_422)))
      | ~ v1_funct_2(F_423,D_424,B_422)
      | ~ v1_funct_1(F_423)
      | ~ m1_subset_1(E_426,k1_zfmisc_1(k2_zfmisc_1(C_427,B_422)))
      | ~ v1_funct_2(E_426,C_427,B_422)
      | ~ v1_funct_1(E_426)
      | ~ m1_subset_1(D_424,k1_zfmisc_1(A_425))
      | v1_xboole_0(D_424)
      | ~ m1_subset_1(C_427,k1_zfmisc_1(A_425))
      | v1_xboole_0(C_427)
      | v1_xboole_0(B_422)
      | v1_xboole_0(A_425) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_1880,plain,(
    ! [A_425,C_427,E_426] :
      ( v1_funct_1(k1_tmap_1(A_425,'#skF_2',C_427,'#skF_4',E_426,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_426,k1_zfmisc_1(k2_zfmisc_1(C_427,'#skF_2')))
      | ~ v1_funct_2(E_426,C_427,'#skF_2')
      | ~ v1_funct_1(E_426)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_425))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_427,k1_zfmisc_1(A_425))
      | v1_xboole_0(C_427)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_425) ) ),
    inference(resolution,[status(thm)],[c_52,c_1876])).

tff(c_1887,plain,(
    ! [A_425,C_427,E_426] :
      ( v1_funct_1(k1_tmap_1(A_425,'#skF_2',C_427,'#skF_4',E_426,'#skF_6'))
      | ~ m1_subset_1(E_426,k1_zfmisc_1(k2_zfmisc_1(C_427,'#skF_2')))
      | ~ v1_funct_2(E_426,C_427,'#skF_2')
      | ~ v1_funct_1(E_426)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_425))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_427,k1_zfmisc_1(A_425))
      | v1_xboole_0(C_427)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_425) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_1880])).

tff(c_1912,plain,(
    ! [A_430,C_431,E_432] :
      ( v1_funct_1(k1_tmap_1(A_430,'#skF_2',C_431,'#skF_4',E_432,'#skF_6'))
      | ~ m1_subset_1(E_432,k1_zfmisc_1(k2_zfmisc_1(C_431,'#skF_2')))
      | ~ v1_funct_2(E_432,C_431,'#skF_2')
      | ~ v1_funct_1(E_432)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_430))
      | ~ m1_subset_1(C_431,k1_zfmisc_1(A_430))
      | v1_xboole_0(C_431)
      | v1_xboole_0(A_430) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_1887])).

tff(c_1914,plain,(
    ! [A_430] :
      ( v1_funct_1(k1_tmap_1(A_430,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_430))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_430))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_430) ) ),
    inference(resolution,[status(thm)],[c_58,c_1912])).

tff(c_1919,plain,(
    ! [A_430] :
      ( v1_funct_1(k1_tmap_1(A_430,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_430))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_430))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_430) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1914])).

tff(c_1932,plain,(
    ! [A_434] :
      ( v1_funct_1(k1_tmap_1(A_434,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_434))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_434))
      | v1_xboole_0(A_434) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1919])).

tff(c_1935,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_1932])).

tff(c_1938,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1935])).

tff(c_1939,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1938])).

tff(c_1682,plain,(
    ! [A_401,B_402,C_403,D_404] :
      ( k2_partfun1(A_401,B_402,C_403,D_404) = k7_relat_1(C_403,D_404)
      | ~ m1_subset_1(C_403,k1_zfmisc_1(k2_zfmisc_1(A_401,B_402)))
      | ~ v1_funct_1(C_403) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1684,plain,(
    ! [D_404] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_404) = k7_relat_1('#skF_5',D_404)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_58,c_1682])).

tff(c_1689,plain,(
    ! [D_404] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_404) = k7_relat_1('#skF_5',D_404) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1684])).

tff(c_1686,plain,(
    ! [D_404] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_404) = k7_relat_1('#skF_6',D_404)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_52,c_1682])).

tff(c_1692,plain,(
    ! [D_404] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_404) = k7_relat_1('#skF_6',D_404) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1686])).

tff(c_2113,plain,(
    ! [E_475,C_478,A_474,F_473,D_477,B_476] :
      ( k2_partfun1(k4_subset_1(A_474,C_478,D_477),B_476,k1_tmap_1(A_474,B_476,C_478,D_477,E_475,F_473),D_477) = F_473
      | ~ m1_subset_1(k1_tmap_1(A_474,B_476,C_478,D_477,E_475,F_473),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_474,C_478,D_477),B_476)))
      | ~ v1_funct_2(k1_tmap_1(A_474,B_476,C_478,D_477,E_475,F_473),k4_subset_1(A_474,C_478,D_477),B_476)
      | ~ v1_funct_1(k1_tmap_1(A_474,B_476,C_478,D_477,E_475,F_473))
      | k2_partfun1(D_477,B_476,F_473,k9_subset_1(A_474,C_478,D_477)) != k2_partfun1(C_478,B_476,E_475,k9_subset_1(A_474,C_478,D_477))
      | ~ m1_subset_1(F_473,k1_zfmisc_1(k2_zfmisc_1(D_477,B_476)))
      | ~ v1_funct_2(F_473,D_477,B_476)
      | ~ v1_funct_1(F_473)
      | ~ m1_subset_1(E_475,k1_zfmisc_1(k2_zfmisc_1(C_478,B_476)))
      | ~ v1_funct_2(E_475,C_478,B_476)
      | ~ v1_funct_1(E_475)
      | ~ m1_subset_1(D_477,k1_zfmisc_1(A_474))
      | v1_xboole_0(D_477)
      | ~ m1_subset_1(C_478,k1_zfmisc_1(A_474))
      | v1_xboole_0(C_478)
      | v1_xboole_0(B_476)
      | v1_xboole_0(A_474) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_2634,plain,(
    ! [E_594,C_595,B_590,D_592,F_591,A_593] :
      ( k2_partfun1(k4_subset_1(A_593,C_595,D_592),B_590,k1_tmap_1(A_593,B_590,C_595,D_592,E_594,F_591),D_592) = F_591
      | ~ v1_funct_2(k1_tmap_1(A_593,B_590,C_595,D_592,E_594,F_591),k4_subset_1(A_593,C_595,D_592),B_590)
      | ~ v1_funct_1(k1_tmap_1(A_593,B_590,C_595,D_592,E_594,F_591))
      | k2_partfun1(D_592,B_590,F_591,k9_subset_1(A_593,C_595,D_592)) != k2_partfun1(C_595,B_590,E_594,k9_subset_1(A_593,C_595,D_592))
      | ~ m1_subset_1(F_591,k1_zfmisc_1(k2_zfmisc_1(D_592,B_590)))
      | ~ v1_funct_2(F_591,D_592,B_590)
      | ~ v1_funct_1(F_591)
      | ~ m1_subset_1(E_594,k1_zfmisc_1(k2_zfmisc_1(C_595,B_590)))
      | ~ v1_funct_2(E_594,C_595,B_590)
      | ~ v1_funct_1(E_594)
      | ~ m1_subset_1(D_592,k1_zfmisc_1(A_593))
      | v1_xboole_0(D_592)
      | ~ m1_subset_1(C_595,k1_zfmisc_1(A_593))
      | v1_xboole_0(C_595)
      | v1_xboole_0(B_590)
      | v1_xboole_0(A_593) ) ),
    inference(resolution,[status(thm)],[c_44,c_2113])).

tff(c_2848,plain,(
    ! [F_625,B_624,D_626,E_628,A_627,C_629] :
      ( k2_partfun1(k4_subset_1(A_627,C_629,D_626),B_624,k1_tmap_1(A_627,B_624,C_629,D_626,E_628,F_625),D_626) = F_625
      | ~ v1_funct_1(k1_tmap_1(A_627,B_624,C_629,D_626,E_628,F_625))
      | k2_partfun1(D_626,B_624,F_625,k9_subset_1(A_627,C_629,D_626)) != k2_partfun1(C_629,B_624,E_628,k9_subset_1(A_627,C_629,D_626))
      | ~ m1_subset_1(F_625,k1_zfmisc_1(k2_zfmisc_1(D_626,B_624)))
      | ~ v1_funct_2(F_625,D_626,B_624)
      | ~ v1_funct_1(F_625)
      | ~ m1_subset_1(E_628,k1_zfmisc_1(k2_zfmisc_1(C_629,B_624)))
      | ~ v1_funct_2(E_628,C_629,B_624)
      | ~ v1_funct_1(E_628)
      | ~ m1_subset_1(D_626,k1_zfmisc_1(A_627))
      | v1_xboole_0(D_626)
      | ~ m1_subset_1(C_629,k1_zfmisc_1(A_627))
      | v1_xboole_0(C_629)
      | v1_xboole_0(B_624)
      | v1_xboole_0(A_627) ) ),
    inference(resolution,[status(thm)],[c_46,c_2634])).

tff(c_2854,plain,(
    ! [A_627,C_629,E_628] :
      ( k2_partfun1(k4_subset_1(A_627,C_629,'#skF_4'),'#skF_2',k1_tmap_1(A_627,'#skF_2',C_629,'#skF_4',E_628,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_627,'#skF_2',C_629,'#skF_4',E_628,'#skF_6'))
      | k2_partfun1(C_629,'#skF_2',E_628,k9_subset_1(A_627,C_629,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_627,C_629,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_628,k1_zfmisc_1(k2_zfmisc_1(C_629,'#skF_2')))
      | ~ v1_funct_2(E_628,C_629,'#skF_2')
      | ~ v1_funct_1(E_628)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_627))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_629,k1_zfmisc_1(A_627))
      | v1_xboole_0(C_629)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_627) ) ),
    inference(resolution,[status(thm)],[c_52,c_2848])).

tff(c_2862,plain,(
    ! [A_627,C_629,E_628] :
      ( k2_partfun1(k4_subset_1(A_627,C_629,'#skF_4'),'#skF_2',k1_tmap_1(A_627,'#skF_2',C_629,'#skF_4',E_628,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_627,'#skF_2',C_629,'#skF_4',E_628,'#skF_6'))
      | k2_partfun1(C_629,'#skF_2',E_628,k9_subset_1(A_627,C_629,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_627,C_629,'#skF_4'))
      | ~ m1_subset_1(E_628,k1_zfmisc_1(k2_zfmisc_1(C_629,'#skF_2')))
      | ~ v1_funct_2(E_628,C_629,'#skF_2')
      | ~ v1_funct_1(E_628)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_627))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_629,k1_zfmisc_1(A_627))
      | v1_xboole_0(C_629)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_627) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_1692,c_2854])).

tff(c_3203,plain,(
    ! [A_697,C_698,E_699] :
      ( k2_partfun1(k4_subset_1(A_697,C_698,'#skF_4'),'#skF_2',k1_tmap_1(A_697,'#skF_2',C_698,'#skF_4',E_699,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_697,'#skF_2',C_698,'#skF_4',E_699,'#skF_6'))
      | k2_partfun1(C_698,'#skF_2',E_699,k9_subset_1(A_697,C_698,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_697,C_698,'#skF_4'))
      | ~ m1_subset_1(E_699,k1_zfmisc_1(k2_zfmisc_1(C_698,'#skF_2')))
      | ~ v1_funct_2(E_699,C_698,'#skF_2')
      | ~ v1_funct_1(E_699)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_697))
      | ~ m1_subset_1(C_698,k1_zfmisc_1(A_697))
      | v1_xboole_0(C_698)
      | v1_xboole_0(A_697) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_2862])).

tff(c_3208,plain,(
    ! [A_697] :
      ( k2_partfun1(k4_subset_1(A_697,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_697,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_697,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_697,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_697,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_697))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_697))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_697) ) ),
    inference(resolution,[status(thm)],[c_58,c_3203])).

tff(c_3216,plain,(
    ! [A_697] :
      ( k2_partfun1(k4_subset_1(A_697,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_697,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_697,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_697,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_697,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_697))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_697))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_697) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1689,c_3208])).

tff(c_3238,plain,(
    ! [A_701] :
      ( k2_partfun1(k4_subset_1(A_701,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_701,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_701,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_701,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_701,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_701))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_701))
      | v1_xboole_0(A_701) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3216])).

tff(c_136,plain,(
    ! [B_239,A_240] :
      ( v1_relat_1(B_239)
      | ~ m1_subset_1(B_239,k1_zfmisc_1(A_240))
      | ~ v1_relat_1(A_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_139,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_58,c_136])).

tff(c_151,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_139])).

tff(c_215,plain,(
    ! [A_254,B_255] :
      ( k7_relat_1(A_254,B_255) = k1_xboole_0
      | ~ r1_xboole_0(B_255,k1_relat_1(A_254))
      | ~ v1_relat_1(A_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_236,plain,(
    ! [A_256] :
      ( k7_relat_1(A_256,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_256) ) ),
    inference(resolution,[status(thm)],[c_82,c_215])).

tff(c_247,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_151,c_236])).

tff(c_142,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_136])).

tff(c_154,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_142])).

tff(c_246,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_154,c_236])).

tff(c_207,plain,(
    ! [A_252,B_253] :
      ( r1_xboole_0(A_252,B_253)
      | ~ r1_subset_1(A_252,B_253)
      | v1_xboole_0(B_253)
      | v1_xboole_0(A_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_410,plain,(
    ! [A_280,B_281] :
      ( k3_xboole_0(A_280,B_281) = k1_xboole_0
      | ~ r1_subset_1(A_280,B_281)
      | v1_xboole_0(B_281)
      | v1_xboole_0(A_280) ) ),
    inference(resolution,[status(thm)],[c_207,c_2])).

tff(c_416,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_410])).

tff(c_422,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_68,c_416])).

tff(c_371,plain,(
    ! [A_273,B_274,C_275,D_276] :
      ( k2_partfun1(A_273,B_274,C_275,D_276) = k7_relat_1(C_275,D_276)
      | ~ m1_subset_1(C_275,k1_zfmisc_1(k2_zfmisc_1(A_273,B_274)))
      | ~ v1_funct_1(C_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_375,plain,(
    ! [D_276] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_276) = k7_relat_1('#skF_6',D_276)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_52,c_371])).

tff(c_381,plain,(
    ! [D_276] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_276) = k7_relat_1('#skF_6',D_276) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_375])).

tff(c_373,plain,(
    ! [D_276] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_276) = k7_relat_1('#skF_5',D_276)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_58,c_371])).

tff(c_378,plain,(
    ! [D_276] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_276) = k7_relat_1('#skF_5',D_276) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_373])).

tff(c_330,plain,(
    ! [A_267,B_268,C_269] :
      ( k9_subset_1(A_267,B_268,C_269) = k3_xboole_0(B_268,C_269)
      | ~ m1_subset_1(C_269,k1_zfmisc_1(A_267)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_342,plain,(
    ! [B_268] : k9_subset_1('#skF_1',B_268,'#skF_4') = k3_xboole_0(B_268,'#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_330])).

tff(c_50,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_104,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_352,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_342,c_104])).

tff(c_409,plain,(
    k7_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k7_relat_1('#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_381,c_378,c_352])).

tff(c_423,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) != k7_relat_1('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_422,c_409])).

tff(c_426,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_246,c_423])).

tff(c_427,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_566,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_427])).

tff(c_3249,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3238,c_566])).

tff(c_3263,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_599,c_600,c_1673,c_618,c_1673,c_618,c_1939,c_3249])).

tff(c_3265,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_3263])).

tff(c_3266,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_427])).

tff(c_6158,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6149,c_3266])).

tff(c_6169,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_3304,c_3305,c_4623,c_4342,c_4623,c_4342,c_4825,c_6158])).

tff(c_6171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_6169])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:30:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.06/3.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.06/3.08  
% 8.06/3.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.06/3.08  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.06/3.08  
% 8.06/3.08  %Foreground sorts:
% 8.06/3.08  
% 8.06/3.08  
% 8.06/3.08  %Background operators:
% 8.06/3.08  
% 8.06/3.08  
% 8.06/3.08  %Foreground operators:
% 8.06/3.08  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 8.06/3.08  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.06/3.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.06/3.08  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.06/3.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.06/3.08  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 8.06/3.08  tff('#skF_5', type, '#skF_5': $i).
% 8.06/3.08  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.06/3.08  tff('#skF_6', type, '#skF_6': $i).
% 8.06/3.08  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.06/3.08  tff('#skF_2', type, '#skF_2': $i).
% 8.06/3.08  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 8.06/3.08  tff('#skF_3', type, '#skF_3': $i).
% 8.06/3.08  tff('#skF_1', type, '#skF_1': $i).
% 8.06/3.08  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.06/3.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.06/3.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.06/3.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.06/3.08  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.06/3.08  tff('#skF_4', type, '#skF_4': $i).
% 8.06/3.08  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.06/3.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.06/3.08  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 8.06/3.08  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.06/3.08  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.06/3.08  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.06/3.08  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.06/3.08  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 8.06/3.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.06/3.08  
% 8.20/3.11  tff(f_230, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 8.20/3.11  tff(f_55, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.20/3.11  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.20/3.11  tff(f_35, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 8.20/3.11  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 8.20/3.11  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 8.20/3.11  tff(f_72, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 8.20/3.11  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.20/3.11  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 8.20/3.11  tff(f_188, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 8.20/3.11  tff(f_106, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 8.20/3.11  tff(f_154, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 8.20/3.11  tff(c_76, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.20/3.11  tff(c_70, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.20/3.11  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.20/3.11  tff(c_16, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.20/3.11  tff(c_52, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.20/3.11  tff(c_460, plain, (![B_287, A_288]: (v1_relat_1(B_287) | ~m1_subset_1(B_287, k1_zfmisc_1(A_288)) | ~v1_relat_1(A_288))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.20/3.11  tff(c_466, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_460])).
% 8.20/3.11  tff(c_478, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_466])).
% 8.20/3.11  tff(c_8, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.20/3.11  tff(c_79, plain, (![B_228, A_229]: (r1_xboole_0(B_228, A_229) | ~r1_xboole_0(A_229, B_228))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.20/3.11  tff(c_82, plain, (![A_5]: (r1_xboole_0(k1_xboole_0, A_5))), inference(resolution, [status(thm)], [c_8, c_79])).
% 8.20/3.11  tff(c_3273, plain, (![A_702, B_703]: (k7_relat_1(A_702, B_703)=k1_xboole_0 | ~r1_xboole_0(B_703, k1_relat_1(A_702)) | ~v1_relat_1(A_702))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.20/3.11  tff(c_3294, plain, (![A_704]: (k7_relat_1(A_704, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_704))), inference(resolution, [status(thm)], [c_82, c_3273])).
% 8.20/3.11  tff(c_3304, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_478, c_3294])).
% 8.20/3.11  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.20/3.11  tff(c_463, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_460])).
% 8.20/3.11  tff(c_475, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_463])).
% 8.20/3.11  tff(c_3305, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_475, c_3294])).
% 8.20/3.11  tff(c_72, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.20/3.11  tff(c_68, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.20/3.11  tff(c_64, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.20/3.11  tff(c_535, plain, (![A_299, B_300]: (r1_xboole_0(A_299, B_300) | ~r1_subset_1(A_299, B_300) | v1_xboole_0(B_300) | v1_xboole_0(A_299))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.20/3.11  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.20/3.11  tff(c_4607, plain, (![A_845, B_846]: (k3_xboole_0(A_845, B_846)=k1_xboole_0 | ~r1_subset_1(A_845, B_846) | v1_xboole_0(B_846) | v1_xboole_0(A_845))), inference(resolution, [status(thm)], [c_535, c_2])).
% 8.20/3.11  tff(c_4616, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_64, c_4607])).
% 8.20/3.11  tff(c_4623, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_72, c_68, c_4616])).
% 8.20/3.11  tff(c_4330, plain, (![A_816, B_817, C_818]: (k9_subset_1(A_816, B_817, C_818)=k3_xboole_0(B_817, C_818) | ~m1_subset_1(C_818, k1_zfmisc_1(A_816)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.20/3.11  tff(c_4342, plain, (![B_817]: (k9_subset_1('#skF_1', B_817, '#skF_4')=k3_xboole_0(B_817, '#skF_4'))), inference(resolution, [status(thm)], [c_66, c_4330])).
% 8.20/3.11  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.20/3.11  tff(c_60, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.20/3.11  tff(c_74, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.20/3.11  tff(c_56, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.20/3.11  tff(c_54, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.20/3.11  tff(c_4710, plain, (![E_857, A_856, F_854, D_855, C_858, B_853]: (v1_funct_1(k1_tmap_1(A_856, B_853, C_858, D_855, E_857, F_854)) | ~m1_subset_1(F_854, k1_zfmisc_1(k2_zfmisc_1(D_855, B_853))) | ~v1_funct_2(F_854, D_855, B_853) | ~v1_funct_1(F_854) | ~m1_subset_1(E_857, k1_zfmisc_1(k2_zfmisc_1(C_858, B_853))) | ~v1_funct_2(E_857, C_858, B_853) | ~v1_funct_1(E_857) | ~m1_subset_1(D_855, k1_zfmisc_1(A_856)) | v1_xboole_0(D_855) | ~m1_subset_1(C_858, k1_zfmisc_1(A_856)) | v1_xboole_0(C_858) | v1_xboole_0(B_853) | v1_xboole_0(A_856))), inference(cnfTransformation, [status(thm)], [f_188])).
% 8.20/3.11  tff(c_4714, plain, (![A_856, C_858, E_857]: (v1_funct_1(k1_tmap_1(A_856, '#skF_2', C_858, '#skF_4', E_857, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_857, k1_zfmisc_1(k2_zfmisc_1(C_858, '#skF_2'))) | ~v1_funct_2(E_857, C_858, '#skF_2') | ~v1_funct_1(E_857) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_856)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_858, k1_zfmisc_1(A_856)) | v1_xboole_0(C_858) | v1_xboole_0('#skF_2') | v1_xboole_0(A_856))), inference(resolution, [status(thm)], [c_52, c_4710])).
% 8.20/3.11  tff(c_4721, plain, (![A_856, C_858, E_857]: (v1_funct_1(k1_tmap_1(A_856, '#skF_2', C_858, '#skF_4', E_857, '#skF_6')) | ~m1_subset_1(E_857, k1_zfmisc_1(k2_zfmisc_1(C_858, '#skF_2'))) | ~v1_funct_2(E_857, C_858, '#skF_2') | ~v1_funct_1(E_857) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_856)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_858, k1_zfmisc_1(A_856)) | v1_xboole_0(C_858) | v1_xboole_0('#skF_2') | v1_xboole_0(A_856))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_4714])).
% 8.20/3.11  tff(c_4797, plain, (![A_868, C_869, E_870]: (v1_funct_1(k1_tmap_1(A_868, '#skF_2', C_869, '#skF_4', E_870, '#skF_6')) | ~m1_subset_1(E_870, k1_zfmisc_1(k2_zfmisc_1(C_869, '#skF_2'))) | ~v1_funct_2(E_870, C_869, '#skF_2') | ~v1_funct_1(E_870) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_868)) | ~m1_subset_1(C_869, k1_zfmisc_1(A_868)) | v1_xboole_0(C_869) | v1_xboole_0(A_868))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_4721])).
% 8.20/3.11  tff(c_4799, plain, (![A_868]: (v1_funct_1(k1_tmap_1(A_868, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_868)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_868)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_868))), inference(resolution, [status(thm)], [c_58, c_4797])).
% 8.20/3.11  tff(c_4804, plain, (![A_868]: (v1_funct_1(k1_tmap_1(A_868, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_868)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_868)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_868))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_4799])).
% 8.20/3.11  tff(c_4818, plain, (![A_878]: (v1_funct_1(k1_tmap_1(A_878, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_878)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_878)) | v1_xboole_0(A_878))), inference(negUnitSimplification, [status(thm)], [c_72, c_4804])).
% 8.20/3.11  tff(c_4821, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_70, c_4818])).
% 8.20/3.11  tff(c_4824, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_4821])).
% 8.20/3.11  tff(c_4825, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_76, c_4824])).
% 8.20/3.11  tff(c_4468, plain, (![A_828, B_829, C_830, D_831]: (k2_partfun1(A_828, B_829, C_830, D_831)=k7_relat_1(C_830, D_831) | ~m1_subset_1(C_830, k1_zfmisc_1(k2_zfmisc_1(A_828, B_829))) | ~v1_funct_1(C_830))), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.20/3.11  tff(c_4470, plain, (![D_831]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_831)=k7_relat_1('#skF_5', D_831) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_58, c_4468])).
% 8.20/3.11  tff(c_4475, plain, (![D_831]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_831)=k7_relat_1('#skF_5', D_831))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_4470])).
% 8.20/3.11  tff(c_4472, plain, (![D_831]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_831)=k7_relat_1('#skF_6', D_831) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_52, c_4468])).
% 8.20/3.11  tff(c_4478, plain, (![D_831]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_831)=k7_relat_1('#skF_6', D_831))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_4472])).
% 8.20/3.11  tff(c_46, plain, (![E_166, F_167, B_163, D_165, A_162, C_164]: (v1_funct_2(k1_tmap_1(A_162, B_163, C_164, D_165, E_166, F_167), k4_subset_1(A_162, C_164, D_165), B_163) | ~m1_subset_1(F_167, k1_zfmisc_1(k2_zfmisc_1(D_165, B_163))) | ~v1_funct_2(F_167, D_165, B_163) | ~v1_funct_1(F_167) | ~m1_subset_1(E_166, k1_zfmisc_1(k2_zfmisc_1(C_164, B_163))) | ~v1_funct_2(E_166, C_164, B_163) | ~v1_funct_1(E_166) | ~m1_subset_1(D_165, k1_zfmisc_1(A_162)) | v1_xboole_0(D_165) | ~m1_subset_1(C_164, k1_zfmisc_1(A_162)) | v1_xboole_0(C_164) | v1_xboole_0(B_163) | v1_xboole_0(A_162))), inference(cnfTransformation, [status(thm)], [f_188])).
% 8.20/3.11  tff(c_44, plain, (![E_166, F_167, B_163, D_165, A_162, C_164]: (m1_subset_1(k1_tmap_1(A_162, B_163, C_164, D_165, E_166, F_167), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_162, C_164, D_165), B_163))) | ~m1_subset_1(F_167, k1_zfmisc_1(k2_zfmisc_1(D_165, B_163))) | ~v1_funct_2(F_167, D_165, B_163) | ~v1_funct_1(F_167) | ~m1_subset_1(E_166, k1_zfmisc_1(k2_zfmisc_1(C_164, B_163))) | ~v1_funct_2(E_166, C_164, B_163) | ~v1_funct_1(E_166) | ~m1_subset_1(D_165, k1_zfmisc_1(A_162)) | v1_xboole_0(D_165) | ~m1_subset_1(C_164, k1_zfmisc_1(A_162)) | v1_xboole_0(C_164) | v1_xboole_0(B_163) | v1_xboole_0(A_162))), inference(cnfTransformation, [status(thm)], [f_188])).
% 8.20/3.11  tff(c_4920, plain, (![E_897, C_900, A_896, B_898, F_895, D_899]: (k2_partfun1(k4_subset_1(A_896, C_900, D_899), B_898, k1_tmap_1(A_896, B_898, C_900, D_899, E_897, F_895), C_900)=E_897 | ~m1_subset_1(k1_tmap_1(A_896, B_898, C_900, D_899, E_897, F_895), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_896, C_900, D_899), B_898))) | ~v1_funct_2(k1_tmap_1(A_896, B_898, C_900, D_899, E_897, F_895), k4_subset_1(A_896, C_900, D_899), B_898) | ~v1_funct_1(k1_tmap_1(A_896, B_898, C_900, D_899, E_897, F_895)) | k2_partfun1(D_899, B_898, F_895, k9_subset_1(A_896, C_900, D_899))!=k2_partfun1(C_900, B_898, E_897, k9_subset_1(A_896, C_900, D_899)) | ~m1_subset_1(F_895, k1_zfmisc_1(k2_zfmisc_1(D_899, B_898))) | ~v1_funct_2(F_895, D_899, B_898) | ~v1_funct_1(F_895) | ~m1_subset_1(E_897, k1_zfmisc_1(k2_zfmisc_1(C_900, B_898))) | ~v1_funct_2(E_897, C_900, B_898) | ~v1_funct_1(E_897) | ~m1_subset_1(D_899, k1_zfmisc_1(A_896)) | v1_xboole_0(D_899) | ~m1_subset_1(C_900, k1_zfmisc_1(A_896)) | v1_xboole_0(C_900) | v1_xboole_0(B_898) | v1_xboole_0(A_896))), inference(cnfTransformation, [status(thm)], [f_154])).
% 8.20/3.11  tff(c_5311, plain, (![D_1008, B_1006, F_1007, E_1010, A_1009, C_1011]: (k2_partfun1(k4_subset_1(A_1009, C_1011, D_1008), B_1006, k1_tmap_1(A_1009, B_1006, C_1011, D_1008, E_1010, F_1007), C_1011)=E_1010 | ~v1_funct_2(k1_tmap_1(A_1009, B_1006, C_1011, D_1008, E_1010, F_1007), k4_subset_1(A_1009, C_1011, D_1008), B_1006) | ~v1_funct_1(k1_tmap_1(A_1009, B_1006, C_1011, D_1008, E_1010, F_1007)) | k2_partfun1(D_1008, B_1006, F_1007, k9_subset_1(A_1009, C_1011, D_1008))!=k2_partfun1(C_1011, B_1006, E_1010, k9_subset_1(A_1009, C_1011, D_1008)) | ~m1_subset_1(F_1007, k1_zfmisc_1(k2_zfmisc_1(D_1008, B_1006))) | ~v1_funct_2(F_1007, D_1008, B_1006) | ~v1_funct_1(F_1007) | ~m1_subset_1(E_1010, k1_zfmisc_1(k2_zfmisc_1(C_1011, B_1006))) | ~v1_funct_2(E_1010, C_1011, B_1006) | ~v1_funct_1(E_1010) | ~m1_subset_1(D_1008, k1_zfmisc_1(A_1009)) | v1_xboole_0(D_1008) | ~m1_subset_1(C_1011, k1_zfmisc_1(A_1009)) | v1_xboole_0(C_1011) | v1_xboole_0(B_1006) | v1_xboole_0(A_1009))), inference(resolution, [status(thm)], [c_44, c_4920])).
% 8.20/3.11  tff(c_5741, plain, (![A_1060, C_1062, E_1061, B_1057, D_1059, F_1058]: (k2_partfun1(k4_subset_1(A_1060, C_1062, D_1059), B_1057, k1_tmap_1(A_1060, B_1057, C_1062, D_1059, E_1061, F_1058), C_1062)=E_1061 | ~v1_funct_1(k1_tmap_1(A_1060, B_1057, C_1062, D_1059, E_1061, F_1058)) | k2_partfun1(D_1059, B_1057, F_1058, k9_subset_1(A_1060, C_1062, D_1059))!=k2_partfun1(C_1062, B_1057, E_1061, k9_subset_1(A_1060, C_1062, D_1059)) | ~m1_subset_1(F_1058, k1_zfmisc_1(k2_zfmisc_1(D_1059, B_1057))) | ~v1_funct_2(F_1058, D_1059, B_1057) | ~v1_funct_1(F_1058) | ~m1_subset_1(E_1061, k1_zfmisc_1(k2_zfmisc_1(C_1062, B_1057))) | ~v1_funct_2(E_1061, C_1062, B_1057) | ~v1_funct_1(E_1061) | ~m1_subset_1(D_1059, k1_zfmisc_1(A_1060)) | v1_xboole_0(D_1059) | ~m1_subset_1(C_1062, k1_zfmisc_1(A_1060)) | v1_xboole_0(C_1062) | v1_xboole_0(B_1057) | v1_xboole_0(A_1060))), inference(resolution, [status(thm)], [c_46, c_5311])).
% 8.20/3.11  tff(c_5747, plain, (![A_1060, C_1062, E_1061]: (k2_partfun1(k4_subset_1(A_1060, C_1062, '#skF_4'), '#skF_2', k1_tmap_1(A_1060, '#skF_2', C_1062, '#skF_4', E_1061, '#skF_6'), C_1062)=E_1061 | ~v1_funct_1(k1_tmap_1(A_1060, '#skF_2', C_1062, '#skF_4', E_1061, '#skF_6')) | k2_partfun1(C_1062, '#skF_2', E_1061, k9_subset_1(A_1060, C_1062, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_1060, C_1062, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1061, k1_zfmisc_1(k2_zfmisc_1(C_1062, '#skF_2'))) | ~v1_funct_2(E_1061, C_1062, '#skF_2') | ~v1_funct_1(E_1061) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1060)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1062, k1_zfmisc_1(A_1060)) | v1_xboole_0(C_1062) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1060))), inference(resolution, [status(thm)], [c_52, c_5741])).
% 8.20/3.11  tff(c_5755, plain, (![A_1060, C_1062, E_1061]: (k2_partfun1(k4_subset_1(A_1060, C_1062, '#skF_4'), '#skF_2', k1_tmap_1(A_1060, '#skF_2', C_1062, '#skF_4', E_1061, '#skF_6'), C_1062)=E_1061 | ~v1_funct_1(k1_tmap_1(A_1060, '#skF_2', C_1062, '#skF_4', E_1061, '#skF_6')) | k2_partfun1(C_1062, '#skF_2', E_1061, k9_subset_1(A_1060, C_1062, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1060, C_1062, '#skF_4')) | ~m1_subset_1(E_1061, k1_zfmisc_1(k2_zfmisc_1(C_1062, '#skF_2'))) | ~v1_funct_2(E_1061, C_1062, '#skF_2') | ~v1_funct_1(E_1061) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1060)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1062, k1_zfmisc_1(A_1060)) | v1_xboole_0(C_1062) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1060))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_4478, c_5747])).
% 8.20/3.11  tff(c_5854, plain, (![A_1092, C_1093, E_1094]: (k2_partfun1(k4_subset_1(A_1092, C_1093, '#skF_4'), '#skF_2', k1_tmap_1(A_1092, '#skF_2', C_1093, '#skF_4', E_1094, '#skF_6'), C_1093)=E_1094 | ~v1_funct_1(k1_tmap_1(A_1092, '#skF_2', C_1093, '#skF_4', E_1094, '#skF_6')) | k2_partfun1(C_1093, '#skF_2', E_1094, k9_subset_1(A_1092, C_1093, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1092, C_1093, '#skF_4')) | ~m1_subset_1(E_1094, k1_zfmisc_1(k2_zfmisc_1(C_1093, '#skF_2'))) | ~v1_funct_2(E_1094, C_1093, '#skF_2') | ~v1_funct_1(E_1094) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1092)) | ~m1_subset_1(C_1093, k1_zfmisc_1(A_1092)) | v1_xboole_0(C_1093) | v1_xboole_0(A_1092))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_5755])).
% 8.20/3.11  tff(c_5859, plain, (![A_1092]: (k2_partfun1(k4_subset_1(A_1092, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1092, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1092, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_1092, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1092, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1092)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1092)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1092))), inference(resolution, [status(thm)], [c_58, c_5854])).
% 8.20/3.11  tff(c_5867, plain, (![A_1092]: (k2_partfun1(k4_subset_1(A_1092, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1092, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1092, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1092, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1092, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1092)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1092)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1092))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_4475, c_5859])).
% 8.20/3.11  tff(c_6149, plain, (![A_1122]: (k2_partfun1(k4_subset_1(A_1122, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1122, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1122, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1122, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1122, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1122)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1122)) | v1_xboole_0(A_1122))), inference(negUnitSimplification, [status(thm)], [c_72, c_5867])).
% 8.20/3.11  tff(c_568, plain, (![A_304, B_305]: (k7_relat_1(A_304, B_305)=k1_xboole_0 | ~r1_xboole_0(B_305, k1_relat_1(A_304)) | ~v1_relat_1(A_304))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.20/3.11  tff(c_589, plain, (![A_306]: (k7_relat_1(A_306, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_306))), inference(resolution, [status(thm)], [c_82, c_568])).
% 8.20/3.11  tff(c_599, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_478, c_589])).
% 8.20/3.11  tff(c_600, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_475, c_589])).
% 8.20/3.11  tff(c_1661, plain, (![A_399, B_400]: (k3_xboole_0(A_399, B_400)=k1_xboole_0 | ~r1_subset_1(A_399, B_400) | v1_xboole_0(B_400) | v1_xboole_0(A_399))), inference(resolution, [status(thm)], [c_535, c_2])).
% 8.20/3.11  tff(c_1667, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_64, c_1661])).
% 8.20/3.11  tff(c_1673, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_72, c_68, c_1667])).
% 8.20/3.11  tff(c_606, plain, (![A_307, B_308, C_309]: (k9_subset_1(A_307, B_308, C_309)=k3_xboole_0(B_308, C_309) | ~m1_subset_1(C_309, k1_zfmisc_1(A_307)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.20/3.11  tff(c_618, plain, (![B_308]: (k9_subset_1('#skF_1', B_308, '#skF_4')=k3_xboole_0(B_308, '#skF_4'))), inference(resolution, [status(thm)], [c_66, c_606])).
% 8.20/3.11  tff(c_1876, plain, (![F_423, C_427, D_424, B_422, A_425, E_426]: (v1_funct_1(k1_tmap_1(A_425, B_422, C_427, D_424, E_426, F_423)) | ~m1_subset_1(F_423, k1_zfmisc_1(k2_zfmisc_1(D_424, B_422))) | ~v1_funct_2(F_423, D_424, B_422) | ~v1_funct_1(F_423) | ~m1_subset_1(E_426, k1_zfmisc_1(k2_zfmisc_1(C_427, B_422))) | ~v1_funct_2(E_426, C_427, B_422) | ~v1_funct_1(E_426) | ~m1_subset_1(D_424, k1_zfmisc_1(A_425)) | v1_xboole_0(D_424) | ~m1_subset_1(C_427, k1_zfmisc_1(A_425)) | v1_xboole_0(C_427) | v1_xboole_0(B_422) | v1_xboole_0(A_425))), inference(cnfTransformation, [status(thm)], [f_188])).
% 8.20/3.11  tff(c_1880, plain, (![A_425, C_427, E_426]: (v1_funct_1(k1_tmap_1(A_425, '#skF_2', C_427, '#skF_4', E_426, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_426, k1_zfmisc_1(k2_zfmisc_1(C_427, '#skF_2'))) | ~v1_funct_2(E_426, C_427, '#skF_2') | ~v1_funct_1(E_426) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_425)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_427, k1_zfmisc_1(A_425)) | v1_xboole_0(C_427) | v1_xboole_0('#skF_2') | v1_xboole_0(A_425))), inference(resolution, [status(thm)], [c_52, c_1876])).
% 8.20/3.11  tff(c_1887, plain, (![A_425, C_427, E_426]: (v1_funct_1(k1_tmap_1(A_425, '#skF_2', C_427, '#skF_4', E_426, '#skF_6')) | ~m1_subset_1(E_426, k1_zfmisc_1(k2_zfmisc_1(C_427, '#skF_2'))) | ~v1_funct_2(E_426, C_427, '#skF_2') | ~v1_funct_1(E_426) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_425)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_427, k1_zfmisc_1(A_425)) | v1_xboole_0(C_427) | v1_xboole_0('#skF_2') | v1_xboole_0(A_425))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_1880])).
% 8.20/3.11  tff(c_1912, plain, (![A_430, C_431, E_432]: (v1_funct_1(k1_tmap_1(A_430, '#skF_2', C_431, '#skF_4', E_432, '#skF_6')) | ~m1_subset_1(E_432, k1_zfmisc_1(k2_zfmisc_1(C_431, '#skF_2'))) | ~v1_funct_2(E_432, C_431, '#skF_2') | ~v1_funct_1(E_432) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_430)) | ~m1_subset_1(C_431, k1_zfmisc_1(A_430)) | v1_xboole_0(C_431) | v1_xboole_0(A_430))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_1887])).
% 8.20/3.11  tff(c_1914, plain, (![A_430]: (v1_funct_1(k1_tmap_1(A_430, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_430)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_430)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_430))), inference(resolution, [status(thm)], [c_58, c_1912])).
% 8.20/3.11  tff(c_1919, plain, (![A_430]: (v1_funct_1(k1_tmap_1(A_430, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_430)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_430)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_430))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1914])).
% 8.20/3.11  tff(c_1932, plain, (![A_434]: (v1_funct_1(k1_tmap_1(A_434, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_434)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_434)) | v1_xboole_0(A_434))), inference(negUnitSimplification, [status(thm)], [c_72, c_1919])).
% 8.20/3.11  tff(c_1935, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_70, c_1932])).
% 8.20/3.11  tff(c_1938, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1935])).
% 8.20/3.11  tff(c_1939, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_76, c_1938])).
% 8.20/3.11  tff(c_1682, plain, (![A_401, B_402, C_403, D_404]: (k2_partfun1(A_401, B_402, C_403, D_404)=k7_relat_1(C_403, D_404) | ~m1_subset_1(C_403, k1_zfmisc_1(k2_zfmisc_1(A_401, B_402))) | ~v1_funct_1(C_403))), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.20/3.11  tff(c_1684, plain, (![D_404]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_404)=k7_relat_1('#skF_5', D_404) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_58, c_1682])).
% 8.20/3.11  tff(c_1689, plain, (![D_404]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_404)=k7_relat_1('#skF_5', D_404))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1684])).
% 8.20/3.11  tff(c_1686, plain, (![D_404]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_404)=k7_relat_1('#skF_6', D_404) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_52, c_1682])).
% 8.20/3.11  tff(c_1692, plain, (![D_404]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_404)=k7_relat_1('#skF_6', D_404))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1686])).
% 8.20/3.11  tff(c_2113, plain, (![E_475, C_478, A_474, F_473, D_477, B_476]: (k2_partfun1(k4_subset_1(A_474, C_478, D_477), B_476, k1_tmap_1(A_474, B_476, C_478, D_477, E_475, F_473), D_477)=F_473 | ~m1_subset_1(k1_tmap_1(A_474, B_476, C_478, D_477, E_475, F_473), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_474, C_478, D_477), B_476))) | ~v1_funct_2(k1_tmap_1(A_474, B_476, C_478, D_477, E_475, F_473), k4_subset_1(A_474, C_478, D_477), B_476) | ~v1_funct_1(k1_tmap_1(A_474, B_476, C_478, D_477, E_475, F_473)) | k2_partfun1(D_477, B_476, F_473, k9_subset_1(A_474, C_478, D_477))!=k2_partfun1(C_478, B_476, E_475, k9_subset_1(A_474, C_478, D_477)) | ~m1_subset_1(F_473, k1_zfmisc_1(k2_zfmisc_1(D_477, B_476))) | ~v1_funct_2(F_473, D_477, B_476) | ~v1_funct_1(F_473) | ~m1_subset_1(E_475, k1_zfmisc_1(k2_zfmisc_1(C_478, B_476))) | ~v1_funct_2(E_475, C_478, B_476) | ~v1_funct_1(E_475) | ~m1_subset_1(D_477, k1_zfmisc_1(A_474)) | v1_xboole_0(D_477) | ~m1_subset_1(C_478, k1_zfmisc_1(A_474)) | v1_xboole_0(C_478) | v1_xboole_0(B_476) | v1_xboole_0(A_474))), inference(cnfTransformation, [status(thm)], [f_154])).
% 8.20/3.11  tff(c_2634, plain, (![E_594, C_595, B_590, D_592, F_591, A_593]: (k2_partfun1(k4_subset_1(A_593, C_595, D_592), B_590, k1_tmap_1(A_593, B_590, C_595, D_592, E_594, F_591), D_592)=F_591 | ~v1_funct_2(k1_tmap_1(A_593, B_590, C_595, D_592, E_594, F_591), k4_subset_1(A_593, C_595, D_592), B_590) | ~v1_funct_1(k1_tmap_1(A_593, B_590, C_595, D_592, E_594, F_591)) | k2_partfun1(D_592, B_590, F_591, k9_subset_1(A_593, C_595, D_592))!=k2_partfun1(C_595, B_590, E_594, k9_subset_1(A_593, C_595, D_592)) | ~m1_subset_1(F_591, k1_zfmisc_1(k2_zfmisc_1(D_592, B_590))) | ~v1_funct_2(F_591, D_592, B_590) | ~v1_funct_1(F_591) | ~m1_subset_1(E_594, k1_zfmisc_1(k2_zfmisc_1(C_595, B_590))) | ~v1_funct_2(E_594, C_595, B_590) | ~v1_funct_1(E_594) | ~m1_subset_1(D_592, k1_zfmisc_1(A_593)) | v1_xboole_0(D_592) | ~m1_subset_1(C_595, k1_zfmisc_1(A_593)) | v1_xboole_0(C_595) | v1_xboole_0(B_590) | v1_xboole_0(A_593))), inference(resolution, [status(thm)], [c_44, c_2113])).
% 8.20/3.11  tff(c_2848, plain, (![F_625, B_624, D_626, E_628, A_627, C_629]: (k2_partfun1(k4_subset_1(A_627, C_629, D_626), B_624, k1_tmap_1(A_627, B_624, C_629, D_626, E_628, F_625), D_626)=F_625 | ~v1_funct_1(k1_tmap_1(A_627, B_624, C_629, D_626, E_628, F_625)) | k2_partfun1(D_626, B_624, F_625, k9_subset_1(A_627, C_629, D_626))!=k2_partfun1(C_629, B_624, E_628, k9_subset_1(A_627, C_629, D_626)) | ~m1_subset_1(F_625, k1_zfmisc_1(k2_zfmisc_1(D_626, B_624))) | ~v1_funct_2(F_625, D_626, B_624) | ~v1_funct_1(F_625) | ~m1_subset_1(E_628, k1_zfmisc_1(k2_zfmisc_1(C_629, B_624))) | ~v1_funct_2(E_628, C_629, B_624) | ~v1_funct_1(E_628) | ~m1_subset_1(D_626, k1_zfmisc_1(A_627)) | v1_xboole_0(D_626) | ~m1_subset_1(C_629, k1_zfmisc_1(A_627)) | v1_xboole_0(C_629) | v1_xboole_0(B_624) | v1_xboole_0(A_627))), inference(resolution, [status(thm)], [c_46, c_2634])).
% 8.20/3.11  tff(c_2854, plain, (![A_627, C_629, E_628]: (k2_partfun1(k4_subset_1(A_627, C_629, '#skF_4'), '#skF_2', k1_tmap_1(A_627, '#skF_2', C_629, '#skF_4', E_628, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_627, '#skF_2', C_629, '#skF_4', E_628, '#skF_6')) | k2_partfun1(C_629, '#skF_2', E_628, k9_subset_1(A_627, C_629, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_627, C_629, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_628, k1_zfmisc_1(k2_zfmisc_1(C_629, '#skF_2'))) | ~v1_funct_2(E_628, C_629, '#skF_2') | ~v1_funct_1(E_628) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_627)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_629, k1_zfmisc_1(A_627)) | v1_xboole_0(C_629) | v1_xboole_0('#skF_2') | v1_xboole_0(A_627))), inference(resolution, [status(thm)], [c_52, c_2848])).
% 8.20/3.11  tff(c_2862, plain, (![A_627, C_629, E_628]: (k2_partfun1(k4_subset_1(A_627, C_629, '#skF_4'), '#skF_2', k1_tmap_1(A_627, '#skF_2', C_629, '#skF_4', E_628, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_627, '#skF_2', C_629, '#skF_4', E_628, '#skF_6')) | k2_partfun1(C_629, '#skF_2', E_628, k9_subset_1(A_627, C_629, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_627, C_629, '#skF_4')) | ~m1_subset_1(E_628, k1_zfmisc_1(k2_zfmisc_1(C_629, '#skF_2'))) | ~v1_funct_2(E_628, C_629, '#skF_2') | ~v1_funct_1(E_628) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_627)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_629, k1_zfmisc_1(A_627)) | v1_xboole_0(C_629) | v1_xboole_0('#skF_2') | v1_xboole_0(A_627))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_1692, c_2854])).
% 8.20/3.11  tff(c_3203, plain, (![A_697, C_698, E_699]: (k2_partfun1(k4_subset_1(A_697, C_698, '#skF_4'), '#skF_2', k1_tmap_1(A_697, '#skF_2', C_698, '#skF_4', E_699, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_697, '#skF_2', C_698, '#skF_4', E_699, '#skF_6')) | k2_partfun1(C_698, '#skF_2', E_699, k9_subset_1(A_697, C_698, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_697, C_698, '#skF_4')) | ~m1_subset_1(E_699, k1_zfmisc_1(k2_zfmisc_1(C_698, '#skF_2'))) | ~v1_funct_2(E_699, C_698, '#skF_2') | ~v1_funct_1(E_699) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_697)) | ~m1_subset_1(C_698, k1_zfmisc_1(A_697)) | v1_xboole_0(C_698) | v1_xboole_0(A_697))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_2862])).
% 8.20/3.11  tff(c_3208, plain, (![A_697]: (k2_partfun1(k4_subset_1(A_697, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_697, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_697, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_697, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_697, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_697)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_697)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_697))), inference(resolution, [status(thm)], [c_58, c_3203])).
% 8.20/3.11  tff(c_3216, plain, (![A_697]: (k2_partfun1(k4_subset_1(A_697, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_697, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_697, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_697, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_697, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_697)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_697)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_697))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1689, c_3208])).
% 8.20/3.11  tff(c_3238, plain, (![A_701]: (k2_partfun1(k4_subset_1(A_701, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_701, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_701, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_701, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_701, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_701)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_701)) | v1_xboole_0(A_701))), inference(negUnitSimplification, [status(thm)], [c_72, c_3216])).
% 8.20/3.11  tff(c_136, plain, (![B_239, A_240]: (v1_relat_1(B_239) | ~m1_subset_1(B_239, k1_zfmisc_1(A_240)) | ~v1_relat_1(A_240))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.20/3.11  tff(c_139, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_136])).
% 8.20/3.11  tff(c_151, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_139])).
% 8.20/3.11  tff(c_215, plain, (![A_254, B_255]: (k7_relat_1(A_254, B_255)=k1_xboole_0 | ~r1_xboole_0(B_255, k1_relat_1(A_254)) | ~v1_relat_1(A_254))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.20/3.11  tff(c_236, plain, (![A_256]: (k7_relat_1(A_256, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_256))), inference(resolution, [status(thm)], [c_82, c_215])).
% 8.20/3.11  tff(c_247, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_151, c_236])).
% 8.20/3.11  tff(c_142, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_136])).
% 8.20/3.11  tff(c_154, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_142])).
% 8.20/3.11  tff(c_246, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_154, c_236])).
% 8.20/3.11  tff(c_207, plain, (![A_252, B_253]: (r1_xboole_0(A_252, B_253) | ~r1_subset_1(A_252, B_253) | v1_xboole_0(B_253) | v1_xboole_0(A_252))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.20/3.11  tff(c_410, plain, (![A_280, B_281]: (k3_xboole_0(A_280, B_281)=k1_xboole_0 | ~r1_subset_1(A_280, B_281) | v1_xboole_0(B_281) | v1_xboole_0(A_280))), inference(resolution, [status(thm)], [c_207, c_2])).
% 8.20/3.11  tff(c_416, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_64, c_410])).
% 8.20/3.11  tff(c_422, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_72, c_68, c_416])).
% 8.20/3.11  tff(c_371, plain, (![A_273, B_274, C_275, D_276]: (k2_partfun1(A_273, B_274, C_275, D_276)=k7_relat_1(C_275, D_276) | ~m1_subset_1(C_275, k1_zfmisc_1(k2_zfmisc_1(A_273, B_274))) | ~v1_funct_1(C_275))), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.20/3.11  tff(c_375, plain, (![D_276]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_276)=k7_relat_1('#skF_6', D_276) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_52, c_371])).
% 8.20/3.11  tff(c_381, plain, (![D_276]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_276)=k7_relat_1('#skF_6', D_276))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_375])).
% 8.20/3.11  tff(c_373, plain, (![D_276]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_276)=k7_relat_1('#skF_5', D_276) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_58, c_371])).
% 8.20/3.11  tff(c_378, plain, (![D_276]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_276)=k7_relat_1('#skF_5', D_276))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_373])).
% 8.20/3.11  tff(c_330, plain, (![A_267, B_268, C_269]: (k9_subset_1(A_267, B_268, C_269)=k3_xboole_0(B_268, C_269) | ~m1_subset_1(C_269, k1_zfmisc_1(A_267)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.20/3.11  tff(c_342, plain, (![B_268]: (k9_subset_1('#skF_1', B_268, '#skF_4')=k3_xboole_0(B_268, '#skF_4'))), inference(resolution, [status(thm)], [c_66, c_330])).
% 8.20/3.11  tff(c_50, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.20/3.11  tff(c_104, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_50])).
% 8.20/3.11  tff(c_352, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_342, c_342, c_104])).
% 8.20/3.11  tff(c_409, plain, (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_381, c_378, c_352])).
% 8.20/3.11  tff(c_423, plain, (k7_relat_1('#skF_5', k1_xboole_0)!=k7_relat_1('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_422, c_422, c_409])).
% 8.20/3.11  tff(c_426, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_247, c_246, c_423])).
% 8.20/3.11  tff(c_427, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_50])).
% 8.20/3.11  tff(c_566, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_427])).
% 8.20/3.11  tff(c_3249, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3238, c_566])).
% 8.20/3.11  tff(c_3263, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_599, c_600, c_1673, c_618, c_1673, c_618, c_1939, c_3249])).
% 8.20/3.11  tff(c_3265, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_3263])).
% 8.20/3.11  tff(c_3266, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_427])).
% 8.20/3.11  tff(c_6158, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6149, c_3266])).
% 8.20/3.11  tff(c_6169, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_3304, c_3305, c_4623, c_4342, c_4623, c_4342, c_4825, c_6158])).
% 8.20/3.11  tff(c_6171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_6169])).
% 8.20/3.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.20/3.11  
% 8.20/3.11  Inference rules
% 8.20/3.11  ----------------------
% 8.20/3.11  #Ref     : 0
% 8.20/3.11  #Sup     : 1248
% 8.20/3.11  #Fact    : 0
% 8.20/3.11  #Define  : 0
% 8.20/3.11  #Split   : 49
% 8.20/3.11  #Chain   : 0
% 8.20/3.11  #Close   : 0
% 8.20/3.11  
% 8.20/3.11  Ordering : KBO
% 8.20/3.11  
% 8.20/3.11  Simplification rules
% 8.20/3.11  ----------------------
% 8.20/3.11  #Subsume      : 145
% 8.20/3.11  #Demod        : 861
% 8.20/3.11  #Tautology    : 622
% 8.20/3.11  #SimpNegUnit  : 293
% 8.20/3.11  #BackRed      : 12
% 8.20/3.11  
% 8.20/3.11  #Partial instantiations: 0
% 8.20/3.11  #Strategies tried      : 1
% 8.20/3.11  
% 8.20/3.11  Timing (in seconds)
% 8.20/3.11  ----------------------
% 8.20/3.11  Preprocessing        : 0.43
% 8.20/3.11  Parsing              : 0.22
% 8.20/3.11  CNF conversion       : 0.06
% 8.20/3.11  Main loop            : 1.81
% 8.20/3.11  Inferencing          : 0.63
% 8.20/3.11  Reduction            : 0.60
% 8.20/3.11  Demodulation         : 0.43
% 8.20/3.11  BG Simplification    : 0.06
% 8.20/3.11  Subsumption          : 0.41
% 8.20/3.11  Abstraction          : 0.08
% 8.20/3.12  MUC search           : 0.00
% 8.20/3.12  Cooper               : 0.00
% 8.20/3.12  Total                : 2.30
% 8.20/3.12  Index Insertion      : 0.00
% 8.20/3.12  Index Deletion       : 0.00
% 8.20/3.12  Index Matching       : 0.00
% 8.20/3.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
