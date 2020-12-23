%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:22 EST 2020

% Result     : Theorem 5.62s
% Output     : CNFRefutation 5.84s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 452 expanded)
%              Number of leaves         :   41 ( 184 expanded)
%              Depth                    :   12
%              Number of atoms          :  593 (2516 expanded)
%              Number of equality atoms :   98 ( 444 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k2_enumset1 > k9_subset_1 > k4_subset_1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_208,negated_conjecture,(
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

tff(f_68,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_30,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_xboole_0(B) )
     => ( v1_xboole_0(k7_relat_1(A,B))
        & v1_relat_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc16_relat_1)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_78,axiom,(
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

tff(f_42,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_166,axiom,(
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

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_132,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_26,plain,(
    ! [A_22,B_23] : v1_relat_1(k2_zfmisc_1(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_494,plain,(
    ! [B_277,A_278] :
      ( v1_relat_1(B_277)
      | ~ m1_subset_1(B_277,k1_zfmisc_1(A_278))
      | ~ v1_relat_1(A_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_497,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_494])).

tff(c_509,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_497])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_518,plain,(
    ! [A_281,B_282] :
      ( v1_xboole_0(k7_relat_1(A_281,B_282))
      | ~ v1_xboole_0(B_282)
      | ~ v1_relat_1(A_281) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_532,plain,(
    ! [A_286,B_287] :
      ( k7_relat_1(A_286,B_287) = k1_xboole_0
      | ~ v1_xboole_0(B_287)
      | ~ v1_relat_1(A_286) ) ),
    inference(resolution,[status(thm)],[c_518,c_8])).

tff(c_539,plain,(
    ! [A_288] :
      ( k7_relat_1(A_288,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_288) ) ),
    inference(resolution,[status(thm)],[c_6,c_532])).

tff(c_554,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_509,c_539])).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_60,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_1641,plain,(
    ! [A_469,B_470] :
      ( r1_xboole_0(A_469,B_470)
      | ~ r1_subset_1(A_469,B_470)
      | v1_xboole_0(B_470)
      | v1_xboole_0(A_469) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1749,plain,(
    ! [A_480,B_481] :
      ( k3_xboole_0(A_480,B_481) = k1_xboole_0
      | ~ r1_subset_1(A_480,B_481)
      | v1_xboole_0(B_481)
      | v1_xboole_0(A_480) ) ),
    inference(resolution,[status(thm)],[c_1641,c_2])).

tff(c_1752,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_1749])).

tff(c_1755,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_64,c_1752])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_500,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_54,c_494])).

tff(c_512,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_500])).

tff(c_553,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_512,c_539])).

tff(c_1699,plain,(
    ! [A_473,B_474,C_475] :
      ( k9_subset_1(A_473,B_474,C_475) = k3_xboole_0(B_474,C_475)
      | ~ m1_subset_1(C_475,k1_zfmisc_1(A_473)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1711,plain,(
    ! [B_474] : k9_subset_1('#skF_1',B_474,'#skF_4') = k3_xboole_0(B_474,'#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_1699])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_56,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_52,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_50,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_1869,plain,(
    ! [F_497,E_493,D_494,A_495,B_498,C_496] :
      ( v1_funct_1(k1_tmap_1(A_495,B_498,C_496,D_494,E_493,F_497))
      | ~ m1_subset_1(F_497,k1_zfmisc_1(k2_zfmisc_1(D_494,B_498)))
      | ~ v1_funct_2(F_497,D_494,B_498)
      | ~ v1_funct_1(F_497)
      | ~ m1_subset_1(E_493,k1_zfmisc_1(k2_zfmisc_1(C_496,B_498)))
      | ~ v1_funct_2(E_493,C_496,B_498)
      | ~ v1_funct_1(E_493)
      | ~ m1_subset_1(D_494,k1_zfmisc_1(A_495))
      | v1_xboole_0(D_494)
      | ~ m1_subset_1(C_496,k1_zfmisc_1(A_495))
      | v1_xboole_0(C_496)
      | v1_xboole_0(B_498)
      | v1_xboole_0(A_495) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_1871,plain,(
    ! [A_495,C_496,E_493] :
      ( v1_funct_1(k1_tmap_1(A_495,'#skF_2',C_496,'#skF_4',E_493,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_493,k1_zfmisc_1(k2_zfmisc_1(C_496,'#skF_2')))
      | ~ v1_funct_2(E_493,C_496,'#skF_2')
      | ~ v1_funct_1(E_493)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_495))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_496,k1_zfmisc_1(A_495))
      | v1_xboole_0(C_496)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_495) ) ),
    inference(resolution,[status(thm)],[c_48,c_1869])).

tff(c_1876,plain,(
    ! [A_495,C_496,E_493] :
      ( v1_funct_1(k1_tmap_1(A_495,'#skF_2',C_496,'#skF_4',E_493,'#skF_6'))
      | ~ m1_subset_1(E_493,k1_zfmisc_1(k2_zfmisc_1(C_496,'#skF_2')))
      | ~ v1_funct_2(E_493,C_496,'#skF_2')
      | ~ v1_funct_1(E_493)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_495))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_496,k1_zfmisc_1(A_495))
      | v1_xboole_0(C_496)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_495) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1871])).

tff(c_1882,plain,(
    ! [A_499,C_500,E_501] :
      ( v1_funct_1(k1_tmap_1(A_499,'#skF_2',C_500,'#skF_4',E_501,'#skF_6'))
      | ~ m1_subset_1(E_501,k1_zfmisc_1(k2_zfmisc_1(C_500,'#skF_2')))
      | ~ v1_funct_2(E_501,C_500,'#skF_2')
      | ~ v1_funct_1(E_501)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_499))
      | ~ m1_subset_1(C_500,k1_zfmisc_1(A_499))
      | v1_xboole_0(C_500)
      | v1_xboole_0(A_499) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_1876])).

tff(c_1886,plain,(
    ! [A_499] :
      ( v1_funct_1(k1_tmap_1(A_499,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_499))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_499))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_499) ) ),
    inference(resolution,[status(thm)],[c_54,c_1882])).

tff(c_1893,plain,(
    ! [A_499] :
      ( v1_funct_1(k1_tmap_1(A_499,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_499))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_499))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_499) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1886])).

tff(c_1903,plain,(
    ! [A_509] :
      ( v1_funct_1(k1_tmap_1(A_509,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_509))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_509))
      | v1_xboole_0(A_509) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1893])).

tff(c_1906,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_1903])).

tff(c_1909,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1906])).

tff(c_1910,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1909])).

tff(c_1826,plain,(
    ! [A_487,B_488,C_489,D_490] :
      ( k2_partfun1(A_487,B_488,C_489,D_490) = k7_relat_1(C_489,D_490)
      | ~ m1_subset_1(C_489,k1_zfmisc_1(k2_zfmisc_1(A_487,B_488)))
      | ~ v1_funct_1(C_489) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1830,plain,(
    ! [D_490] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_490) = k7_relat_1('#skF_5',D_490)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_1826])).

tff(c_1836,plain,(
    ! [D_490] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_490) = k7_relat_1('#skF_5',D_490) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1830])).

tff(c_1828,plain,(
    ! [D_490] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_490) = k7_relat_1('#skF_6',D_490)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_48,c_1826])).

tff(c_1833,plain,(
    ! [D_490] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_490) = k7_relat_1('#skF_6',D_490) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1828])).

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
    inference(cnfTransformation,[status(thm)],[f_166])).

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
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_1971,plain,(
    ! [B_521,A_523,C_525,E_522,D_524,F_526] :
      ( k2_partfun1(k4_subset_1(A_523,C_525,D_524),B_521,k1_tmap_1(A_523,B_521,C_525,D_524,E_522,F_526),C_525) = E_522
      | ~ m1_subset_1(k1_tmap_1(A_523,B_521,C_525,D_524,E_522,F_526),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_523,C_525,D_524),B_521)))
      | ~ v1_funct_2(k1_tmap_1(A_523,B_521,C_525,D_524,E_522,F_526),k4_subset_1(A_523,C_525,D_524),B_521)
      | ~ v1_funct_1(k1_tmap_1(A_523,B_521,C_525,D_524,E_522,F_526))
      | k2_partfun1(D_524,B_521,F_526,k9_subset_1(A_523,C_525,D_524)) != k2_partfun1(C_525,B_521,E_522,k9_subset_1(A_523,C_525,D_524))
      | ~ m1_subset_1(F_526,k1_zfmisc_1(k2_zfmisc_1(D_524,B_521)))
      | ~ v1_funct_2(F_526,D_524,B_521)
      | ~ v1_funct_1(F_526)
      | ~ m1_subset_1(E_522,k1_zfmisc_1(k2_zfmisc_1(C_525,B_521)))
      | ~ v1_funct_2(E_522,C_525,B_521)
      | ~ v1_funct_1(E_522)
      | ~ m1_subset_1(D_524,k1_zfmisc_1(A_523))
      | v1_xboole_0(D_524)
      | ~ m1_subset_1(C_525,k1_zfmisc_1(A_523))
      | v1_xboole_0(C_525)
      | v1_xboole_0(B_521)
      | v1_xboole_0(A_523) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_2344,plain,(
    ! [B_595,A_592,E_590,F_594,C_593,D_591] :
      ( k2_partfun1(k4_subset_1(A_592,C_593,D_591),B_595,k1_tmap_1(A_592,B_595,C_593,D_591,E_590,F_594),C_593) = E_590
      | ~ v1_funct_2(k1_tmap_1(A_592,B_595,C_593,D_591,E_590,F_594),k4_subset_1(A_592,C_593,D_591),B_595)
      | ~ v1_funct_1(k1_tmap_1(A_592,B_595,C_593,D_591,E_590,F_594))
      | k2_partfun1(D_591,B_595,F_594,k9_subset_1(A_592,C_593,D_591)) != k2_partfun1(C_593,B_595,E_590,k9_subset_1(A_592,C_593,D_591))
      | ~ m1_subset_1(F_594,k1_zfmisc_1(k2_zfmisc_1(D_591,B_595)))
      | ~ v1_funct_2(F_594,D_591,B_595)
      | ~ v1_funct_1(F_594)
      | ~ m1_subset_1(E_590,k1_zfmisc_1(k2_zfmisc_1(C_593,B_595)))
      | ~ v1_funct_2(E_590,C_593,B_595)
      | ~ v1_funct_1(E_590)
      | ~ m1_subset_1(D_591,k1_zfmisc_1(A_592))
      | v1_xboole_0(D_591)
      | ~ m1_subset_1(C_593,k1_zfmisc_1(A_592))
      | v1_xboole_0(C_593)
      | v1_xboole_0(B_595)
      | v1_xboole_0(A_592) ) ),
    inference(resolution,[status(thm)],[c_40,c_1971])).

tff(c_2348,plain,(
    ! [B_601,A_598,F_600,D_597,C_599,E_596] :
      ( k2_partfun1(k4_subset_1(A_598,C_599,D_597),B_601,k1_tmap_1(A_598,B_601,C_599,D_597,E_596,F_600),C_599) = E_596
      | ~ v1_funct_1(k1_tmap_1(A_598,B_601,C_599,D_597,E_596,F_600))
      | k2_partfun1(D_597,B_601,F_600,k9_subset_1(A_598,C_599,D_597)) != k2_partfun1(C_599,B_601,E_596,k9_subset_1(A_598,C_599,D_597))
      | ~ m1_subset_1(F_600,k1_zfmisc_1(k2_zfmisc_1(D_597,B_601)))
      | ~ v1_funct_2(F_600,D_597,B_601)
      | ~ v1_funct_1(F_600)
      | ~ m1_subset_1(E_596,k1_zfmisc_1(k2_zfmisc_1(C_599,B_601)))
      | ~ v1_funct_2(E_596,C_599,B_601)
      | ~ v1_funct_1(E_596)
      | ~ m1_subset_1(D_597,k1_zfmisc_1(A_598))
      | v1_xboole_0(D_597)
      | ~ m1_subset_1(C_599,k1_zfmisc_1(A_598))
      | v1_xboole_0(C_599)
      | v1_xboole_0(B_601)
      | v1_xboole_0(A_598) ) ),
    inference(resolution,[status(thm)],[c_42,c_2344])).

tff(c_2352,plain,(
    ! [A_598,C_599,E_596] :
      ( k2_partfun1(k4_subset_1(A_598,C_599,'#skF_4'),'#skF_2',k1_tmap_1(A_598,'#skF_2',C_599,'#skF_4',E_596,'#skF_6'),C_599) = E_596
      | ~ v1_funct_1(k1_tmap_1(A_598,'#skF_2',C_599,'#skF_4',E_596,'#skF_6'))
      | k2_partfun1(C_599,'#skF_2',E_596,k9_subset_1(A_598,C_599,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_598,C_599,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_596,k1_zfmisc_1(k2_zfmisc_1(C_599,'#skF_2')))
      | ~ v1_funct_2(E_596,C_599,'#skF_2')
      | ~ v1_funct_1(E_596)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_598))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_599,k1_zfmisc_1(A_598))
      | v1_xboole_0(C_599)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_598) ) ),
    inference(resolution,[status(thm)],[c_48,c_2348])).

tff(c_2358,plain,(
    ! [A_598,C_599,E_596] :
      ( k2_partfun1(k4_subset_1(A_598,C_599,'#skF_4'),'#skF_2',k1_tmap_1(A_598,'#skF_2',C_599,'#skF_4',E_596,'#skF_6'),C_599) = E_596
      | ~ v1_funct_1(k1_tmap_1(A_598,'#skF_2',C_599,'#skF_4',E_596,'#skF_6'))
      | k2_partfun1(C_599,'#skF_2',E_596,k9_subset_1(A_598,C_599,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_598,C_599,'#skF_4'))
      | ~ m1_subset_1(E_596,k1_zfmisc_1(k2_zfmisc_1(C_599,'#skF_2')))
      | ~ v1_funct_2(E_596,C_599,'#skF_2')
      | ~ v1_funct_1(E_596)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_598))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_599,k1_zfmisc_1(A_598))
      | v1_xboole_0(C_599)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_598) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1833,c_2352])).

tff(c_2364,plain,(
    ! [A_602,C_603,E_604] :
      ( k2_partfun1(k4_subset_1(A_602,C_603,'#skF_4'),'#skF_2',k1_tmap_1(A_602,'#skF_2',C_603,'#skF_4',E_604,'#skF_6'),C_603) = E_604
      | ~ v1_funct_1(k1_tmap_1(A_602,'#skF_2',C_603,'#skF_4',E_604,'#skF_6'))
      | k2_partfun1(C_603,'#skF_2',E_604,k9_subset_1(A_602,C_603,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_602,C_603,'#skF_4'))
      | ~ m1_subset_1(E_604,k1_zfmisc_1(k2_zfmisc_1(C_603,'#skF_2')))
      | ~ v1_funct_2(E_604,C_603,'#skF_2')
      | ~ v1_funct_1(E_604)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_602))
      | ~ m1_subset_1(C_603,k1_zfmisc_1(A_602))
      | v1_xboole_0(C_603)
      | v1_xboole_0(A_602) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_2358])).

tff(c_2371,plain,(
    ! [A_602] :
      ( k2_partfun1(k4_subset_1(A_602,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_602,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_602,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_602,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_602,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_602))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_602))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_602) ) ),
    inference(resolution,[status(thm)],[c_54,c_2364])).

tff(c_2381,plain,(
    ! [A_602] :
      ( k2_partfun1(k4_subset_1(A_602,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_602,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_602,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_602,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_602,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_602))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_602))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_602) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1836,c_2371])).

tff(c_2405,plain,(
    ! [A_606] :
      ( k2_partfun1(k4_subset_1(A_606,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_606,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_606,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_606,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_606,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_606))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_606))
      | v1_xboole_0(A_606) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2381])).

tff(c_625,plain,(
    ! [A_293,B_294] :
      ( r1_xboole_0(A_293,B_294)
      | ~ r1_subset_1(A_293,B_294)
      | v1_xboole_0(B_294)
      | v1_xboole_0(A_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_733,plain,(
    ! [A_304,B_305] :
      ( k3_xboole_0(A_304,B_305) = k1_xboole_0
      | ~ r1_subset_1(A_304,B_305)
      | v1_xboole_0(B_305)
      | v1_xboole_0(A_304) ) ),
    inference(resolution,[status(thm)],[c_625,c_2])).

tff(c_736,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_733])).

tff(c_739,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_64,c_736])).

tff(c_683,plain,(
    ! [A_297,B_298,C_299] :
      ( k9_subset_1(A_297,B_298,C_299) = k3_xboole_0(B_298,C_299)
      | ~ m1_subset_1(C_299,k1_zfmisc_1(A_297)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_695,plain,(
    ! [B_298] : k9_subset_1('#skF_1',B_298,'#skF_4') = k3_xboole_0(B_298,'#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_683])).

tff(c_849,plain,(
    ! [C_320,A_319,E_317,B_322,F_321,D_318] :
      ( v1_funct_1(k1_tmap_1(A_319,B_322,C_320,D_318,E_317,F_321))
      | ~ m1_subset_1(F_321,k1_zfmisc_1(k2_zfmisc_1(D_318,B_322)))
      | ~ v1_funct_2(F_321,D_318,B_322)
      | ~ v1_funct_1(F_321)
      | ~ m1_subset_1(E_317,k1_zfmisc_1(k2_zfmisc_1(C_320,B_322)))
      | ~ v1_funct_2(E_317,C_320,B_322)
      | ~ v1_funct_1(E_317)
      | ~ m1_subset_1(D_318,k1_zfmisc_1(A_319))
      | v1_xboole_0(D_318)
      | ~ m1_subset_1(C_320,k1_zfmisc_1(A_319))
      | v1_xboole_0(C_320)
      | v1_xboole_0(B_322)
      | v1_xboole_0(A_319) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_851,plain,(
    ! [A_319,C_320,E_317] :
      ( v1_funct_1(k1_tmap_1(A_319,'#skF_2',C_320,'#skF_4',E_317,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_317,k1_zfmisc_1(k2_zfmisc_1(C_320,'#skF_2')))
      | ~ v1_funct_2(E_317,C_320,'#skF_2')
      | ~ v1_funct_1(E_317)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_319))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_320,k1_zfmisc_1(A_319))
      | v1_xboole_0(C_320)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_319) ) ),
    inference(resolution,[status(thm)],[c_48,c_849])).

tff(c_856,plain,(
    ! [A_319,C_320,E_317] :
      ( v1_funct_1(k1_tmap_1(A_319,'#skF_2',C_320,'#skF_4',E_317,'#skF_6'))
      | ~ m1_subset_1(E_317,k1_zfmisc_1(k2_zfmisc_1(C_320,'#skF_2')))
      | ~ v1_funct_2(E_317,C_320,'#skF_2')
      | ~ v1_funct_1(E_317)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_319))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_320,k1_zfmisc_1(A_319))
      | v1_xboole_0(C_320)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_319) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_851])).

tff(c_862,plain,(
    ! [A_323,C_324,E_325] :
      ( v1_funct_1(k1_tmap_1(A_323,'#skF_2',C_324,'#skF_4',E_325,'#skF_6'))
      | ~ m1_subset_1(E_325,k1_zfmisc_1(k2_zfmisc_1(C_324,'#skF_2')))
      | ~ v1_funct_2(E_325,C_324,'#skF_2')
      | ~ v1_funct_1(E_325)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_323))
      | ~ m1_subset_1(C_324,k1_zfmisc_1(A_323))
      | v1_xboole_0(C_324)
      | v1_xboole_0(A_323) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_856])).

tff(c_866,plain,(
    ! [A_323] :
      ( v1_funct_1(k1_tmap_1(A_323,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_323))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_323))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_323) ) ),
    inference(resolution,[status(thm)],[c_54,c_862])).

tff(c_873,plain,(
    ! [A_323] :
      ( v1_funct_1(k1_tmap_1(A_323,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_323))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_323))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_323) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_866])).

tff(c_883,plain,(
    ! [A_333] :
      ( v1_funct_1(k1_tmap_1(A_333,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_333))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_333))
      | v1_xboole_0(A_333) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_873])).

tff(c_886,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_883])).

tff(c_889,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_886])).

tff(c_890,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_889])).

tff(c_806,plain,(
    ! [A_311,B_312,C_313,D_314] :
      ( k2_partfun1(A_311,B_312,C_313,D_314) = k7_relat_1(C_313,D_314)
      | ~ m1_subset_1(C_313,k1_zfmisc_1(k2_zfmisc_1(A_311,B_312)))
      | ~ v1_funct_1(C_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_810,plain,(
    ! [D_314] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_314) = k7_relat_1('#skF_5',D_314)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_806])).

tff(c_816,plain,(
    ! [D_314] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_314) = k7_relat_1('#skF_5',D_314) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_810])).

tff(c_808,plain,(
    ! [D_314] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_314) = k7_relat_1('#skF_6',D_314)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_48,c_806])).

tff(c_813,plain,(
    ! [D_314] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_314) = k7_relat_1('#skF_6',D_314) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_808])).

tff(c_951,plain,(
    ! [C_349,B_345,A_347,E_346,D_348,F_350] :
      ( k2_partfun1(k4_subset_1(A_347,C_349,D_348),B_345,k1_tmap_1(A_347,B_345,C_349,D_348,E_346,F_350),D_348) = F_350
      | ~ m1_subset_1(k1_tmap_1(A_347,B_345,C_349,D_348,E_346,F_350),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_347,C_349,D_348),B_345)))
      | ~ v1_funct_2(k1_tmap_1(A_347,B_345,C_349,D_348,E_346,F_350),k4_subset_1(A_347,C_349,D_348),B_345)
      | ~ v1_funct_1(k1_tmap_1(A_347,B_345,C_349,D_348,E_346,F_350))
      | k2_partfun1(D_348,B_345,F_350,k9_subset_1(A_347,C_349,D_348)) != k2_partfun1(C_349,B_345,E_346,k9_subset_1(A_347,C_349,D_348))
      | ~ m1_subset_1(F_350,k1_zfmisc_1(k2_zfmisc_1(D_348,B_345)))
      | ~ v1_funct_2(F_350,D_348,B_345)
      | ~ v1_funct_1(F_350)
      | ~ m1_subset_1(E_346,k1_zfmisc_1(k2_zfmisc_1(C_349,B_345)))
      | ~ v1_funct_2(E_346,C_349,B_345)
      | ~ v1_funct_1(E_346)
      | ~ m1_subset_1(D_348,k1_zfmisc_1(A_347))
      | v1_xboole_0(D_348)
      | ~ m1_subset_1(C_349,k1_zfmisc_1(A_347))
      | v1_xboole_0(C_349)
      | v1_xboole_0(B_345)
      | v1_xboole_0(A_347) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1302,plain,(
    ! [D_427,B_431,F_430,E_426,C_429,A_428] :
      ( k2_partfun1(k4_subset_1(A_428,C_429,D_427),B_431,k1_tmap_1(A_428,B_431,C_429,D_427,E_426,F_430),D_427) = F_430
      | ~ v1_funct_2(k1_tmap_1(A_428,B_431,C_429,D_427,E_426,F_430),k4_subset_1(A_428,C_429,D_427),B_431)
      | ~ v1_funct_1(k1_tmap_1(A_428,B_431,C_429,D_427,E_426,F_430))
      | k2_partfun1(D_427,B_431,F_430,k9_subset_1(A_428,C_429,D_427)) != k2_partfun1(C_429,B_431,E_426,k9_subset_1(A_428,C_429,D_427))
      | ~ m1_subset_1(F_430,k1_zfmisc_1(k2_zfmisc_1(D_427,B_431)))
      | ~ v1_funct_2(F_430,D_427,B_431)
      | ~ v1_funct_1(F_430)
      | ~ m1_subset_1(E_426,k1_zfmisc_1(k2_zfmisc_1(C_429,B_431)))
      | ~ v1_funct_2(E_426,C_429,B_431)
      | ~ v1_funct_1(E_426)
      | ~ m1_subset_1(D_427,k1_zfmisc_1(A_428))
      | v1_xboole_0(D_427)
      | ~ m1_subset_1(C_429,k1_zfmisc_1(A_428))
      | v1_xboole_0(C_429)
      | v1_xboole_0(B_431)
      | v1_xboole_0(A_428) ) ),
    inference(resolution,[status(thm)],[c_40,c_951])).

tff(c_1522,plain,(
    ! [F_459,C_458,D_456,B_460,E_455,A_457] :
      ( k2_partfun1(k4_subset_1(A_457,C_458,D_456),B_460,k1_tmap_1(A_457,B_460,C_458,D_456,E_455,F_459),D_456) = F_459
      | ~ v1_funct_1(k1_tmap_1(A_457,B_460,C_458,D_456,E_455,F_459))
      | k2_partfun1(D_456,B_460,F_459,k9_subset_1(A_457,C_458,D_456)) != k2_partfun1(C_458,B_460,E_455,k9_subset_1(A_457,C_458,D_456))
      | ~ m1_subset_1(F_459,k1_zfmisc_1(k2_zfmisc_1(D_456,B_460)))
      | ~ v1_funct_2(F_459,D_456,B_460)
      | ~ v1_funct_1(F_459)
      | ~ m1_subset_1(E_455,k1_zfmisc_1(k2_zfmisc_1(C_458,B_460)))
      | ~ v1_funct_2(E_455,C_458,B_460)
      | ~ v1_funct_1(E_455)
      | ~ m1_subset_1(D_456,k1_zfmisc_1(A_457))
      | v1_xboole_0(D_456)
      | ~ m1_subset_1(C_458,k1_zfmisc_1(A_457))
      | v1_xboole_0(C_458)
      | v1_xboole_0(B_460)
      | v1_xboole_0(A_457) ) ),
    inference(resolution,[status(thm)],[c_42,c_1302])).

tff(c_1526,plain,(
    ! [A_457,C_458,E_455] :
      ( k2_partfun1(k4_subset_1(A_457,C_458,'#skF_4'),'#skF_2',k1_tmap_1(A_457,'#skF_2',C_458,'#skF_4',E_455,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_457,'#skF_2',C_458,'#skF_4',E_455,'#skF_6'))
      | k2_partfun1(C_458,'#skF_2',E_455,k9_subset_1(A_457,C_458,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_457,C_458,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_455,k1_zfmisc_1(k2_zfmisc_1(C_458,'#skF_2')))
      | ~ v1_funct_2(E_455,C_458,'#skF_2')
      | ~ v1_funct_1(E_455)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_457))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_458,k1_zfmisc_1(A_457))
      | v1_xboole_0(C_458)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_457) ) ),
    inference(resolution,[status(thm)],[c_48,c_1522])).

tff(c_1532,plain,(
    ! [A_457,C_458,E_455] :
      ( k2_partfun1(k4_subset_1(A_457,C_458,'#skF_4'),'#skF_2',k1_tmap_1(A_457,'#skF_2',C_458,'#skF_4',E_455,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_457,'#skF_2',C_458,'#skF_4',E_455,'#skF_6'))
      | k2_partfun1(C_458,'#skF_2',E_455,k9_subset_1(A_457,C_458,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_457,C_458,'#skF_4'))
      | ~ m1_subset_1(E_455,k1_zfmisc_1(k2_zfmisc_1(C_458,'#skF_2')))
      | ~ v1_funct_2(E_455,C_458,'#skF_2')
      | ~ v1_funct_1(E_455)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_457))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_458,k1_zfmisc_1(A_457))
      | v1_xboole_0(C_458)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_457) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_813,c_1526])).

tff(c_1538,plain,(
    ! [A_461,C_462,E_463] :
      ( k2_partfun1(k4_subset_1(A_461,C_462,'#skF_4'),'#skF_2',k1_tmap_1(A_461,'#skF_2',C_462,'#skF_4',E_463,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_461,'#skF_2',C_462,'#skF_4',E_463,'#skF_6'))
      | k2_partfun1(C_462,'#skF_2',E_463,k9_subset_1(A_461,C_462,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_461,C_462,'#skF_4'))
      | ~ m1_subset_1(E_463,k1_zfmisc_1(k2_zfmisc_1(C_462,'#skF_2')))
      | ~ v1_funct_2(E_463,C_462,'#skF_2')
      | ~ v1_funct_1(E_463)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_461))
      | ~ m1_subset_1(C_462,k1_zfmisc_1(A_461))
      | v1_xboole_0(C_462)
      | v1_xboole_0(A_461) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_1532])).

tff(c_1545,plain,(
    ! [A_461] :
      ( k2_partfun1(k4_subset_1(A_461,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_461,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_461,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_461,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_461,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_461))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_461))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_461) ) ),
    inference(resolution,[status(thm)],[c_54,c_1538])).

tff(c_1555,plain,(
    ! [A_461] :
      ( k2_partfun1(k4_subset_1(A_461,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_461,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_461,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_461,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_461,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_461))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_461))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_461) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_816,c_1545])).

tff(c_1557,plain,(
    ! [A_464] :
      ( k2_partfun1(k4_subset_1(A_464,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_464,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_464,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_464,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_464,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_464))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_464))
      | v1_xboole_0(A_464) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1555])).

tff(c_105,plain,(
    ! [B_231,A_232] :
      ( v1_relat_1(B_231)
      | ~ m1_subset_1(B_231,k1_zfmisc_1(A_232))
      | ~ v1_relat_1(A_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_111,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_54,c_105])).

tff(c_123,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_111])).

tff(c_148,plain,(
    ! [A_235,B_236] :
      ( v1_xboole_0(k7_relat_1(A_235,B_236))
      | ~ v1_xboole_0(B_236)
      | ~ v1_relat_1(A_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_154,plain,(
    ! [A_239,B_240] :
      ( k7_relat_1(A_239,B_240) = k1_xboole_0
      | ~ v1_xboole_0(B_240)
      | ~ v1_relat_1(A_239) ) ),
    inference(resolution,[status(thm)],[c_148,c_8])).

tff(c_170,plain,(
    ! [A_244] :
      ( k7_relat_1(A_244,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_244) ) ),
    inference(resolution,[status(thm)],[c_6,c_154])).

tff(c_184,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_123,c_170])).

tff(c_431,plain,(
    ! [A_267,B_268,C_269,D_270] :
      ( k2_partfun1(A_267,B_268,C_269,D_270) = k7_relat_1(C_269,D_270)
      | ~ m1_subset_1(C_269,k1_zfmisc_1(k2_zfmisc_1(A_267,B_268)))
      | ~ v1_funct_1(C_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_435,plain,(
    ! [D_270] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_270) = k7_relat_1('#skF_5',D_270)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_431])).

tff(c_441,plain,(
    ! [D_270] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_270) = k7_relat_1('#skF_5',D_270) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_435])).

tff(c_108,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_105])).

tff(c_120,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_108])).

tff(c_185,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_120,c_170])).

tff(c_433,plain,(
    ! [D_270] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_270) = k7_relat_1('#skF_6',D_270)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_48,c_431])).

tff(c_438,plain,(
    ! [D_270] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_270) = k7_relat_1('#skF_6',D_270) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_433])).

tff(c_255,plain,(
    ! [A_249,B_250] :
      ( r1_xboole_0(A_249,B_250)
      | ~ r1_subset_1(A_249,B_250)
      | v1_xboole_0(B_250)
      | v1_xboole_0(A_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_363,plain,(
    ! [A_260,B_261] :
      ( k3_xboole_0(A_260,B_261) = k1_xboole_0
      | ~ r1_subset_1(A_260,B_261)
      | v1_xboole_0(B_261)
      | v1_xboole_0(A_260) ) ),
    inference(resolution,[status(thm)],[c_255,c_2])).

tff(c_366,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_363])).

tff(c_369,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_64,c_366])).

tff(c_264,plain,(
    ! [A_251,B_252,C_253] :
      ( k9_subset_1(A_251,B_252,C_253) = k3_xboole_0(B_252,C_253)
      | ~ m1_subset_1(C_253,k1_zfmisc_1(A_251)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_276,plain,(
    ! [B_252] : k9_subset_1('#skF_1',B_252,'#skF_4') = k3_xboole_0(B_252,'#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_264])).

tff(c_46,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_99,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_286,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_276,c_99])).

tff(c_461,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_441,c_185,c_438,c_369,c_369,c_286])).

tff(c_462,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_570,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_462])).

tff(c_1568,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1557,c_570])).

tff(c_1582,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_554,c_739,c_553,c_739,c_695,c_695,c_890,c_1568])).

tff(c_1584,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1582])).

tff(c_1585,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_462])).

tff(c_2414,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2405,c_1585])).

tff(c_2425,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_554,c_1755,c_553,c_1755,c_1711,c_1711,c_1910,c_2414])).

tff(c_2427,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2425])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:23:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.62/2.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.62/2.09  
% 5.62/2.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.62/2.09  %$ v1_funct_2 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k2_enumset1 > k9_subset_1 > k4_subset_1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.62/2.09  
% 5.62/2.09  %Foreground sorts:
% 5.62/2.09  
% 5.62/2.09  
% 5.62/2.09  %Background operators:
% 5.62/2.09  
% 5.62/2.09  
% 5.62/2.09  %Foreground operators:
% 5.62/2.09  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 5.62/2.09  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.62/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.62/2.09  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.62/2.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.62/2.09  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.62/2.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.62/2.09  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.62/2.09  tff('#skF_5', type, '#skF_5': $i).
% 5.62/2.09  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.62/2.09  tff('#skF_6', type, '#skF_6': $i).
% 5.62/2.09  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.62/2.09  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.62/2.09  tff('#skF_2', type, '#skF_2': $i).
% 5.62/2.09  tff('#skF_3', type, '#skF_3': $i).
% 5.62/2.09  tff('#skF_1', type, '#skF_1': $i).
% 5.62/2.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.62/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.62/2.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.62/2.09  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.62/2.09  tff('#skF_4', type, '#skF_4': $i).
% 5.62/2.09  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.62/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.62/2.09  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 5.62/2.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.62/2.09  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.62/2.09  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 5.62/2.09  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.62/2.09  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.62/2.09  
% 5.84/2.13  tff(f_208, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 5.84/2.13  tff(f_68, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.84/2.13  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.84/2.13  tff(f_30, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.84/2.13  tff(f_66, axiom, (![A, B]: ((v1_relat_1(A) & v1_xboole_0(B)) => (v1_xboole_0(k7_relat_1(A, B)) & v1_relat_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc16_relat_1)).
% 5.84/2.13  tff(f_34, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.84/2.13  tff(f_78, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 5.84/2.13  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.84/2.13  tff(f_42, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 5.84/2.13  tff(f_166, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 5.84/2.13  tff(f_84, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 5.84/2.13  tff(f_132, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 5.84/2.13  tff(c_72, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_208])).
% 5.84/2.13  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_208])).
% 5.84/2.13  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_208])).
% 5.84/2.13  tff(c_26, plain, (![A_22, B_23]: (v1_relat_1(k2_zfmisc_1(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.84/2.13  tff(c_48, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_208])).
% 5.84/2.13  tff(c_494, plain, (![B_277, A_278]: (v1_relat_1(B_277) | ~m1_subset_1(B_277, k1_zfmisc_1(A_278)) | ~v1_relat_1(A_278))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.84/2.13  tff(c_497, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_48, c_494])).
% 5.84/2.13  tff(c_509, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_497])).
% 5.84/2.13  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 5.84/2.13  tff(c_518, plain, (![A_281, B_282]: (v1_xboole_0(k7_relat_1(A_281, B_282)) | ~v1_xboole_0(B_282) | ~v1_relat_1(A_281))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.84/2.13  tff(c_8, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.84/2.13  tff(c_532, plain, (![A_286, B_287]: (k7_relat_1(A_286, B_287)=k1_xboole_0 | ~v1_xboole_0(B_287) | ~v1_relat_1(A_286))), inference(resolution, [status(thm)], [c_518, c_8])).
% 5.84/2.13  tff(c_539, plain, (![A_288]: (k7_relat_1(A_288, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_288))), inference(resolution, [status(thm)], [c_6, c_532])).
% 5.84/2.13  tff(c_554, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_509, c_539])).
% 5.84/2.13  tff(c_68, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_208])).
% 5.84/2.13  tff(c_64, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_208])).
% 5.84/2.13  tff(c_60, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_208])).
% 5.84/2.13  tff(c_1641, plain, (![A_469, B_470]: (r1_xboole_0(A_469, B_470) | ~r1_subset_1(A_469, B_470) | v1_xboole_0(B_470) | v1_xboole_0(A_469))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.84/2.13  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.84/2.13  tff(c_1749, plain, (![A_480, B_481]: (k3_xboole_0(A_480, B_481)=k1_xboole_0 | ~r1_subset_1(A_480, B_481) | v1_xboole_0(B_481) | v1_xboole_0(A_480))), inference(resolution, [status(thm)], [c_1641, c_2])).
% 5.84/2.13  tff(c_1752, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_1749])).
% 5.84/2.13  tff(c_1755, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_68, c_64, c_1752])).
% 5.84/2.13  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_208])).
% 5.84/2.13  tff(c_500, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_54, c_494])).
% 5.84/2.13  tff(c_512, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_500])).
% 5.84/2.13  tff(c_553, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_512, c_539])).
% 5.84/2.13  tff(c_1699, plain, (![A_473, B_474, C_475]: (k9_subset_1(A_473, B_474, C_475)=k3_xboole_0(B_474, C_475) | ~m1_subset_1(C_475, k1_zfmisc_1(A_473)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.84/2.13  tff(c_1711, plain, (![B_474]: (k9_subset_1('#skF_1', B_474, '#skF_4')=k3_xboole_0(B_474, '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_1699])).
% 5.84/2.13  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_208])).
% 5.84/2.13  tff(c_56, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 5.84/2.13  tff(c_70, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 5.84/2.13  tff(c_52, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_208])).
% 5.84/2.13  tff(c_50, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 5.84/2.13  tff(c_1869, plain, (![F_497, E_493, D_494, A_495, B_498, C_496]: (v1_funct_1(k1_tmap_1(A_495, B_498, C_496, D_494, E_493, F_497)) | ~m1_subset_1(F_497, k1_zfmisc_1(k2_zfmisc_1(D_494, B_498))) | ~v1_funct_2(F_497, D_494, B_498) | ~v1_funct_1(F_497) | ~m1_subset_1(E_493, k1_zfmisc_1(k2_zfmisc_1(C_496, B_498))) | ~v1_funct_2(E_493, C_496, B_498) | ~v1_funct_1(E_493) | ~m1_subset_1(D_494, k1_zfmisc_1(A_495)) | v1_xboole_0(D_494) | ~m1_subset_1(C_496, k1_zfmisc_1(A_495)) | v1_xboole_0(C_496) | v1_xboole_0(B_498) | v1_xboole_0(A_495))), inference(cnfTransformation, [status(thm)], [f_166])).
% 5.84/2.13  tff(c_1871, plain, (![A_495, C_496, E_493]: (v1_funct_1(k1_tmap_1(A_495, '#skF_2', C_496, '#skF_4', E_493, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_493, k1_zfmisc_1(k2_zfmisc_1(C_496, '#skF_2'))) | ~v1_funct_2(E_493, C_496, '#skF_2') | ~v1_funct_1(E_493) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_495)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_496, k1_zfmisc_1(A_495)) | v1_xboole_0(C_496) | v1_xboole_0('#skF_2') | v1_xboole_0(A_495))), inference(resolution, [status(thm)], [c_48, c_1869])).
% 5.84/2.13  tff(c_1876, plain, (![A_495, C_496, E_493]: (v1_funct_1(k1_tmap_1(A_495, '#skF_2', C_496, '#skF_4', E_493, '#skF_6')) | ~m1_subset_1(E_493, k1_zfmisc_1(k2_zfmisc_1(C_496, '#skF_2'))) | ~v1_funct_2(E_493, C_496, '#skF_2') | ~v1_funct_1(E_493) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_495)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_496, k1_zfmisc_1(A_495)) | v1_xboole_0(C_496) | v1_xboole_0('#skF_2') | v1_xboole_0(A_495))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1871])).
% 5.84/2.13  tff(c_1882, plain, (![A_499, C_500, E_501]: (v1_funct_1(k1_tmap_1(A_499, '#skF_2', C_500, '#skF_4', E_501, '#skF_6')) | ~m1_subset_1(E_501, k1_zfmisc_1(k2_zfmisc_1(C_500, '#skF_2'))) | ~v1_funct_2(E_501, C_500, '#skF_2') | ~v1_funct_1(E_501) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_499)) | ~m1_subset_1(C_500, k1_zfmisc_1(A_499)) | v1_xboole_0(C_500) | v1_xboole_0(A_499))), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_1876])).
% 5.84/2.13  tff(c_1886, plain, (![A_499]: (v1_funct_1(k1_tmap_1(A_499, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_499)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_499)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_499))), inference(resolution, [status(thm)], [c_54, c_1882])).
% 5.84/2.13  tff(c_1893, plain, (![A_499]: (v1_funct_1(k1_tmap_1(A_499, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_499)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_499)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_499))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_1886])).
% 5.84/2.13  tff(c_1903, plain, (![A_509]: (v1_funct_1(k1_tmap_1(A_509, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_509)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_509)) | v1_xboole_0(A_509))), inference(negUnitSimplification, [status(thm)], [c_68, c_1893])).
% 5.84/2.13  tff(c_1906, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_66, c_1903])).
% 5.84/2.13  tff(c_1909, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1906])).
% 5.84/2.13  tff(c_1910, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_72, c_1909])).
% 5.84/2.13  tff(c_1826, plain, (![A_487, B_488, C_489, D_490]: (k2_partfun1(A_487, B_488, C_489, D_490)=k7_relat_1(C_489, D_490) | ~m1_subset_1(C_489, k1_zfmisc_1(k2_zfmisc_1(A_487, B_488))) | ~v1_funct_1(C_489))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.84/2.13  tff(c_1830, plain, (![D_490]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_490)=k7_relat_1('#skF_5', D_490) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_1826])).
% 5.84/2.13  tff(c_1836, plain, (![D_490]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_490)=k7_relat_1('#skF_5', D_490))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1830])).
% 5.84/2.13  tff(c_1828, plain, (![D_490]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_490)=k7_relat_1('#skF_6', D_490) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_48, c_1826])).
% 5.84/2.13  tff(c_1833, plain, (![D_490]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_490)=k7_relat_1('#skF_6', D_490))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1828])).
% 5.84/2.13  tff(c_42, plain, (![C_159, D_160, F_162, A_157, B_158, E_161]: (v1_funct_2(k1_tmap_1(A_157, B_158, C_159, D_160, E_161, F_162), k4_subset_1(A_157, C_159, D_160), B_158) | ~m1_subset_1(F_162, k1_zfmisc_1(k2_zfmisc_1(D_160, B_158))) | ~v1_funct_2(F_162, D_160, B_158) | ~v1_funct_1(F_162) | ~m1_subset_1(E_161, k1_zfmisc_1(k2_zfmisc_1(C_159, B_158))) | ~v1_funct_2(E_161, C_159, B_158) | ~v1_funct_1(E_161) | ~m1_subset_1(D_160, k1_zfmisc_1(A_157)) | v1_xboole_0(D_160) | ~m1_subset_1(C_159, k1_zfmisc_1(A_157)) | v1_xboole_0(C_159) | v1_xboole_0(B_158) | v1_xboole_0(A_157))), inference(cnfTransformation, [status(thm)], [f_166])).
% 5.84/2.13  tff(c_40, plain, (![C_159, D_160, F_162, A_157, B_158, E_161]: (m1_subset_1(k1_tmap_1(A_157, B_158, C_159, D_160, E_161, F_162), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_157, C_159, D_160), B_158))) | ~m1_subset_1(F_162, k1_zfmisc_1(k2_zfmisc_1(D_160, B_158))) | ~v1_funct_2(F_162, D_160, B_158) | ~v1_funct_1(F_162) | ~m1_subset_1(E_161, k1_zfmisc_1(k2_zfmisc_1(C_159, B_158))) | ~v1_funct_2(E_161, C_159, B_158) | ~v1_funct_1(E_161) | ~m1_subset_1(D_160, k1_zfmisc_1(A_157)) | v1_xboole_0(D_160) | ~m1_subset_1(C_159, k1_zfmisc_1(A_157)) | v1_xboole_0(C_159) | v1_xboole_0(B_158) | v1_xboole_0(A_157))), inference(cnfTransformation, [status(thm)], [f_166])).
% 5.84/2.13  tff(c_1971, plain, (![B_521, A_523, C_525, E_522, D_524, F_526]: (k2_partfun1(k4_subset_1(A_523, C_525, D_524), B_521, k1_tmap_1(A_523, B_521, C_525, D_524, E_522, F_526), C_525)=E_522 | ~m1_subset_1(k1_tmap_1(A_523, B_521, C_525, D_524, E_522, F_526), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_523, C_525, D_524), B_521))) | ~v1_funct_2(k1_tmap_1(A_523, B_521, C_525, D_524, E_522, F_526), k4_subset_1(A_523, C_525, D_524), B_521) | ~v1_funct_1(k1_tmap_1(A_523, B_521, C_525, D_524, E_522, F_526)) | k2_partfun1(D_524, B_521, F_526, k9_subset_1(A_523, C_525, D_524))!=k2_partfun1(C_525, B_521, E_522, k9_subset_1(A_523, C_525, D_524)) | ~m1_subset_1(F_526, k1_zfmisc_1(k2_zfmisc_1(D_524, B_521))) | ~v1_funct_2(F_526, D_524, B_521) | ~v1_funct_1(F_526) | ~m1_subset_1(E_522, k1_zfmisc_1(k2_zfmisc_1(C_525, B_521))) | ~v1_funct_2(E_522, C_525, B_521) | ~v1_funct_1(E_522) | ~m1_subset_1(D_524, k1_zfmisc_1(A_523)) | v1_xboole_0(D_524) | ~m1_subset_1(C_525, k1_zfmisc_1(A_523)) | v1_xboole_0(C_525) | v1_xboole_0(B_521) | v1_xboole_0(A_523))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.84/2.13  tff(c_2344, plain, (![B_595, A_592, E_590, F_594, C_593, D_591]: (k2_partfun1(k4_subset_1(A_592, C_593, D_591), B_595, k1_tmap_1(A_592, B_595, C_593, D_591, E_590, F_594), C_593)=E_590 | ~v1_funct_2(k1_tmap_1(A_592, B_595, C_593, D_591, E_590, F_594), k4_subset_1(A_592, C_593, D_591), B_595) | ~v1_funct_1(k1_tmap_1(A_592, B_595, C_593, D_591, E_590, F_594)) | k2_partfun1(D_591, B_595, F_594, k9_subset_1(A_592, C_593, D_591))!=k2_partfun1(C_593, B_595, E_590, k9_subset_1(A_592, C_593, D_591)) | ~m1_subset_1(F_594, k1_zfmisc_1(k2_zfmisc_1(D_591, B_595))) | ~v1_funct_2(F_594, D_591, B_595) | ~v1_funct_1(F_594) | ~m1_subset_1(E_590, k1_zfmisc_1(k2_zfmisc_1(C_593, B_595))) | ~v1_funct_2(E_590, C_593, B_595) | ~v1_funct_1(E_590) | ~m1_subset_1(D_591, k1_zfmisc_1(A_592)) | v1_xboole_0(D_591) | ~m1_subset_1(C_593, k1_zfmisc_1(A_592)) | v1_xboole_0(C_593) | v1_xboole_0(B_595) | v1_xboole_0(A_592))), inference(resolution, [status(thm)], [c_40, c_1971])).
% 5.84/2.13  tff(c_2348, plain, (![B_601, A_598, F_600, D_597, C_599, E_596]: (k2_partfun1(k4_subset_1(A_598, C_599, D_597), B_601, k1_tmap_1(A_598, B_601, C_599, D_597, E_596, F_600), C_599)=E_596 | ~v1_funct_1(k1_tmap_1(A_598, B_601, C_599, D_597, E_596, F_600)) | k2_partfun1(D_597, B_601, F_600, k9_subset_1(A_598, C_599, D_597))!=k2_partfun1(C_599, B_601, E_596, k9_subset_1(A_598, C_599, D_597)) | ~m1_subset_1(F_600, k1_zfmisc_1(k2_zfmisc_1(D_597, B_601))) | ~v1_funct_2(F_600, D_597, B_601) | ~v1_funct_1(F_600) | ~m1_subset_1(E_596, k1_zfmisc_1(k2_zfmisc_1(C_599, B_601))) | ~v1_funct_2(E_596, C_599, B_601) | ~v1_funct_1(E_596) | ~m1_subset_1(D_597, k1_zfmisc_1(A_598)) | v1_xboole_0(D_597) | ~m1_subset_1(C_599, k1_zfmisc_1(A_598)) | v1_xboole_0(C_599) | v1_xboole_0(B_601) | v1_xboole_0(A_598))), inference(resolution, [status(thm)], [c_42, c_2344])).
% 5.84/2.13  tff(c_2352, plain, (![A_598, C_599, E_596]: (k2_partfun1(k4_subset_1(A_598, C_599, '#skF_4'), '#skF_2', k1_tmap_1(A_598, '#skF_2', C_599, '#skF_4', E_596, '#skF_6'), C_599)=E_596 | ~v1_funct_1(k1_tmap_1(A_598, '#skF_2', C_599, '#skF_4', E_596, '#skF_6')) | k2_partfun1(C_599, '#skF_2', E_596, k9_subset_1(A_598, C_599, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_598, C_599, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_596, k1_zfmisc_1(k2_zfmisc_1(C_599, '#skF_2'))) | ~v1_funct_2(E_596, C_599, '#skF_2') | ~v1_funct_1(E_596) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_598)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_599, k1_zfmisc_1(A_598)) | v1_xboole_0(C_599) | v1_xboole_0('#skF_2') | v1_xboole_0(A_598))), inference(resolution, [status(thm)], [c_48, c_2348])).
% 5.84/2.13  tff(c_2358, plain, (![A_598, C_599, E_596]: (k2_partfun1(k4_subset_1(A_598, C_599, '#skF_4'), '#skF_2', k1_tmap_1(A_598, '#skF_2', C_599, '#skF_4', E_596, '#skF_6'), C_599)=E_596 | ~v1_funct_1(k1_tmap_1(A_598, '#skF_2', C_599, '#skF_4', E_596, '#skF_6')) | k2_partfun1(C_599, '#skF_2', E_596, k9_subset_1(A_598, C_599, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_598, C_599, '#skF_4')) | ~m1_subset_1(E_596, k1_zfmisc_1(k2_zfmisc_1(C_599, '#skF_2'))) | ~v1_funct_2(E_596, C_599, '#skF_2') | ~v1_funct_1(E_596) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_598)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_599, k1_zfmisc_1(A_598)) | v1_xboole_0(C_599) | v1_xboole_0('#skF_2') | v1_xboole_0(A_598))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1833, c_2352])).
% 5.84/2.13  tff(c_2364, plain, (![A_602, C_603, E_604]: (k2_partfun1(k4_subset_1(A_602, C_603, '#skF_4'), '#skF_2', k1_tmap_1(A_602, '#skF_2', C_603, '#skF_4', E_604, '#skF_6'), C_603)=E_604 | ~v1_funct_1(k1_tmap_1(A_602, '#skF_2', C_603, '#skF_4', E_604, '#skF_6')) | k2_partfun1(C_603, '#skF_2', E_604, k9_subset_1(A_602, C_603, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_602, C_603, '#skF_4')) | ~m1_subset_1(E_604, k1_zfmisc_1(k2_zfmisc_1(C_603, '#skF_2'))) | ~v1_funct_2(E_604, C_603, '#skF_2') | ~v1_funct_1(E_604) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_602)) | ~m1_subset_1(C_603, k1_zfmisc_1(A_602)) | v1_xboole_0(C_603) | v1_xboole_0(A_602))), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_2358])).
% 5.84/2.13  tff(c_2371, plain, (![A_602]: (k2_partfun1(k4_subset_1(A_602, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_602, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_602, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_602, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_602, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_602)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_602)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_602))), inference(resolution, [status(thm)], [c_54, c_2364])).
% 5.84/2.13  tff(c_2381, plain, (![A_602]: (k2_partfun1(k4_subset_1(A_602, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_602, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_602, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_602, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_602, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_602)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_602)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_602))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_1836, c_2371])).
% 5.84/2.13  tff(c_2405, plain, (![A_606]: (k2_partfun1(k4_subset_1(A_606, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_606, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_606, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_606, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_606, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_606)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_606)) | v1_xboole_0(A_606))), inference(negUnitSimplification, [status(thm)], [c_68, c_2381])).
% 5.84/2.13  tff(c_625, plain, (![A_293, B_294]: (r1_xboole_0(A_293, B_294) | ~r1_subset_1(A_293, B_294) | v1_xboole_0(B_294) | v1_xboole_0(A_293))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.84/2.13  tff(c_733, plain, (![A_304, B_305]: (k3_xboole_0(A_304, B_305)=k1_xboole_0 | ~r1_subset_1(A_304, B_305) | v1_xboole_0(B_305) | v1_xboole_0(A_304))), inference(resolution, [status(thm)], [c_625, c_2])).
% 5.84/2.13  tff(c_736, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_733])).
% 5.84/2.13  tff(c_739, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_68, c_64, c_736])).
% 5.84/2.13  tff(c_683, plain, (![A_297, B_298, C_299]: (k9_subset_1(A_297, B_298, C_299)=k3_xboole_0(B_298, C_299) | ~m1_subset_1(C_299, k1_zfmisc_1(A_297)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.84/2.13  tff(c_695, plain, (![B_298]: (k9_subset_1('#skF_1', B_298, '#skF_4')=k3_xboole_0(B_298, '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_683])).
% 5.84/2.13  tff(c_849, plain, (![C_320, A_319, E_317, B_322, F_321, D_318]: (v1_funct_1(k1_tmap_1(A_319, B_322, C_320, D_318, E_317, F_321)) | ~m1_subset_1(F_321, k1_zfmisc_1(k2_zfmisc_1(D_318, B_322))) | ~v1_funct_2(F_321, D_318, B_322) | ~v1_funct_1(F_321) | ~m1_subset_1(E_317, k1_zfmisc_1(k2_zfmisc_1(C_320, B_322))) | ~v1_funct_2(E_317, C_320, B_322) | ~v1_funct_1(E_317) | ~m1_subset_1(D_318, k1_zfmisc_1(A_319)) | v1_xboole_0(D_318) | ~m1_subset_1(C_320, k1_zfmisc_1(A_319)) | v1_xboole_0(C_320) | v1_xboole_0(B_322) | v1_xboole_0(A_319))), inference(cnfTransformation, [status(thm)], [f_166])).
% 5.84/2.13  tff(c_851, plain, (![A_319, C_320, E_317]: (v1_funct_1(k1_tmap_1(A_319, '#skF_2', C_320, '#skF_4', E_317, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_317, k1_zfmisc_1(k2_zfmisc_1(C_320, '#skF_2'))) | ~v1_funct_2(E_317, C_320, '#skF_2') | ~v1_funct_1(E_317) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_319)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_320, k1_zfmisc_1(A_319)) | v1_xboole_0(C_320) | v1_xboole_0('#skF_2') | v1_xboole_0(A_319))), inference(resolution, [status(thm)], [c_48, c_849])).
% 5.84/2.13  tff(c_856, plain, (![A_319, C_320, E_317]: (v1_funct_1(k1_tmap_1(A_319, '#skF_2', C_320, '#skF_4', E_317, '#skF_6')) | ~m1_subset_1(E_317, k1_zfmisc_1(k2_zfmisc_1(C_320, '#skF_2'))) | ~v1_funct_2(E_317, C_320, '#skF_2') | ~v1_funct_1(E_317) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_319)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_320, k1_zfmisc_1(A_319)) | v1_xboole_0(C_320) | v1_xboole_0('#skF_2') | v1_xboole_0(A_319))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_851])).
% 5.84/2.13  tff(c_862, plain, (![A_323, C_324, E_325]: (v1_funct_1(k1_tmap_1(A_323, '#skF_2', C_324, '#skF_4', E_325, '#skF_6')) | ~m1_subset_1(E_325, k1_zfmisc_1(k2_zfmisc_1(C_324, '#skF_2'))) | ~v1_funct_2(E_325, C_324, '#skF_2') | ~v1_funct_1(E_325) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_323)) | ~m1_subset_1(C_324, k1_zfmisc_1(A_323)) | v1_xboole_0(C_324) | v1_xboole_0(A_323))), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_856])).
% 5.84/2.13  tff(c_866, plain, (![A_323]: (v1_funct_1(k1_tmap_1(A_323, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_323)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_323)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_323))), inference(resolution, [status(thm)], [c_54, c_862])).
% 5.84/2.13  tff(c_873, plain, (![A_323]: (v1_funct_1(k1_tmap_1(A_323, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_323)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_323)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_323))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_866])).
% 5.84/2.13  tff(c_883, plain, (![A_333]: (v1_funct_1(k1_tmap_1(A_333, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_333)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_333)) | v1_xboole_0(A_333))), inference(negUnitSimplification, [status(thm)], [c_68, c_873])).
% 5.84/2.13  tff(c_886, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_66, c_883])).
% 5.84/2.13  tff(c_889, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_886])).
% 5.84/2.13  tff(c_890, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_72, c_889])).
% 5.84/2.13  tff(c_806, plain, (![A_311, B_312, C_313, D_314]: (k2_partfun1(A_311, B_312, C_313, D_314)=k7_relat_1(C_313, D_314) | ~m1_subset_1(C_313, k1_zfmisc_1(k2_zfmisc_1(A_311, B_312))) | ~v1_funct_1(C_313))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.84/2.13  tff(c_810, plain, (![D_314]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_314)=k7_relat_1('#skF_5', D_314) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_806])).
% 5.84/2.13  tff(c_816, plain, (![D_314]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_314)=k7_relat_1('#skF_5', D_314))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_810])).
% 5.84/2.13  tff(c_808, plain, (![D_314]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_314)=k7_relat_1('#skF_6', D_314) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_48, c_806])).
% 5.84/2.13  tff(c_813, plain, (![D_314]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_314)=k7_relat_1('#skF_6', D_314))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_808])).
% 5.84/2.13  tff(c_951, plain, (![C_349, B_345, A_347, E_346, D_348, F_350]: (k2_partfun1(k4_subset_1(A_347, C_349, D_348), B_345, k1_tmap_1(A_347, B_345, C_349, D_348, E_346, F_350), D_348)=F_350 | ~m1_subset_1(k1_tmap_1(A_347, B_345, C_349, D_348, E_346, F_350), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_347, C_349, D_348), B_345))) | ~v1_funct_2(k1_tmap_1(A_347, B_345, C_349, D_348, E_346, F_350), k4_subset_1(A_347, C_349, D_348), B_345) | ~v1_funct_1(k1_tmap_1(A_347, B_345, C_349, D_348, E_346, F_350)) | k2_partfun1(D_348, B_345, F_350, k9_subset_1(A_347, C_349, D_348))!=k2_partfun1(C_349, B_345, E_346, k9_subset_1(A_347, C_349, D_348)) | ~m1_subset_1(F_350, k1_zfmisc_1(k2_zfmisc_1(D_348, B_345))) | ~v1_funct_2(F_350, D_348, B_345) | ~v1_funct_1(F_350) | ~m1_subset_1(E_346, k1_zfmisc_1(k2_zfmisc_1(C_349, B_345))) | ~v1_funct_2(E_346, C_349, B_345) | ~v1_funct_1(E_346) | ~m1_subset_1(D_348, k1_zfmisc_1(A_347)) | v1_xboole_0(D_348) | ~m1_subset_1(C_349, k1_zfmisc_1(A_347)) | v1_xboole_0(C_349) | v1_xboole_0(B_345) | v1_xboole_0(A_347))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.84/2.13  tff(c_1302, plain, (![D_427, B_431, F_430, E_426, C_429, A_428]: (k2_partfun1(k4_subset_1(A_428, C_429, D_427), B_431, k1_tmap_1(A_428, B_431, C_429, D_427, E_426, F_430), D_427)=F_430 | ~v1_funct_2(k1_tmap_1(A_428, B_431, C_429, D_427, E_426, F_430), k4_subset_1(A_428, C_429, D_427), B_431) | ~v1_funct_1(k1_tmap_1(A_428, B_431, C_429, D_427, E_426, F_430)) | k2_partfun1(D_427, B_431, F_430, k9_subset_1(A_428, C_429, D_427))!=k2_partfun1(C_429, B_431, E_426, k9_subset_1(A_428, C_429, D_427)) | ~m1_subset_1(F_430, k1_zfmisc_1(k2_zfmisc_1(D_427, B_431))) | ~v1_funct_2(F_430, D_427, B_431) | ~v1_funct_1(F_430) | ~m1_subset_1(E_426, k1_zfmisc_1(k2_zfmisc_1(C_429, B_431))) | ~v1_funct_2(E_426, C_429, B_431) | ~v1_funct_1(E_426) | ~m1_subset_1(D_427, k1_zfmisc_1(A_428)) | v1_xboole_0(D_427) | ~m1_subset_1(C_429, k1_zfmisc_1(A_428)) | v1_xboole_0(C_429) | v1_xboole_0(B_431) | v1_xboole_0(A_428))), inference(resolution, [status(thm)], [c_40, c_951])).
% 5.84/2.13  tff(c_1522, plain, (![F_459, C_458, D_456, B_460, E_455, A_457]: (k2_partfun1(k4_subset_1(A_457, C_458, D_456), B_460, k1_tmap_1(A_457, B_460, C_458, D_456, E_455, F_459), D_456)=F_459 | ~v1_funct_1(k1_tmap_1(A_457, B_460, C_458, D_456, E_455, F_459)) | k2_partfun1(D_456, B_460, F_459, k9_subset_1(A_457, C_458, D_456))!=k2_partfun1(C_458, B_460, E_455, k9_subset_1(A_457, C_458, D_456)) | ~m1_subset_1(F_459, k1_zfmisc_1(k2_zfmisc_1(D_456, B_460))) | ~v1_funct_2(F_459, D_456, B_460) | ~v1_funct_1(F_459) | ~m1_subset_1(E_455, k1_zfmisc_1(k2_zfmisc_1(C_458, B_460))) | ~v1_funct_2(E_455, C_458, B_460) | ~v1_funct_1(E_455) | ~m1_subset_1(D_456, k1_zfmisc_1(A_457)) | v1_xboole_0(D_456) | ~m1_subset_1(C_458, k1_zfmisc_1(A_457)) | v1_xboole_0(C_458) | v1_xboole_0(B_460) | v1_xboole_0(A_457))), inference(resolution, [status(thm)], [c_42, c_1302])).
% 5.84/2.13  tff(c_1526, plain, (![A_457, C_458, E_455]: (k2_partfun1(k4_subset_1(A_457, C_458, '#skF_4'), '#skF_2', k1_tmap_1(A_457, '#skF_2', C_458, '#skF_4', E_455, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_457, '#skF_2', C_458, '#skF_4', E_455, '#skF_6')) | k2_partfun1(C_458, '#skF_2', E_455, k9_subset_1(A_457, C_458, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_457, C_458, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_455, k1_zfmisc_1(k2_zfmisc_1(C_458, '#skF_2'))) | ~v1_funct_2(E_455, C_458, '#skF_2') | ~v1_funct_1(E_455) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_457)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_458, k1_zfmisc_1(A_457)) | v1_xboole_0(C_458) | v1_xboole_0('#skF_2') | v1_xboole_0(A_457))), inference(resolution, [status(thm)], [c_48, c_1522])).
% 5.84/2.13  tff(c_1532, plain, (![A_457, C_458, E_455]: (k2_partfun1(k4_subset_1(A_457, C_458, '#skF_4'), '#skF_2', k1_tmap_1(A_457, '#skF_2', C_458, '#skF_4', E_455, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_457, '#skF_2', C_458, '#skF_4', E_455, '#skF_6')) | k2_partfun1(C_458, '#skF_2', E_455, k9_subset_1(A_457, C_458, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_457, C_458, '#skF_4')) | ~m1_subset_1(E_455, k1_zfmisc_1(k2_zfmisc_1(C_458, '#skF_2'))) | ~v1_funct_2(E_455, C_458, '#skF_2') | ~v1_funct_1(E_455) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_457)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_458, k1_zfmisc_1(A_457)) | v1_xboole_0(C_458) | v1_xboole_0('#skF_2') | v1_xboole_0(A_457))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_813, c_1526])).
% 5.84/2.13  tff(c_1538, plain, (![A_461, C_462, E_463]: (k2_partfun1(k4_subset_1(A_461, C_462, '#skF_4'), '#skF_2', k1_tmap_1(A_461, '#skF_2', C_462, '#skF_4', E_463, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_461, '#skF_2', C_462, '#skF_4', E_463, '#skF_6')) | k2_partfun1(C_462, '#skF_2', E_463, k9_subset_1(A_461, C_462, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_461, C_462, '#skF_4')) | ~m1_subset_1(E_463, k1_zfmisc_1(k2_zfmisc_1(C_462, '#skF_2'))) | ~v1_funct_2(E_463, C_462, '#skF_2') | ~v1_funct_1(E_463) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_461)) | ~m1_subset_1(C_462, k1_zfmisc_1(A_461)) | v1_xboole_0(C_462) | v1_xboole_0(A_461))), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_1532])).
% 5.84/2.13  tff(c_1545, plain, (![A_461]: (k2_partfun1(k4_subset_1(A_461, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_461, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_461, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_461, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_461, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_461)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_461)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_461))), inference(resolution, [status(thm)], [c_54, c_1538])).
% 5.84/2.13  tff(c_1555, plain, (![A_461]: (k2_partfun1(k4_subset_1(A_461, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_461, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_461, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_461, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_461, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_461)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_461)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_461))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_816, c_1545])).
% 5.84/2.13  tff(c_1557, plain, (![A_464]: (k2_partfun1(k4_subset_1(A_464, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_464, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_464, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_464, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_464, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_464)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_464)) | v1_xboole_0(A_464))), inference(negUnitSimplification, [status(thm)], [c_68, c_1555])).
% 5.84/2.13  tff(c_105, plain, (![B_231, A_232]: (v1_relat_1(B_231) | ~m1_subset_1(B_231, k1_zfmisc_1(A_232)) | ~v1_relat_1(A_232))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.84/2.13  tff(c_111, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_54, c_105])).
% 5.84/2.13  tff(c_123, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_111])).
% 5.84/2.13  tff(c_148, plain, (![A_235, B_236]: (v1_xboole_0(k7_relat_1(A_235, B_236)) | ~v1_xboole_0(B_236) | ~v1_relat_1(A_235))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.84/2.13  tff(c_154, plain, (![A_239, B_240]: (k7_relat_1(A_239, B_240)=k1_xboole_0 | ~v1_xboole_0(B_240) | ~v1_relat_1(A_239))), inference(resolution, [status(thm)], [c_148, c_8])).
% 5.84/2.13  tff(c_170, plain, (![A_244]: (k7_relat_1(A_244, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_244))), inference(resolution, [status(thm)], [c_6, c_154])).
% 5.84/2.13  tff(c_184, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_123, c_170])).
% 5.84/2.13  tff(c_431, plain, (![A_267, B_268, C_269, D_270]: (k2_partfun1(A_267, B_268, C_269, D_270)=k7_relat_1(C_269, D_270) | ~m1_subset_1(C_269, k1_zfmisc_1(k2_zfmisc_1(A_267, B_268))) | ~v1_funct_1(C_269))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.84/2.13  tff(c_435, plain, (![D_270]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_270)=k7_relat_1('#skF_5', D_270) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_431])).
% 5.84/2.13  tff(c_441, plain, (![D_270]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_270)=k7_relat_1('#skF_5', D_270))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_435])).
% 5.84/2.13  tff(c_108, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_48, c_105])).
% 5.84/2.13  tff(c_120, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_108])).
% 5.84/2.13  tff(c_185, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_120, c_170])).
% 5.84/2.13  tff(c_433, plain, (![D_270]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_270)=k7_relat_1('#skF_6', D_270) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_48, c_431])).
% 5.84/2.13  tff(c_438, plain, (![D_270]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_270)=k7_relat_1('#skF_6', D_270))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_433])).
% 5.84/2.13  tff(c_255, plain, (![A_249, B_250]: (r1_xboole_0(A_249, B_250) | ~r1_subset_1(A_249, B_250) | v1_xboole_0(B_250) | v1_xboole_0(A_249))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.84/2.13  tff(c_363, plain, (![A_260, B_261]: (k3_xboole_0(A_260, B_261)=k1_xboole_0 | ~r1_subset_1(A_260, B_261) | v1_xboole_0(B_261) | v1_xboole_0(A_260))), inference(resolution, [status(thm)], [c_255, c_2])).
% 5.84/2.13  tff(c_366, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_363])).
% 5.84/2.13  tff(c_369, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_68, c_64, c_366])).
% 5.84/2.13  tff(c_264, plain, (![A_251, B_252, C_253]: (k9_subset_1(A_251, B_252, C_253)=k3_xboole_0(B_252, C_253) | ~m1_subset_1(C_253, k1_zfmisc_1(A_251)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.84/2.13  tff(c_276, plain, (![B_252]: (k9_subset_1('#skF_1', B_252, '#skF_4')=k3_xboole_0(B_252, '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_264])).
% 5.84/2.13  tff(c_46, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_208])).
% 5.84/2.13  tff(c_99, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_46])).
% 5.84/2.13  tff(c_286, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_276, c_276, c_99])).
% 5.84/2.13  tff(c_461, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_184, c_441, c_185, c_438, c_369, c_369, c_286])).
% 5.84/2.13  tff(c_462, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_46])).
% 5.84/2.13  tff(c_570, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_462])).
% 5.84/2.13  tff(c_1568, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1557, c_570])).
% 5.84/2.13  tff(c_1582, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_554, c_739, c_553, c_739, c_695, c_695, c_890, c_1568])).
% 5.84/2.13  tff(c_1584, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_1582])).
% 5.84/2.13  tff(c_1585, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_462])).
% 5.84/2.13  tff(c_2414, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2405, c_1585])).
% 5.84/2.13  tff(c_2425, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_554, c_1755, c_553, c_1755, c_1711, c_1711, c_1910, c_2414])).
% 5.84/2.13  tff(c_2427, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_2425])).
% 5.84/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.84/2.13  
% 5.84/2.13  Inference rules
% 5.84/2.13  ----------------------
% 5.84/2.13  #Ref     : 0
% 5.84/2.13  #Sup     : 502
% 5.84/2.13  #Fact    : 0
% 5.84/2.13  #Define  : 0
% 5.84/2.13  #Split   : 10
% 5.84/2.13  #Chain   : 0
% 5.84/2.13  #Close   : 0
% 5.84/2.13  
% 5.84/2.13  Ordering : KBO
% 5.84/2.13  
% 5.84/2.13  Simplification rules
% 5.84/2.13  ----------------------
% 5.84/2.13  #Subsume      : 62
% 5.84/2.13  #Demod        : 499
% 5.84/2.13  #Tautology    : 243
% 5.84/2.13  #SimpNegUnit  : 112
% 5.84/2.13  #BackRed      : 5
% 5.84/2.13  
% 5.84/2.13  #Partial instantiations: 0
% 5.84/2.13  #Strategies tried      : 1
% 5.84/2.13  
% 5.84/2.13  Timing (in seconds)
% 5.84/2.13  ----------------------
% 5.84/2.13  Preprocessing        : 0.42
% 5.84/2.13  Parsing              : 0.22
% 5.84/2.13  CNF conversion       : 0.05
% 5.84/2.13  Main loop            : 0.85
% 5.84/2.13  Inferencing          : 0.29
% 5.84/2.13  Reduction            : 0.28
% 5.84/2.13  Demodulation         : 0.20
% 5.84/2.13  BG Simplification    : 0.04
% 5.84/2.13  Subsumption          : 0.18
% 5.84/2.13  Abstraction          : 0.05
% 5.84/2.13  MUC search           : 0.00
% 5.84/2.13  Cooper               : 0.00
% 5.84/2.13  Total                : 1.33
% 5.84/2.13  Index Insertion      : 0.00
% 5.84/2.13  Index Deletion       : 0.00
% 5.84/2.13  Index Matching       : 0.00
% 5.84/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
