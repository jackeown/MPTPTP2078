%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1697+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:15 EST 2020

% Result     : Theorem 14.87s
% Output     : CNFRefutation 14.97s
% Verified   : 
% Statistics : Number of formulae       :  204 (1712 expanded)
%              Number of leaves         :   39 ( 652 expanded)
%              Depth                    :   22
%              Number of atoms          :  781 (9739 expanded)
%              Number of equality atoms :  124 (1842 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r1_subset_1,type,(
    r1_subset_1: ( $i * $i ) > $o )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_213,negated_conjecture,(
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

tff(f_120,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_171,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_167,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(C,A)
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | ( v1_funct_1(k2_partfun1(A,B,D,C))
            & v1_funct_2(k2_partfun1(A,B,D,C),C,B)
            & m1_subset_1(k2_partfun1(A,B,D,C),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_148,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_146,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_144,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
       => r1_subset_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_subset_1)).

tff(f_134,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_124,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_119,axiom,(
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

tff(f_81,axiom,(
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

tff(c_76,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_72,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_70,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_22,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_84,plain,(
    ! [A_215] :
      ( k1_xboole_0 = A_215
      | ~ v1_xboole_0(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_88,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_84])).

tff(c_89,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_22])).

tff(c_56,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_54,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_839,plain,(
    ! [B_332,A_333,D_334,C_335] :
      ( k1_xboole_0 = B_332
      | v1_funct_1(k2_partfun1(A_333,B_332,D_334,C_335))
      | ~ r1_tarski(C_335,A_333)
      | ~ m1_subset_1(D_334,k1_zfmisc_1(k2_zfmisc_1(A_333,B_332)))
      | ~ v1_funct_2(D_334,A_333,B_332)
      | ~ v1_funct_1(D_334) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_841,plain,(
    ! [C_335] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_1(k2_partfun1('#skF_4','#skF_2','#skF_6',C_335))
      | ~ r1_tarski(C_335,'#skF_4')
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_52,c_839])).

tff(c_846,plain,(
    ! [C_335] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_1(k2_partfun1('#skF_4','#skF_2','#skF_6',C_335))
      | ~ r1_tarski(C_335,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_841])).

tff(c_850,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_846])).

tff(c_863,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_850,c_89])).

tff(c_868,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_863])).

tff(c_870,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_846])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_60,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_34,plain,(
    ! [A_151] : k3_xboole_0(A_151,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_94,plain,(
    ! [A_216,B_217] : r1_tarski(k3_xboole_0(A_216,B_217),A_216) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_97,plain,(
    ! [A_151] : r1_tarski(k1_xboole_0,A_151) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_94])).

tff(c_64,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_701,plain,(
    ! [B_310,A_311] :
      ( r1_subset_1(B_310,A_311)
      | ~ r1_subset_1(A_311,B_310)
      | v1_xboole_0(B_310)
      | v1_xboole_0(A_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_703,plain,
    ( r1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_701])).

tff(c_706,plain,(
    r1_subset_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_68,c_703])).

tff(c_683,plain,(
    ! [A_305,B_306] :
      ( r1_xboole_0(A_305,B_306)
      | ~ r1_subset_1(A_305,B_306)
      | v1_xboole_0(B_306)
      | v1_xboole_0(A_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_12,plain,(
    ! [A_134,B_135] :
      ( k3_xboole_0(A_134,B_135) = k1_xboole_0
      | ~ r1_xboole_0(A_134,B_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_778,plain,(
    ! [A_326,B_327] :
      ( k3_xboole_0(A_326,B_327) = k1_xboole_0
      | ~ r1_subset_1(A_326,B_327)
      | v1_xboole_0(B_327)
      | v1_xboole_0(A_326) ) ),
    inference(resolution,[status(thm)],[c_683,c_12])).

tff(c_784,plain,
    ( k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_706,c_778])).

tff(c_791,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_72,c_784])).

tff(c_4,plain,(
    ! [B_6,A_5] : k3_xboole_0(B_6,A_5) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_721,plain,(
    ! [A_314,B_315,C_316] :
      ( k9_subset_1(A_314,B_315,C_316) = k3_xboole_0(B_315,C_316)
      | ~ m1_subset_1(C_316,k1_zfmisc_1(A_314)) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_732,plain,(
    ! [B_315] : k9_subset_1('#skF_1',B_315,'#skF_4') = k3_xboole_0(B_315,'#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_721])).

tff(c_368,plain,(
    ! [B_258,A_259,D_260,C_261] :
      ( k1_xboole_0 = B_258
      | v1_funct_1(k2_partfun1(A_259,B_258,D_260,C_261))
      | ~ r1_tarski(C_261,A_259)
      | ~ m1_subset_1(D_260,k1_zfmisc_1(k2_zfmisc_1(A_259,B_258)))
      | ~ v1_funct_2(D_260,A_259,B_258)
      | ~ v1_funct_1(D_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_370,plain,(
    ! [C_261] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_1(k2_partfun1('#skF_4','#skF_2','#skF_6',C_261))
      | ~ r1_tarski(C_261,'#skF_4')
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_52,c_368])).

tff(c_375,plain,(
    ! [C_261] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_1(k2_partfun1('#skF_4','#skF_2','#skF_6',C_261))
      | ~ r1_tarski(C_261,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_370])).

tff(c_379,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_375])).

tff(c_393,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_89])).

tff(c_398,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_393])).

tff(c_400,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_375])).

tff(c_452,plain,(
    ! [B_276,A_277,D_278,C_279] :
      ( k1_xboole_0 = B_276
      | m1_subset_1(k2_partfun1(A_277,B_276,D_278,C_279),k1_zfmisc_1(k2_zfmisc_1(C_279,B_276)))
      | ~ r1_tarski(C_279,A_277)
      | ~ m1_subset_1(D_278,k1_zfmisc_1(k2_zfmisc_1(A_277,B_276)))
      | ~ v1_funct_2(D_278,A_277,B_276)
      | ~ v1_funct_1(D_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( v1_xboole_0(C_4)
      | ~ m1_subset_1(C_4,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_484,plain,(
    ! [A_280,B_281,D_282,C_283] :
      ( v1_xboole_0(k2_partfun1(A_280,B_281,D_282,C_283))
      | ~ v1_xboole_0(C_283)
      | k1_xboole_0 = B_281
      | ~ r1_tarski(C_283,A_280)
      | ~ m1_subset_1(D_282,k1_zfmisc_1(k2_zfmisc_1(A_280,B_281)))
      | ~ v1_funct_2(D_282,A_280,B_281)
      | ~ v1_funct_1(D_282) ) ),
    inference(resolution,[status(thm)],[c_452,c_2])).

tff(c_490,plain,(
    ! [C_283] :
      ( v1_xboole_0(k2_partfun1('#skF_4','#skF_2','#skF_6',C_283))
      | ~ v1_xboole_0(C_283)
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(C_283,'#skF_4')
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_52,c_484])).

tff(c_497,plain,(
    ! [C_283] :
      ( v1_xboole_0(k2_partfun1('#skF_4','#skF_2','#skF_6',C_283))
      | ~ v1_xboole_0(C_283)
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(C_283,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_490])).

tff(c_503,plain,(
    ! [C_284] :
      ( v1_xboole_0(k2_partfun1('#skF_4','#skF_2','#skF_6',C_284))
      | ~ v1_xboole_0(C_284)
      | ~ r1_tarski(C_284,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_400,c_497])).

tff(c_48,plain,(
    ! [A_156] :
      ( k1_xboole_0 = A_156
      | ~ v1_xboole_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_513,plain,(
    ! [C_286] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',C_286) = k1_xboole_0
      | ~ v1_xboole_0(C_286)
      | ~ r1_tarski(C_286,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_503,c_48])).

tff(c_521,plain,
    ( k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0) = k1_xboole_0
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_97,c_513])).

tff(c_529,plain,(
    k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_521])).

tff(c_236,plain,(
    ! [B_233,A_234] :
      ( r1_subset_1(B_233,A_234)
      | ~ r1_subset_1(A_234,B_233)
      | v1_xboole_0(B_233)
      | v1_xboole_0(A_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_238,plain,
    ( r1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_236])).

tff(c_241,plain,(
    r1_subset_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_68,c_238])).

tff(c_222,plain,(
    ! [A_228,B_229] :
      ( r1_xboole_0(A_228,B_229)
      | ~ r1_subset_1(A_228,B_229)
      | v1_xboole_0(B_229)
      | v1_xboole_0(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_305,plain,(
    ! [A_244,B_245] :
      ( k3_xboole_0(A_244,B_245) = k1_xboole_0
      | ~ r1_subset_1(A_244,B_245)
      | v1_xboole_0(B_245)
      | v1_xboole_0(A_244) ) ),
    inference(resolution,[status(thm)],[c_222,c_12])).

tff(c_308,plain,
    ( k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_241,c_305])).

tff(c_314,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_72,c_308])).

tff(c_256,plain,(
    ! [A_237,B_238,C_239] :
      ( k9_subset_1(A_237,B_238,C_239) = k3_xboole_0(B_238,C_239)
      | ~ m1_subset_1(C_239,k1_zfmisc_1(A_237)) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_267,plain,(
    ! [B_238] : k9_subset_1('#skF_1',B_238,'#skF_4') = k3_xboole_0(B_238,'#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_256])).

tff(c_50,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_221,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_347,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k1_xboole_0) != k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_314,c_4,c_267,c_4,c_267,c_221])).

tff(c_550,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_529,c_347])).

tff(c_492,plain,(
    ! [C_283] :
      ( v1_xboole_0(k2_partfun1('#skF_3','#skF_2','#skF_5',C_283))
      | ~ v1_xboole_0(C_283)
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(C_283,'#skF_3')
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_58,c_484])).

tff(c_501,plain,(
    ! [C_283] :
      ( v1_xboole_0(k2_partfun1('#skF_3','#skF_2','#skF_5',C_283))
      | ~ v1_xboole_0(C_283)
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(C_283,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_492])).

tff(c_508,plain,(
    ! [C_285] :
      ( v1_xboole_0(k2_partfun1('#skF_3','#skF_2','#skF_5',C_285))
      | ~ v1_xboole_0(C_285)
      | ~ r1_tarski(C_285,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_400,c_501])).

tff(c_662,plain,(
    ! [C_304] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',C_304) = k1_xboole_0
      | ~ v1_xboole_0(C_304)
      | ~ r1_tarski(C_304,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_508,c_48])).

tff(c_670,plain,
    ( k2_partfun1('#skF_3','#skF_2','#skF_5',k1_xboole_0) = k1_xboole_0
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_97,c_662])).

tff(c_678,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_670])).

tff(c_680,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_550,c_678])).

tff(c_682,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_734,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_732,c_732,c_682])).

tff(c_735,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_4','#skF_3')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_734])).

tff(c_834,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k1_xboole_0) = k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_791,c_791,c_735])).

tff(c_933,plain,(
    ! [B_353,A_354,D_355,C_356] :
      ( k1_xboole_0 = B_353
      | m1_subset_1(k2_partfun1(A_354,B_353,D_355,C_356),k1_zfmisc_1(k2_zfmisc_1(C_356,B_353)))
      | ~ r1_tarski(C_356,A_354)
      | ~ m1_subset_1(D_355,k1_zfmisc_1(k2_zfmisc_1(A_354,B_353)))
      | ~ v1_funct_2(D_355,A_354,B_353)
      | ~ v1_funct_1(D_355) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_954,plain,
    ( k1_xboole_0 = '#skF_2'
    | m1_subset_1(k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2')))
    | ~ r1_tarski(k1_xboole_0,'#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_834,c_933])).

tff(c_969,plain,
    ( k1_xboole_0 = '#skF_2'
    | m1_subset_1(k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_97,c_954])).

tff(c_970,plain,(
    m1_subset_1(k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_870,c_969])).

tff(c_985,plain,
    ( v1_xboole_0(k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_970,c_2])).

tff(c_1006,plain,(
    v1_xboole_0(k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_985])).

tff(c_1010,plain,(
    k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1006,c_48])).

tff(c_1040,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1010,c_834])).

tff(c_1011,plain,(
    ! [C_357,F_358,B_360,E_361,A_362,D_359] :
      ( v1_funct_1(k1_tmap_1(A_362,B_360,C_357,D_359,E_361,F_358))
      | ~ m1_subset_1(F_358,k1_zfmisc_1(k2_zfmisc_1(D_359,B_360)))
      | ~ v1_funct_2(F_358,D_359,B_360)
      | ~ v1_funct_1(F_358)
      | ~ m1_subset_1(E_361,k1_zfmisc_1(k2_zfmisc_1(C_357,B_360)))
      | ~ v1_funct_2(E_361,C_357,B_360)
      | ~ v1_funct_1(E_361)
      | ~ m1_subset_1(D_359,k1_zfmisc_1(A_362))
      | v1_xboole_0(D_359)
      | ~ m1_subset_1(C_357,k1_zfmisc_1(A_362))
      | v1_xboole_0(C_357)
      | v1_xboole_0(B_360)
      | v1_xboole_0(A_362) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1019,plain,(
    ! [A_362,C_357,E_361] :
      ( v1_funct_1(k1_tmap_1(A_362,'#skF_2',C_357,'#skF_4',E_361,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_361,k1_zfmisc_1(k2_zfmisc_1(C_357,'#skF_2')))
      | ~ v1_funct_2(E_361,C_357,'#skF_2')
      | ~ v1_funct_1(E_361)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_362))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_357,k1_zfmisc_1(A_362))
      | v1_xboole_0(C_357)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_362) ) ),
    inference(resolution,[status(thm)],[c_52,c_1011])).

tff(c_1030,plain,(
    ! [A_362,C_357,E_361] :
      ( v1_funct_1(k1_tmap_1(A_362,'#skF_2',C_357,'#skF_4',E_361,'#skF_6'))
      | ~ m1_subset_1(E_361,k1_zfmisc_1(k2_zfmisc_1(C_357,'#skF_2')))
      | ~ v1_funct_2(E_361,C_357,'#skF_2')
      | ~ v1_funct_1(E_361)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_362))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_357,k1_zfmisc_1(A_362))
      | v1_xboole_0(C_357)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_362) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_1019])).

tff(c_1301,plain,(
    ! [A_395,C_396,E_397] :
      ( v1_funct_1(k1_tmap_1(A_395,'#skF_2',C_396,'#skF_4',E_397,'#skF_6'))
      | ~ m1_subset_1(E_397,k1_zfmisc_1(k2_zfmisc_1(C_396,'#skF_2')))
      | ~ v1_funct_2(E_397,C_396,'#skF_2')
      | ~ v1_funct_1(E_397)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_395))
      | ~ m1_subset_1(C_396,k1_zfmisc_1(A_395))
      | v1_xboole_0(C_396)
      | v1_xboole_0(A_395) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_1030])).

tff(c_1316,plain,(
    ! [A_395] :
      ( v1_funct_1(k1_tmap_1(A_395,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_395))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_395))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_395) ) ),
    inference(resolution,[status(thm)],[c_58,c_1301])).

tff(c_1333,plain,(
    ! [A_395] :
      ( v1_funct_1(k1_tmap_1(A_395,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_395))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_395))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_395) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1316])).

tff(c_1547,plain,(
    ! [A_422] :
      ( v1_funct_1(k1_tmap_1(A_422,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_422))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_422))
      | v1_xboole_0(A_422) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1333])).

tff(c_1550,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_1547])).

tff(c_1553,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1550])).

tff(c_1554,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1553])).

tff(c_18,plain,(
    ! [E_140,B_137,F_141,A_136,C_138,D_139] :
      ( v1_funct_2(k1_tmap_1(A_136,B_137,C_138,D_139,E_140,F_141),k4_subset_1(A_136,C_138,D_139),B_137)
      | ~ m1_subset_1(F_141,k1_zfmisc_1(k2_zfmisc_1(D_139,B_137)))
      | ~ v1_funct_2(F_141,D_139,B_137)
      | ~ v1_funct_1(F_141)
      | ~ m1_subset_1(E_140,k1_zfmisc_1(k2_zfmisc_1(C_138,B_137)))
      | ~ v1_funct_2(E_140,C_138,B_137)
      | ~ v1_funct_1(E_140)
      | ~ m1_subset_1(D_139,k1_zfmisc_1(A_136))
      | v1_xboole_0(D_139)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(A_136))
      | v1_xboole_0(C_138)
      | v1_xboole_0(B_137)
      | v1_xboole_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_16,plain,(
    ! [E_140,B_137,F_141,A_136,C_138,D_139] :
      ( m1_subset_1(k1_tmap_1(A_136,B_137,C_138,D_139,E_140,F_141),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_136,C_138,D_139),B_137)))
      | ~ m1_subset_1(F_141,k1_zfmisc_1(k2_zfmisc_1(D_139,B_137)))
      | ~ v1_funct_2(F_141,D_139,B_137)
      | ~ v1_funct_1(F_141)
      | ~ m1_subset_1(E_140,k1_zfmisc_1(k2_zfmisc_1(C_138,B_137)))
      | ~ v1_funct_2(E_140,C_138,B_137)
      | ~ v1_funct_1(E_140)
      | ~ m1_subset_1(D_139,k1_zfmisc_1(A_136))
      | v1_xboole_0(D_139)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(A_136))
      | v1_xboole_0(C_138)
      | v1_xboole_0(B_137)
      | v1_xboole_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1267,plain,(
    ! [C_389,E_390,D_385,B_388,A_387,F_386] :
      ( k2_partfun1(k4_subset_1(A_387,C_389,D_385),B_388,k1_tmap_1(A_387,B_388,C_389,D_385,E_390,F_386),D_385) = F_386
      | ~ m1_subset_1(k1_tmap_1(A_387,B_388,C_389,D_385,E_390,F_386),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_387,C_389,D_385),B_388)))
      | ~ v1_funct_2(k1_tmap_1(A_387,B_388,C_389,D_385,E_390,F_386),k4_subset_1(A_387,C_389,D_385),B_388)
      | ~ v1_funct_1(k1_tmap_1(A_387,B_388,C_389,D_385,E_390,F_386))
      | k2_partfun1(D_385,B_388,F_386,k9_subset_1(A_387,C_389,D_385)) != k2_partfun1(C_389,B_388,E_390,k9_subset_1(A_387,C_389,D_385))
      | ~ m1_subset_1(F_386,k1_zfmisc_1(k2_zfmisc_1(D_385,B_388)))
      | ~ v1_funct_2(F_386,D_385,B_388)
      | ~ v1_funct_1(F_386)
      | ~ m1_subset_1(E_390,k1_zfmisc_1(k2_zfmisc_1(C_389,B_388)))
      | ~ v1_funct_2(E_390,C_389,B_388)
      | ~ v1_funct_1(E_390)
      | ~ m1_subset_1(D_385,k1_zfmisc_1(A_387))
      | v1_xboole_0(D_385)
      | ~ m1_subset_1(C_389,k1_zfmisc_1(A_387))
      | v1_xboole_0(C_389)
      | v1_xboole_0(B_388)
      | v1_xboole_0(A_387) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3004,plain,(
    ! [B_639,C_636,A_641,E_640,D_638,F_637] :
      ( k2_partfun1(k4_subset_1(A_641,C_636,D_638),B_639,k1_tmap_1(A_641,B_639,C_636,D_638,E_640,F_637),D_638) = F_637
      | ~ v1_funct_2(k1_tmap_1(A_641,B_639,C_636,D_638,E_640,F_637),k4_subset_1(A_641,C_636,D_638),B_639)
      | ~ v1_funct_1(k1_tmap_1(A_641,B_639,C_636,D_638,E_640,F_637))
      | k2_partfun1(D_638,B_639,F_637,k9_subset_1(A_641,C_636,D_638)) != k2_partfun1(C_636,B_639,E_640,k9_subset_1(A_641,C_636,D_638))
      | ~ m1_subset_1(F_637,k1_zfmisc_1(k2_zfmisc_1(D_638,B_639)))
      | ~ v1_funct_2(F_637,D_638,B_639)
      | ~ v1_funct_1(F_637)
      | ~ m1_subset_1(E_640,k1_zfmisc_1(k2_zfmisc_1(C_636,B_639)))
      | ~ v1_funct_2(E_640,C_636,B_639)
      | ~ v1_funct_1(E_640)
      | ~ m1_subset_1(D_638,k1_zfmisc_1(A_641))
      | v1_xboole_0(D_638)
      | ~ m1_subset_1(C_636,k1_zfmisc_1(A_641))
      | v1_xboole_0(C_636)
      | v1_xboole_0(B_639)
      | v1_xboole_0(A_641) ) ),
    inference(resolution,[status(thm)],[c_16,c_1267])).

tff(c_14596,plain,(
    ! [B_1004,D_1003,F_1002,C_1001,E_1005,A_1006] :
      ( k2_partfun1(k4_subset_1(A_1006,C_1001,D_1003),B_1004,k1_tmap_1(A_1006,B_1004,C_1001,D_1003,E_1005,F_1002),D_1003) = F_1002
      | ~ v1_funct_1(k1_tmap_1(A_1006,B_1004,C_1001,D_1003,E_1005,F_1002))
      | k2_partfun1(D_1003,B_1004,F_1002,k9_subset_1(A_1006,C_1001,D_1003)) != k2_partfun1(C_1001,B_1004,E_1005,k9_subset_1(A_1006,C_1001,D_1003))
      | ~ m1_subset_1(F_1002,k1_zfmisc_1(k2_zfmisc_1(D_1003,B_1004)))
      | ~ v1_funct_2(F_1002,D_1003,B_1004)
      | ~ v1_funct_1(F_1002)
      | ~ m1_subset_1(E_1005,k1_zfmisc_1(k2_zfmisc_1(C_1001,B_1004)))
      | ~ v1_funct_2(E_1005,C_1001,B_1004)
      | ~ v1_funct_1(E_1005)
      | ~ m1_subset_1(D_1003,k1_zfmisc_1(A_1006))
      | v1_xboole_0(D_1003)
      | ~ m1_subset_1(C_1001,k1_zfmisc_1(A_1006))
      | v1_xboole_0(C_1001)
      | v1_xboole_0(B_1004)
      | v1_xboole_0(A_1006) ) ),
    inference(resolution,[status(thm)],[c_18,c_3004])).

tff(c_14628,plain,(
    ! [A_1006,C_1001,E_1005] :
      ( k2_partfun1(k4_subset_1(A_1006,C_1001,'#skF_4'),'#skF_2',k1_tmap_1(A_1006,'#skF_2',C_1001,'#skF_4',E_1005,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1006,'#skF_2',C_1001,'#skF_4',E_1005,'#skF_6'))
      | k2_partfun1(C_1001,'#skF_2',E_1005,k9_subset_1(A_1006,C_1001,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_1006,C_1001,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1005,k1_zfmisc_1(k2_zfmisc_1(C_1001,'#skF_2')))
      | ~ v1_funct_2(E_1005,C_1001,'#skF_2')
      | ~ v1_funct_1(E_1005)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1006))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1001,k1_zfmisc_1(A_1006))
      | v1_xboole_0(C_1001)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1006) ) ),
    inference(resolution,[status(thm)],[c_52,c_14596])).

tff(c_14684,plain,(
    ! [A_1006,C_1001,E_1005] :
      ( k2_partfun1(k4_subset_1(A_1006,C_1001,'#skF_4'),'#skF_2',k1_tmap_1(A_1006,'#skF_2',C_1001,'#skF_4',E_1005,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1006,'#skF_2',C_1001,'#skF_4',E_1005,'#skF_6'))
      | k2_partfun1(C_1001,'#skF_2',E_1005,k9_subset_1(A_1006,C_1001,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_1006,C_1001,'#skF_4'))
      | ~ m1_subset_1(E_1005,k1_zfmisc_1(k2_zfmisc_1(C_1001,'#skF_2')))
      | ~ v1_funct_2(E_1005,C_1001,'#skF_2')
      | ~ v1_funct_1(E_1005)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1006))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1001,k1_zfmisc_1(A_1006))
      | v1_xboole_0(C_1001)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1006) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_14628])).

tff(c_23110,plain,(
    ! [A_1094,C_1095,E_1096] :
      ( k2_partfun1(k4_subset_1(A_1094,C_1095,'#skF_4'),'#skF_2',k1_tmap_1(A_1094,'#skF_2',C_1095,'#skF_4',E_1096,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1094,'#skF_2',C_1095,'#skF_4',E_1096,'#skF_6'))
      | k2_partfun1(C_1095,'#skF_2',E_1096,k9_subset_1(A_1094,C_1095,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_1094,C_1095,'#skF_4'))
      | ~ m1_subset_1(E_1096,k1_zfmisc_1(k2_zfmisc_1(C_1095,'#skF_2')))
      | ~ v1_funct_2(E_1096,C_1095,'#skF_2')
      | ~ v1_funct_1(E_1096)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1094))
      | ~ m1_subset_1(C_1095,k1_zfmisc_1(A_1094))
      | v1_xboole_0(C_1095)
      | v1_xboole_0(A_1094) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_14684])).

tff(c_23151,plain,(
    ! [A_1094] :
      ( k2_partfun1(k4_subset_1(A_1094,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1094,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1094,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1094,'#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_1094,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1094))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1094))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1094) ) ),
    inference(resolution,[status(thm)],[c_58,c_23110])).

tff(c_23207,plain,(
    ! [A_1094] :
      ( k2_partfun1(k4_subset_1(A_1094,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1094,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1094,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1094,'#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_1094,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1094))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1094))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1094) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_23151])).

tff(c_23586,plain,(
    ! [A_1111] :
      ( k2_partfun1(k4_subset_1(A_1111,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1111,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1111,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1111,'#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_1111,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1111))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1111))
      | v1_xboole_0(A_1111) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_23207])).

tff(c_681,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_773,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_681])).

tff(c_23636,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_23586,c_773])).

tff(c_23672,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_1040,c_1010,c_791,c_4,c_791,c_4,c_732,c_732,c_1554,c_23636])).

tff(c_23674,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_23672])).

tff(c_23675,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_681])).

tff(c_23746,plain,(
    ! [B_1120,A_1121,D_1122,C_1123] :
      ( k1_xboole_0 = B_1120
      | v1_funct_1(k2_partfun1(A_1121,B_1120,D_1122,C_1123))
      | ~ r1_tarski(C_1123,A_1121)
      | ~ m1_subset_1(D_1122,k1_zfmisc_1(k2_zfmisc_1(A_1121,B_1120)))
      | ~ v1_funct_2(D_1122,A_1121,B_1120)
      | ~ v1_funct_1(D_1122) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_23748,plain,(
    ! [C_1123] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_1(k2_partfun1('#skF_4','#skF_2','#skF_6',C_1123))
      | ~ r1_tarski(C_1123,'#skF_4')
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_52,c_23746])).

tff(c_23753,plain,(
    ! [C_1123] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_1(k2_partfun1('#skF_4','#skF_2','#skF_6',C_1123))
      | ~ r1_tarski(C_1123,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_23748])).

tff(c_23757,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_23753])).

tff(c_23770,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23757,c_89])).

tff(c_23775,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_23770])).

tff(c_23777,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_23753])).

tff(c_23681,plain,(
    ! [A_1114,B_1115] :
      ( k3_xboole_0(A_1114,B_1115) = k1_xboole_0
      | ~ r1_subset_1(A_1114,B_1115)
      | v1_xboole_0(B_1115)
      | v1_xboole_0(A_1114) ) ),
    inference(resolution,[status(thm)],[c_683,c_12])).

tff(c_23687,plain,
    ( k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_706,c_23681])).

tff(c_23694,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_72,c_23687])).

tff(c_23741,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k1_xboole_0) = k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23694,c_23694,c_735])).

tff(c_23840,plain,(
    ! [B_1141,A_1142,D_1143,C_1144] :
      ( k1_xboole_0 = B_1141
      | m1_subset_1(k2_partfun1(A_1142,B_1141,D_1143,C_1144),k1_zfmisc_1(k2_zfmisc_1(C_1144,B_1141)))
      | ~ r1_tarski(C_1144,A_1142)
      | ~ m1_subset_1(D_1143,k1_zfmisc_1(k2_zfmisc_1(A_1142,B_1141)))
      | ~ v1_funct_2(D_1143,A_1142,B_1141)
      | ~ v1_funct_1(D_1143) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_23861,plain,
    ( k1_xboole_0 = '#skF_2'
    | m1_subset_1(k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2')))
    | ~ r1_tarski(k1_xboole_0,'#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_23741,c_23840])).

tff(c_23879,plain,
    ( k1_xboole_0 = '#skF_2'
    | m1_subset_1(k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_97,c_23861])).

tff(c_23880,plain,(
    m1_subset_1(k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_23777,c_23879])).

tff(c_23897,plain,
    ( v1_xboole_0(k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_23880,c_2])).

tff(c_23918,plain,(
    v1_xboole_0(k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_23897])).

tff(c_23947,plain,(
    k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_23918,c_48])).

tff(c_23952,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_23947,c_23741])).

tff(c_23919,plain,(
    ! [D_1147,B_1148,A_1150,F_1146,E_1149,C_1145] :
      ( v1_funct_1(k1_tmap_1(A_1150,B_1148,C_1145,D_1147,E_1149,F_1146))
      | ~ m1_subset_1(F_1146,k1_zfmisc_1(k2_zfmisc_1(D_1147,B_1148)))
      | ~ v1_funct_2(F_1146,D_1147,B_1148)
      | ~ v1_funct_1(F_1146)
      | ~ m1_subset_1(E_1149,k1_zfmisc_1(k2_zfmisc_1(C_1145,B_1148)))
      | ~ v1_funct_2(E_1149,C_1145,B_1148)
      | ~ v1_funct_1(E_1149)
      | ~ m1_subset_1(D_1147,k1_zfmisc_1(A_1150))
      | v1_xboole_0(D_1147)
      | ~ m1_subset_1(C_1145,k1_zfmisc_1(A_1150))
      | v1_xboole_0(C_1145)
      | v1_xboole_0(B_1148)
      | v1_xboole_0(A_1150) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_23927,plain,(
    ! [A_1150,C_1145,E_1149] :
      ( v1_funct_1(k1_tmap_1(A_1150,'#skF_2',C_1145,'#skF_4',E_1149,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1149,k1_zfmisc_1(k2_zfmisc_1(C_1145,'#skF_2')))
      | ~ v1_funct_2(E_1149,C_1145,'#skF_2')
      | ~ v1_funct_1(E_1149)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1150))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1145,k1_zfmisc_1(A_1150))
      | v1_xboole_0(C_1145)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1150) ) ),
    inference(resolution,[status(thm)],[c_52,c_23919])).

tff(c_23938,plain,(
    ! [A_1150,C_1145,E_1149] :
      ( v1_funct_1(k1_tmap_1(A_1150,'#skF_2',C_1145,'#skF_4',E_1149,'#skF_6'))
      | ~ m1_subset_1(E_1149,k1_zfmisc_1(k2_zfmisc_1(C_1145,'#skF_2')))
      | ~ v1_funct_2(E_1149,C_1145,'#skF_2')
      | ~ v1_funct_1(E_1149)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1150))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1145,k1_zfmisc_1(A_1150))
      | v1_xboole_0(C_1145)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_23927])).

tff(c_23974,plain,(
    ! [A_1151,C_1152,E_1153] :
      ( v1_funct_1(k1_tmap_1(A_1151,'#skF_2',C_1152,'#skF_4',E_1153,'#skF_6'))
      | ~ m1_subset_1(E_1153,k1_zfmisc_1(k2_zfmisc_1(C_1152,'#skF_2')))
      | ~ v1_funct_2(E_1153,C_1152,'#skF_2')
      | ~ v1_funct_1(E_1153)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1151))
      | ~ m1_subset_1(C_1152,k1_zfmisc_1(A_1151))
      | v1_xboole_0(C_1152)
      | v1_xboole_0(A_1151) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_23938])).

tff(c_23984,plain,(
    ! [A_1151] :
      ( v1_funct_1(k1_tmap_1(A_1151,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1151))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1151))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1151) ) ),
    inference(resolution,[status(thm)],[c_58,c_23974])).

tff(c_23995,plain,(
    ! [A_1151] :
      ( v1_funct_1(k1_tmap_1(A_1151,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1151))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1151))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_23984])).

tff(c_24166,plain,(
    ! [A_1172] :
      ( v1_funct_1(k1_tmap_1(A_1172,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1172))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1172))
      | v1_xboole_0(A_1172) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_23995])).

tff(c_24169,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_24166])).

tff(c_24172,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_24169])).

tff(c_24173,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_24172])).

tff(c_24090,plain,(
    ! [C_1165,B_1168,E_1169,D_1167,F_1166,A_1170] :
      ( m1_subset_1(k1_tmap_1(A_1170,B_1168,C_1165,D_1167,E_1169,F_1166),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1170,C_1165,D_1167),B_1168)))
      | ~ m1_subset_1(F_1166,k1_zfmisc_1(k2_zfmisc_1(D_1167,B_1168)))
      | ~ v1_funct_2(F_1166,D_1167,B_1168)
      | ~ v1_funct_1(F_1166)
      | ~ m1_subset_1(E_1169,k1_zfmisc_1(k2_zfmisc_1(C_1165,B_1168)))
      | ~ v1_funct_2(E_1169,C_1165,B_1168)
      | ~ v1_funct_1(E_1169)
      | ~ m1_subset_1(D_1167,k1_zfmisc_1(A_1170))
      | v1_xboole_0(D_1167)
      | ~ m1_subset_1(C_1165,k1_zfmisc_1(A_1170))
      | v1_xboole_0(C_1165)
      | v1_xboole_0(B_1168)
      | v1_xboole_0(A_1170) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_46,plain,(
    ! [B_153,A_152,D_155,C_154] :
      ( k1_xboole_0 = B_153
      | v1_funct_1(k2_partfun1(A_152,B_153,D_155,C_154))
      | ~ r1_tarski(C_154,A_152)
      | ~ m1_subset_1(D_155,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153)))
      | ~ v1_funct_2(D_155,A_152,B_153)
      | ~ v1_funct_1(D_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_25585,plain,(
    ! [E_1381,C_1378,A_1377,C_1380,D_1379,B_1382,F_1383] :
      ( k1_xboole_0 = B_1382
      | v1_funct_1(k2_partfun1(k4_subset_1(A_1377,C_1378,D_1379),B_1382,k1_tmap_1(A_1377,B_1382,C_1378,D_1379,E_1381,F_1383),C_1380))
      | ~ r1_tarski(C_1380,k4_subset_1(A_1377,C_1378,D_1379))
      | ~ v1_funct_2(k1_tmap_1(A_1377,B_1382,C_1378,D_1379,E_1381,F_1383),k4_subset_1(A_1377,C_1378,D_1379),B_1382)
      | ~ v1_funct_1(k1_tmap_1(A_1377,B_1382,C_1378,D_1379,E_1381,F_1383))
      | ~ m1_subset_1(F_1383,k1_zfmisc_1(k2_zfmisc_1(D_1379,B_1382)))
      | ~ v1_funct_2(F_1383,D_1379,B_1382)
      | ~ v1_funct_1(F_1383)
      | ~ m1_subset_1(E_1381,k1_zfmisc_1(k2_zfmisc_1(C_1378,B_1382)))
      | ~ v1_funct_2(E_1381,C_1378,B_1382)
      | ~ v1_funct_1(E_1381)
      | ~ m1_subset_1(D_1379,k1_zfmisc_1(A_1377))
      | v1_xboole_0(D_1379)
      | ~ m1_subset_1(C_1378,k1_zfmisc_1(A_1377))
      | v1_xboole_0(C_1378)
      | v1_xboole_0(B_1382)
      | v1_xboole_0(A_1377) ) ),
    inference(resolution,[status(thm)],[c_24090,c_46])).

tff(c_23676,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_681])).

tff(c_24393,plain,(
    ! [D_1208,B_1211,C_1212,A_1209,G_1210] :
      ( k1_tmap_1(A_1209,B_1211,C_1212,D_1208,k2_partfun1(k4_subset_1(A_1209,C_1212,D_1208),B_1211,G_1210,C_1212),k2_partfun1(k4_subset_1(A_1209,C_1212,D_1208),B_1211,G_1210,D_1208)) = G_1210
      | ~ m1_subset_1(G_1210,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1209,C_1212,D_1208),B_1211)))
      | ~ v1_funct_2(G_1210,k4_subset_1(A_1209,C_1212,D_1208),B_1211)
      | ~ v1_funct_1(G_1210)
      | k2_partfun1(D_1208,B_1211,k2_partfun1(k4_subset_1(A_1209,C_1212,D_1208),B_1211,G_1210,D_1208),k9_subset_1(A_1209,C_1212,D_1208)) != k2_partfun1(C_1212,B_1211,k2_partfun1(k4_subset_1(A_1209,C_1212,D_1208),B_1211,G_1210,C_1212),k9_subset_1(A_1209,C_1212,D_1208))
      | ~ m1_subset_1(k2_partfun1(k4_subset_1(A_1209,C_1212,D_1208),B_1211,G_1210,D_1208),k1_zfmisc_1(k2_zfmisc_1(D_1208,B_1211)))
      | ~ v1_funct_2(k2_partfun1(k4_subset_1(A_1209,C_1212,D_1208),B_1211,G_1210,D_1208),D_1208,B_1211)
      | ~ v1_funct_1(k2_partfun1(k4_subset_1(A_1209,C_1212,D_1208),B_1211,G_1210,D_1208))
      | ~ m1_subset_1(k2_partfun1(k4_subset_1(A_1209,C_1212,D_1208),B_1211,G_1210,C_1212),k1_zfmisc_1(k2_zfmisc_1(C_1212,B_1211)))
      | ~ v1_funct_2(k2_partfun1(k4_subset_1(A_1209,C_1212,D_1208),B_1211,G_1210,C_1212),C_1212,B_1211)
      | ~ v1_funct_1(k2_partfun1(k4_subset_1(A_1209,C_1212,D_1208),B_1211,G_1210,C_1212))
      | ~ m1_subset_1(D_1208,k1_zfmisc_1(A_1209))
      | v1_xboole_0(D_1208)
      | ~ m1_subset_1(C_1212,k1_zfmisc_1(A_1209))
      | v1_xboole_0(C_1212)
      | v1_xboole_0(B_1211)
      | v1_xboole_0(A_1209) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_24398,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_23676,c_24393])).

tff(c_24401,plain,
    ( k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_6') = k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')))
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | k2_partfun1('#skF_3','#skF_2',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_xboole_0) != k1_xboole_0
    | ~ m1_subset_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'))
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_56,c_23676,c_54,c_23676,c_52,c_23947,c_23694,c_4,c_23694,c_4,c_732,c_732,c_23676,c_24173,c_23676,c_24398])).

tff(c_24402,plain,
    ( k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_6') = k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')))
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | k2_partfun1('#skF_3','#skF_2',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_xboole_0) != k1_xboole_0
    | ~ m1_subset_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_74,c_72,c_68,c_24401])).

tff(c_24548,plain,(
    ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_24402])).

tff(c_25588,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_3',k4_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
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
    inference(resolution,[status(thm)],[c_25585,c_24548])).

tff(c_25594,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_3',k4_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_62,c_60,c_58,c_56,c_54,c_52,c_24173,c_25588])).

tff(c_25595,plain,
    ( ~ r1_tarski('#skF_3',k4_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_74,c_72,c_68,c_23777,c_25594])).

tff(c_25621,plain,(
    ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_25595])).

tff(c_25624,plain,
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
    inference(resolution,[status(thm)],[c_18,c_25621])).

tff(c_25627,plain,
    ( v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_62,c_60,c_58,c_56,c_54,c_52,c_25624])).

tff(c_25629,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_74,c_72,c_68,c_25627])).

tff(c_25631,plain,(
    v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_25595])).

tff(c_24262,plain,(
    ! [B_1191,F_1189,C_1192,A_1190,D_1188,E_1193] :
      ( k2_partfun1(k4_subset_1(A_1190,C_1192,D_1188),B_1191,k1_tmap_1(A_1190,B_1191,C_1192,D_1188,E_1193,F_1189),C_1192) = E_1193
      | ~ m1_subset_1(k1_tmap_1(A_1190,B_1191,C_1192,D_1188,E_1193,F_1189),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1190,C_1192,D_1188),B_1191)))
      | ~ v1_funct_2(k1_tmap_1(A_1190,B_1191,C_1192,D_1188,E_1193,F_1189),k4_subset_1(A_1190,C_1192,D_1188),B_1191)
      | ~ v1_funct_1(k1_tmap_1(A_1190,B_1191,C_1192,D_1188,E_1193,F_1189))
      | k2_partfun1(D_1188,B_1191,F_1189,k9_subset_1(A_1190,C_1192,D_1188)) != k2_partfun1(C_1192,B_1191,E_1193,k9_subset_1(A_1190,C_1192,D_1188))
      | ~ m1_subset_1(F_1189,k1_zfmisc_1(k2_zfmisc_1(D_1188,B_1191)))
      | ~ v1_funct_2(F_1189,D_1188,B_1191)
      | ~ v1_funct_1(F_1189)
      | ~ m1_subset_1(E_1193,k1_zfmisc_1(k2_zfmisc_1(C_1192,B_1191)))
      | ~ v1_funct_2(E_1193,C_1192,B_1191)
      | ~ v1_funct_1(E_1193)
      | ~ m1_subset_1(D_1188,k1_zfmisc_1(A_1190))
      | v1_xboole_0(D_1188)
      | ~ m1_subset_1(C_1192,k1_zfmisc_1(A_1190))
      | v1_xboole_0(C_1192)
      | v1_xboole_0(B_1191)
      | v1_xboole_0(A_1190) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_25846,plain,(
    ! [A_1418,C_1413,B_1416,E_1417,D_1415,F_1414] :
      ( k2_partfun1(k4_subset_1(A_1418,C_1413,D_1415),B_1416,k1_tmap_1(A_1418,B_1416,C_1413,D_1415,E_1417,F_1414),C_1413) = E_1417
      | ~ v1_funct_2(k1_tmap_1(A_1418,B_1416,C_1413,D_1415,E_1417,F_1414),k4_subset_1(A_1418,C_1413,D_1415),B_1416)
      | ~ v1_funct_1(k1_tmap_1(A_1418,B_1416,C_1413,D_1415,E_1417,F_1414))
      | k2_partfun1(D_1415,B_1416,F_1414,k9_subset_1(A_1418,C_1413,D_1415)) != k2_partfun1(C_1413,B_1416,E_1417,k9_subset_1(A_1418,C_1413,D_1415))
      | ~ m1_subset_1(F_1414,k1_zfmisc_1(k2_zfmisc_1(D_1415,B_1416)))
      | ~ v1_funct_2(F_1414,D_1415,B_1416)
      | ~ v1_funct_1(F_1414)
      | ~ m1_subset_1(E_1417,k1_zfmisc_1(k2_zfmisc_1(C_1413,B_1416)))
      | ~ v1_funct_2(E_1417,C_1413,B_1416)
      | ~ v1_funct_1(E_1417)
      | ~ m1_subset_1(D_1415,k1_zfmisc_1(A_1418))
      | v1_xboole_0(D_1415)
      | ~ m1_subset_1(C_1413,k1_zfmisc_1(A_1418))
      | v1_xboole_0(C_1413)
      | v1_xboole_0(B_1416)
      | v1_xboole_0(A_1418) ) ),
    inference(resolution,[status(thm)],[c_16,c_24262])).

tff(c_25848,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
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
    inference(resolution,[status(thm)],[c_25631,c_25846])).

tff(c_25853,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_62,c_60,c_58,c_56,c_54,c_52,c_23947,c_23694,c_4,c_23952,c_23694,c_4,c_732,c_732,c_24173,c_25848])).

tff(c_25855,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_74,c_72,c_68,c_23675,c_25853])).

%------------------------------------------------------------------------------
