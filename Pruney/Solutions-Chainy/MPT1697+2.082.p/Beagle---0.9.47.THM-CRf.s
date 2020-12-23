%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:22 EST 2020

% Result     : Theorem 4.62s
% Output     : CNFRefutation 4.62s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 412 expanded)
%              Number of leaves         :   35 ( 168 expanded)
%              Depth                    :   12
%              Number of atoms          :  538 (2432 expanded)
%              Number of equality atoms :   84 ( 432 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_186,negated_conjecture,(
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

tff(f_42,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_56,axiom,(
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

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_144,axiom,(
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

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_110,axiom,(
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

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_10,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_78,plain,(
    ! [B_217,A_218] :
      ( v1_relat_1(B_217)
      | ~ m1_subset_1(B_217,k1_zfmisc_1(A_218))
      | ~ v1_relat_1(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_84,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_78])).

tff(c_96,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_84])).

tff(c_12,plain,(
    ! [A_11] :
      ( k7_relat_1(A_11,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_237,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_96,c_12])).

tff(c_34,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_81,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_78])).

tff(c_93,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_81])).

tff(c_233,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_93,c_12])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_46,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_256,plain,(
    ! [A_242,B_243] :
      ( r1_xboole_0(A_242,B_243)
      | ~ r1_subset_1(A_242,B_243)
      | v1_xboole_0(B_243)
      | v1_xboole_0(A_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_345,plain,(
    ! [A_259,B_260] :
      ( k3_xboole_0(A_259,B_260) = k1_xboole_0
      | ~ r1_subset_1(A_259,B_260)
      | v1_xboole_0(B_260)
      | v1_xboole_0(A_259) ) ),
    inference(resolution,[status(thm)],[c_256,c_2])).

tff(c_351,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_345])).

tff(c_355,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_50,c_351])).

tff(c_265,plain,(
    ! [A_244,B_245,C_246] :
      ( k9_subset_1(A_244,B_245,C_246) = k3_xboole_0(B_245,C_246)
      | ~ m1_subset_1(C_246,k1_zfmisc_1(A_244)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_276,plain,(
    ! [B_245] : k9_subset_1('#skF_1',B_245,'#skF_4') = k3_xboole_0(B_245,'#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_265])).

tff(c_44,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_42,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_38,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_36,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_817,plain,(
    ! [D_376,E_381,B_379,F_380,A_378,C_377] :
      ( v1_funct_1(k1_tmap_1(A_378,B_379,C_377,D_376,E_381,F_380))
      | ~ m1_subset_1(F_380,k1_zfmisc_1(k2_zfmisc_1(D_376,B_379)))
      | ~ v1_funct_2(F_380,D_376,B_379)
      | ~ v1_funct_1(F_380)
      | ~ m1_subset_1(E_381,k1_zfmisc_1(k2_zfmisc_1(C_377,B_379)))
      | ~ v1_funct_2(E_381,C_377,B_379)
      | ~ v1_funct_1(E_381)
      | ~ m1_subset_1(D_376,k1_zfmisc_1(A_378))
      | v1_xboole_0(D_376)
      | ~ m1_subset_1(C_377,k1_zfmisc_1(A_378))
      | v1_xboole_0(C_377)
      | v1_xboole_0(B_379)
      | v1_xboole_0(A_378) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_819,plain,(
    ! [A_378,C_377,E_381] :
      ( v1_funct_1(k1_tmap_1(A_378,'#skF_2',C_377,'#skF_4',E_381,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_381,k1_zfmisc_1(k2_zfmisc_1(C_377,'#skF_2')))
      | ~ v1_funct_2(E_381,C_377,'#skF_2')
      | ~ v1_funct_1(E_381)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_378))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_377,k1_zfmisc_1(A_378))
      | v1_xboole_0(C_377)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_378) ) ),
    inference(resolution,[status(thm)],[c_34,c_817])).

tff(c_824,plain,(
    ! [A_378,C_377,E_381] :
      ( v1_funct_1(k1_tmap_1(A_378,'#skF_2',C_377,'#skF_4',E_381,'#skF_6'))
      | ~ m1_subset_1(E_381,k1_zfmisc_1(k2_zfmisc_1(C_377,'#skF_2')))
      | ~ v1_funct_2(E_381,C_377,'#skF_2')
      | ~ v1_funct_1(E_381)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_378))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_377,k1_zfmisc_1(A_378))
      | v1_xboole_0(C_377)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_378) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_819])).

tff(c_830,plain,(
    ! [A_382,C_383,E_384] :
      ( v1_funct_1(k1_tmap_1(A_382,'#skF_2',C_383,'#skF_4',E_384,'#skF_6'))
      | ~ m1_subset_1(E_384,k1_zfmisc_1(k2_zfmisc_1(C_383,'#skF_2')))
      | ~ v1_funct_2(E_384,C_383,'#skF_2')
      | ~ v1_funct_1(E_384)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_382))
      | ~ m1_subset_1(C_383,k1_zfmisc_1(A_382))
      | v1_xboole_0(C_383)
      | v1_xboole_0(A_382) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_50,c_824])).

tff(c_834,plain,(
    ! [A_382] :
      ( v1_funct_1(k1_tmap_1(A_382,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_382))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_382))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_382) ) ),
    inference(resolution,[status(thm)],[c_40,c_830])).

tff(c_841,plain,(
    ! [A_382] :
      ( v1_funct_1(k1_tmap_1(A_382,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_382))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_382))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_382) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_834])).

tff(c_850,plain,(
    ! [A_386] :
      ( v1_funct_1(k1_tmap_1(A_386,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_386))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_386))
      | v1_xboole_0(A_386) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_841])).

tff(c_853,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_850])).

tff(c_856,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_853])).

tff(c_857,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_856])).

tff(c_297,plain,(
    ! [A_249,B_250,C_251,D_252] :
      ( k2_partfun1(A_249,B_250,C_251,D_252) = k7_relat_1(C_251,D_252)
      | ~ m1_subset_1(C_251,k1_zfmisc_1(k2_zfmisc_1(A_249,B_250)))
      | ~ v1_funct_1(C_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_301,plain,(
    ! [D_252] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_252) = k7_relat_1('#skF_5',D_252)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_297])).

tff(c_307,plain,(
    ! [D_252] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_252) = k7_relat_1('#skF_5',D_252) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_301])).

tff(c_299,plain,(
    ! [D_252] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_252) = k7_relat_1('#skF_6',D_252)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_34,c_297])).

tff(c_304,plain,(
    ! [D_252] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_252) = k7_relat_1('#skF_6',D_252) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_299])).

tff(c_28,plain,(
    ! [E_149,C_147,A_145,D_148,F_150,B_146] :
      ( v1_funct_2(k1_tmap_1(A_145,B_146,C_147,D_148,E_149,F_150),k4_subset_1(A_145,C_147,D_148),B_146)
      | ~ m1_subset_1(F_150,k1_zfmisc_1(k2_zfmisc_1(D_148,B_146)))
      | ~ v1_funct_2(F_150,D_148,B_146)
      | ~ v1_funct_1(F_150)
      | ~ m1_subset_1(E_149,k1_zfmisc_1(k2_zfmisc_1(C_147,B_146)))
      | ~ v1_funct_2(E_149,C_147,B_146)
      | ~ v1_funct_1(E_149)
      | ~ m1_subset_1(D_148,k1_zfmisc_1(A_145))
      | v1_xboole_0(D_148)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(A_145))
      | v1_xboole_0(C_147)
      | v1_xboole_0(B_146)
      | v1_xboole_0(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_26,plain,(
    ! [E_149,C_147,A_145,D_148,F_150,B_146] :
      ( m1_subset_1(k1_tmap_1(A_145,B_146,C_147,D_148,E_149,F_150),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_145,C_147,D_148),B_146)))
      | ~ m1_subset_1(F_150,k1_zfmisc_1(k2_zfmisc_1(D_148,B_146)))
      | ~ v1_funct_2(F_150,D_148,B_146)
      | ~ v1_funct_1(F_150)
      | ~ m1_subset_1(E_149,k1_zfmisc_1(k2_zfmisc_1(C_147,B_146)))
      | ~ v1_funct_2(E_149,C_147,B_146)
      | ~ v1_funct_1(E_149)
      | ~ m1_subset_1(D_148,k1_zfmisc_1(A_145))
      | v1_xboole_0(D_148)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(A_145))
      | v1_xboole_0(C_147)
      | v1_xboole_0(B_146)
      | v1_xboole_0(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_965,plain,(
    ! [B_419,A_415,C_417,D_418,F_414,E_416] :
      ( k2_partfun1(k4_subset_1(A_415,C_417,D_418),B_419,k1_tmap_1(A_415,B_419,C_417,D_418,E_416,F_414),C_417) = E_416
      | ~ m1_subset_1(k1_tmap_1(A_415,B_419,C_417,D_418,E_416,F_414),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_415,C_417,D_418),B_419)))
      | ~ v1_funct_2(k1_tmap_1(A_415,B_419,C_417,D_418,E_416,F_414),k4_subset_1(A_415,C_417,D_418),B_419)
      | ~ v1_funct_1(k1_tmap_1(A_415,B_419,C_417,D_418,E_416,F_414))
      | k2_partfun1(D_418,B_419,F_414,k9_subset_1(A_415,C_417,D_418)) != k2_partfun1(C_417,B_419,E_416,k9_subset_1(A_415,C_417,D_418))
      | ~ m1_subset_1(F_414,k1_zfmisc_1(k2_zfmisc_1(D_418,B_419)))
      | ~ v1_funct_2(F_414,D_418,B_419)
      | ~ v1_funct_1(F_414)
      | ~ m1_subset_1(E_416,k1_zfmisc_1(k2_zfmisc_1(C_417,B_419)))
      | ~ v1_funct_2(E_416,C_417,B_419)
      | ~ v1_funct_1(E_416)
      | ~ m1_subset_1(D_418,k1_zfmisc_1(A_415))
      | v1_xboole_0(D_418)
      | ~ m1_subset_1(C_417,k1_zfmisc_1(A_415))
      | v1_xboole_0(C_417)
      | v1_xboole_0(B_419)
      | v1_xboole_0(A_415) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1188,plain,(
    ! [A_475,F_477,C_474,E_478,D_473,B_476] :
      ( k2_partfun1(k4_subset_1(A_475,C_474,D_473),B_476,k1_tmap_1(A_475,B_476,C_474,D_473,E_478,F_477),C_474) = E_478
      | ~ v1_funct_2(k1_tmap_1(A_475,B_476,C_474,D_473,E_478,F_477),k4_subset_1(A_475,C_474,D_473),B_476)
      | ~ v1_funct_1(k1_tmap_1(A_475,B_476,C_474,D_473,E_478,F_477))
      | k2_partfun1(D_473,B_476,F_477,k9_subset_1(A_475,C_474,D_473)) != k2_partfun1(C_474,B_476,E_478,k9_subset_1(A_475,C_474,D_473))
      | ~ m1_subset_1(F_477,k1_zfmisc_1(k2_zfmisc_1(D_473,B_476)))
      | ~ v1_funct_2(F_477,D_473,B_476)
      | ~ v1_funct_1(F_477)
      | ~ m1_subset_1(E_478,k1_zfmisc_1(k2_zfmisc_1(C_474,B_476)))
      | ~ v1_funct_2(E_478,C_474,B_476)
      | ~ v1_funct_1(E_478)
      | ~ m1_subset_1(D_473,k1_zfmisc_1(A_475))
      | v1_xboole_0(D_473)
      | ~ m1_subset_1(C_474,k1_zfmisc_1(A_475))
      | v1_xboole_0(C_474)
      | v1_xboole_0(B_476)
      | v1_xboole_0(A_475) ) ),
    inference(resolution,[status(thm)],[c_26,c_965])).

tff(c_1192,plain,(
    ! [A_481,B_482,C_480,F_483,D_479,E_484] :
      ( k2_partfun1(k4_subset_1(A_481,C_480,D_479),B_482,k1_tmap_1(A_481,B_482,C_480,D_479,E_484,F_483),C_480) = E_484
      | ~ v1_funct_1(k1_tmap_1(A_481,B_482,C_480,D_479,E_484,F_483))
      | k2_partfun1(D_479,B_482,F_483,k9_subset_1(A_481,C_480,D_479)) != k2_partfun1(C_480,B_482,E_484,k9_subset_1(A_481,C_480,D_479))
      | ~ m1_subset_1(F_483,k1_zfmisc_1(k2_zfmisc_1(D_479,B_482)))
      | ~ v1_funct_2(F_483,D_479,B_482)
      | ~ v1_funct_1(F_483)
      | ~ m1_subset_1(E_484,k1_zfmisc_1(k2_zfmisc_1(C_480,B_482)))
      | ~ v1_funct_2(E_484,C_480,B_482)
      | ~ v1_funct_1(E_484)
      | ~ m1_subset_1(D_479,k1_zfmisc_1(A_481))
      | v1_xboole_0(D_479)
      | ~ m1_subset_1(C_480,k1_zfmisc_1(A_481))
      | v1_xboole_0(C_480)
      | v1_xboole_0(B_482)
      | v1_xboole_0(A_481) ) ),
    inference(resolution,[status(thm)],[c_28,c_1188])).

tff(c_1196,plain,(
    ! [A_481,C_480,E_484] :
      ( k2_partfun1(k4_subset_1(A_481,C_480,'#skF_4'),'#skF_2',k1_tmap_1(A_481,'#skF_2',C_480,'#skF_4',E_484,'#skF_6'),C_480) = E_484
      | ~ v1_funct_1(k1_tmap_1(A_481,'#skF_2',C_480,'#skF_4',E_484,'#skF_6'))
      | k2_partfun1(C_480,'#skF_2',E_484,k9_subset_1(A_481,C_480,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_481,C_480,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_484,k1_zfmisc_1(k2_zfmisc_1(C_480,'#skF_2')))
      | ~ v1_funct_2(E_484,C_480,'#skF_2')
      | ~ v1_funct_1(E_484)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_481))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_480,k1_zfmisc_1(A_481))
      | v1_xboole_0(C_480)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_481) ) ),
    inference(resolution,[status(thm)],[c_34,c_1192])).

tff(c_1202,plain,(
    ! [A_481,C_480,E_484] :
      ( k2_partfun1(k4_subset_1(A_481,C_480,'#skF_4'),'#skF_2',k1_tmap_1(A_481,'#skF_2',C_480,'#skF_4',E_484,'#skF_6'),C_480) = E_484
      | ~ v1_funct_1(k1_tmap_1(A_481,'#skF_2',C_480,'#skF_4',E_484,'#skF_6'))
      | k2_partfun1(C_480,'#skF_2',E_484,k9_subset_1(A_481,C_480,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_481,C_480,'#skF_4'))
      | ~ m1_subset_1(E_484,k1_zfmisc_1(k2_zfmisc_1(C_480,'#skF_2')))
      | ~ v1_funct_2(E_484,C_480,'#skF_2')
      | ~ v1_funct_1(E_484)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_481))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_480,k1_zfmisc_1(A_481))
      | v1_xboole_0(C_480)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_481) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_304,c_1196])).

tff(c_1208,plain,(
    ! [A_485,C_486,E_487] :
      ( k2_partfun1(k4_subset_1(A_485,C_486,'#skF_4'),'#skF_2',k1_tmap_1(A_485,'#skF_2',C_486,'#skF_4',E_487,'#skF_6'),C_486) = E_487
      | ~ v1_funct_1(k1_tmap_1(A_485,'#skF_2',C_486,'#skF_4',E_487,'#skF_6'))
      | k2_partfun1(C_486,'#skF_2',E_487,k9_subset_1(A_485,C_486,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_485,C_486,'#skF_4'))
      | ~ m1_subset_1(E_487,k1_zfmisc_1(k2_zfmisc_1(C_486,'#skF_2')))
      | ~ v1_funct_2(E_487,C_486,'#skF_2')
      | ~ v1_funct_1(E_487)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_485))
      | ~ m1_subset_1(C_486,k1_zfmisc_1(A_485))
      | v1_xboole_0(C_486)
      | v1_xboole_0(A_485) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_50,c_1202])).

tff(c_1215,plain,(
    ! [A_485] :
      ( k2_partfun1(k4_subset_1(A_485,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_485,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_485,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_485,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_485,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_485))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_485))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_485) ) ),
    inference(resolution,[status(thm)],[c_40,c_1208])).

tff(c_1225,plain,(
    ! [A_485] :
      ( k2_partfun1(k4_subset_1(A_485,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_485,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_485,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_485,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_485,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_485))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_485))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_485) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_307,c_1215])).

tff(c_1264,plain,(
    ! [A_496] :
      ( k2_partfun1(k4_subset_1(A_496,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_496,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_496,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_496,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_496,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_496))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_496))
      | v1_xboole_0(A_496) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1225])).

tff(c_362,plain,(
    ! [A_263,E_266,F_265,D_261,B_264,C_262] :
      ( v1_funct_1(k1_tmap_1(A_263,B_264,C_262,D_261,E_266,F_265))
      | ~ m1_subset_1(F_265,k1_zfmisc_1(k2_zfmisc_1(D_261,B_264)))
      | ~ v1_funct_2(F_265,D_261,B_264)
      | ~ v1_funct_1(F_265)
      | ~ m1_subset_1(E_266,k1_zfmisc_1(k2_zfmisc_1(C_262,B_264)))
      | ~ v1_funct_2(E_266,C_262,B_264)
      | ~ v1_funct_1(E_266)
      | ~ m1_subset_1(D_261,k1_zfmisc_1(A_263))
      | v1_xboole_0(D_261)
      | ~ m1_subset_1(C_262,k1_zfmisc_1(A_263))
      | v1_xboole_0(C_262)
      | v1_xboole_0(B_264)
      | v1_xboole_0(A_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_364,plain,(
    ! [A_263,C_262,E_266] :
      ( v1_funct_1(k1_tmap_1(A_263,'#skF_2',C_262,'#skF_4',E_266,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_266,k1_zfmisc_1(k2_zfmisc_1(C_262,'#skF_2')))
      | ~ v1_funct_2(E_266,C_262,'#skF_2')
      | ~ v1_funct_1(E_266)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_263))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_262,k1_zfmisc_1(A_263))
      | v1_xboole_0(C_262)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_263) ) ),
    inference(resolution,[status(thm)],[c_34,c_362])).

tff(c_369,plain,(
    ! [A_263,C_262,E_266] :
      ( v1_funct_1(k1_tmap_1(A_263,'#skF_2',C_262,'#skF_4',E_266,'#skF_6'))
      | ~ m1_subset_1(E_266,k1_zfmisc_1(k2_zfmisc_1(C_262,'#skF_2')))
      | ~ v1_funct_2(E_266,C_262,'#skF_2')
      | ~ v1_funct_1(E_266)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_263))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_262,k1_zfmisc_1(A_263))
      | v1_xboole_0(C_262)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_263) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_364])).

tff(c_375,plain,(
    ! [A_267,C_268,E_269] :
      ( v1_funct_1(k1_tmap_1(A_267,'#skF_2',C_268,'#skF_4',E_269,'#skF_6'))
      | ~ m1_subset_1(E_269,k1_zfmisc_1(k2_zfmisc_1(C_268,'#skF_2')))
      | ~ v1_funct_2(E_269,C_268,'#skF_2')
      | ~ v1_funct_1(E_269)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_267))
      | ~ m1_subset_1(C_268,k1_zfmisc_1(A_267))
      | v1_xboole_0(C_268)
      | v1_xboole_0(A_267) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_50,c_369])).

tff(c_379,plain,(
    ! [A_267] :
      ( v1_funct_1(k1_tmap_1(A_267,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_267))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_267))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_267) ) ),
    inference(resolution,[status(thm)],[c_40,c_375])).

tff(c_386,plain,(
    ! [A_267] :
      ( v1_funct_1(k1_tmap_1(A_267,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_267))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_267))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_267) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_379])).

tff(c_395,plain,(
    ! [A_271] :
      ( v1_funct_1(k1_tmap_1(A_271,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_271))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_271))
      | v1_xboole_0(A_271) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_386])).

tff(c_398,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_395])).

tff(c_401,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_398])).

tff(c_402,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_401])).

tff(c_577,plain,(
    ! [D_321,C_320,E_319,A_318,B_322,F_317] :
      ( k2_partfun1(k4_subset_1(A_318,C_320,D_321),B_322,k1_tmap_1(A_318,B_322,C_320,D_321,E_319,F_317),D_321) = F_317
      | ~ m1_subset_1(k1_tmap_1(A_318,B_322,C_320,D_321,E_319,F_317),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_318,C_320,D_321),B_322)))
      | ~ v1_funct_2(k1_tmap_1(A_318,B_322,C_320,D_321,E_319,F_317),k4_subset_1(A_318,C_320,D_321),B_322)
      | ~ v1_funct_1(k1_tmap_1(A_318,B_322,C_320,D_321,E_319,F_317))
      | k2_partfun1(D_321,B_322,F_317,k9_subset_1(A_318,C_320,D_321)) != k2_partfun1(C_320,B_322,E_319,k9_subset_1(A_318,C_320,D_321))
      | ~ m1_subset_1(F_317,k1_zfmisc_1(k2_zfmisc_1(D_321,B_322)))
      | ~ v1_funct_2(F_317,D_321,B_322)
      | ~ v1_funct_1(F_317)
      | ~ m1_subset_1(E_319,k1_zfmisc_1(k2_zfmisc_1(C_320,B_322)))
      | ~ v1_funct_2(E_319,C_320,B_322)
      | ~ v1_funct_1(E_319)
      | ~ m1_subset_1(D_321,k1_zfmisc_1(A_318))
      | v1_xboole_0(D_321)
      | ~ m1_subset_1(C_320,k1_zfmisc_1(A_318))
      | v1_xboole_0(C_320)
      | v1_xboole_0(B_322)
      | v1_xboole_0(A_318) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_711,plain,(
    ! [B_361,F_362,C_359,A_360,E_363,D_358] :
      ( k2_partfun1(k4_subset_1(A_360,C_359,D_358),B_361,k1_tmap_1(A_360,B_361,C_359,D_358,E_363,F_362),D_358) = F_362
      | ~ v1_funct_2(k1_tmap_1(A_360,B_361,C_359,D_358,E_363,F_362),k4_subset_1(A_360,C_359,D_358),B_361)
      | ~ v1_funct_1(k1_tmap_1(A_360,B_361,C_359,D_358,E_363,F_362))
      | k2_partfun1(D_358,B_361,F_362,k9_subset_1(A_360,C_359,D_358)) != k2_partfun1(C_359,B_361,E_363,k9_subset_1(A_360,C_359,D_358))
      | ~ m1_subset_1(F_362,k1_zfmisc_1(k2_zfmisc_1(D_358,B_361)))
      | ~ v1_funct_2(F_362,D_358,B_361)
      | ~ v1_funct_1(F_362)
      | ~ m1_subset_1(E_363,k1_zfmisc_1(k2_zfmisc_1(C_359,B_361)))
      | ~ v1_funct_2(E_363,C_359,B_361)
      | ~ v1_funct_1(E_363)
      | ~ m1_subset_1(D_358,k1_zfmisc_1(A_360))
      | v1_xboole_0(D_358)
      | ~ m1_subset_1(C_359,k1_zfmisc_1(A_360))
      | v1_xboole_0(C_359)
      | v1_xboole_0(B_361)
      | v1_xboole_0(A_360) ) ),
    inference(resolution,[status(thm)],[c_26,c_577])).

tff(c_715,plain,(
    ! [C_365,B_367,F_368,A_366,D_364,E_369] :
      ( k2_partfun1(k4_subset_1(A_366,C_365,D_364),B_367,k1_tmap_1(A_366,B_367,C_365,D_364,E_369,F_368),D_364) = F_368
      | ~ v1_funct_1(k1_tmap_1(A_366,B_367,C_365,D_364,E_369,F_368))
      | k2_partfun1(D_364,B_367,F_368,k9_subset_1(A_366,C_365,D_364)) != k2_partfun1(C_365,B_367,E_369,k9_subset_1(A_366,C_365,D_364))
      | ~ m1_subset_1(F_368,k1_zfmisc_1(k2_zfmisc_1(D_364,B_367)))
      | ~ v1_funct_2(F_368,D_364,B_367)
      | ~ v1_funct_1(F_368)
      | ~ m1_subset_1(E_369,k1_zfmisc_1(k2_zfmisc_1(C_365,B_367)))
      | ~ v1_funct_2(E_369,C_365,B_367)
      | ~ v1_funct_1(E_369)
      | ~ m1_subset_1(D_364,k1_zfmisc_1(A_366))
      | v1_xboole_0(D_364)
      | ~ m1_subset_1(C_365,k1_zfmisc_1(A_366))
      | v1_xboole_0(C_365)
      | v1_xboole_0(B_367)
      | v1_xboole_0(A_366) ) ),
    inference(resolution,[status(thm)],[c_28,c_711])).

tff(c_719,plain,(
    ! [A_366,C_365,E_369] :
      ( k2_partfun1(k4_subset_1(A_366,C_365,'#skF_4'),'#skF_2',k1_tmap_1(A_366,'#skF_2',C_365,'#skF_4',E_369,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_366,'#skF_2',C_365,'#skF_4',E_369,'#skF_6'))
      | k2_partfun1(C_365,'#skF_2',E_369,k9_subset_1(A_366,C_365,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_366,C_365,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_369,k1_zfmisc_1(k2_zfmisc_1(C_365,'#skF_2')))
      | ~ v1_funct_2(E_369,C_365,'#skF_2')
      | ~ v1_funct_1(E_369)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_366))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_365,k1_zfmisc_1(A_366))
      | v1_xboole_0(C_365)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_366) ) ),
    inference(resolution,[status(thm)],[c_34,c_715])).

tff(c_725,plain,(
    ! [A_366,C_365,E_369] :
      ( k2_partfun1(k4_subset_1(A_366,C_365,'#skF_4'),'#skF_2',k1_tmap_1(A_366,'#skF_2',C_365,'#skF_4',E_369,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_366,'#skF_2',C_365,'#skF_4',E_369,'#skF_6'))
      | k2_partfun1(C_365,'#skF_2',E_369,k9_subset_1(A_366,C_365,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_366,C_365,'#skF_4'))
      | ~ m1_subset_1(E_369,k1_zfmisc_1(k2_zfmisc_1(C_365,'#skF_2')))
      | ~ v1_funct_2(E_369,C_365,'#skF_2')
      | ~ v1_funct_1(E_369)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_366))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_365,k1_zfmisc_1(A_366))
      | v1_xboole_0(C_365)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_366) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_304,c_719])).

tff(c_731,plain,(
    ! [A_370,C_371,E_372] :
      ( k2_partfun1(k4_subset_1(A_370,C_371,'#skF_4'),'#skF_2',k1_tmap_1(A_370,'#skF_2',C_371,'#skF_4',E_372,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_370,'#skF_2',C_371,'#skF_4',E_372,'#skF_6'))
      | k2_partfun1(C_371,'#skF_2',E_372,k9_subset_1(A_370,C_371,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_370,C_371,'#skF_4'))
      | ~ m1_subset_1(E_372,k1_zfmisc_1(k2_zfmisc_1(C_371,'#skF_2')))
      | ~ v1_funct_2(E_372,C_371,'#skF_2')
      | ~ v1_funct_1(E_372)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_370))
      | ~ m1_subset_1(C_371,k1_zfmisc_1(A_370))
      | v1_xboole_0(C_371)
      | v1_xboole_0(A_370) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_50,c_725])).

tff(c_738,plain,(
    ! [A_370] :
      ( k2_partfun1(k4_subset_1(A_370,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_370,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_370,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_370,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_370,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_370))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_370))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_370) ) ),
    inference(resolution,[status(thm)],[c_40,c_731])).

tff(c_748,plain,(
    ! [A_370] :
      ( k2_partfun1(k4_subset_1(A_370,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_370,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_370,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_370,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_370,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_370))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_370))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_370) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_307,c_738])).

tff(c_783,plain,(
    ! [A_375] :
      ( k2_partfun1(k4_subset_1(A_375,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_375,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_375,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_375,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_375,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_375))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_375))
      | v1_xboole_0(A_375) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_748])).

tff(c_103,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_93,c_12])).

tff(c_122,plain,(
    ! [A_221,B_222] :
      ( r1_xboole_0(A_221,B_222)
      | ~ r1_subset_1(A_221,B_222)
      | v1_xboole_0(B_222)
      | v1_xboole_0(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_210,plain,(
    ! [A_236,B_237] :
      ( k3_xboole_0(A_236,B_237) = k1_xboole_0
      | ~ r1_subset_1(A_236,B_237)
      | v1_xboole_0(B_237)
      | v1_xboole_0(A_236) ) ),
    inference(resolution,[status(thm)],[c_122,c_2])).

tff(c_213,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_210])).

tff(c_216,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_50,c_213])).

tff(c_107,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_96,c_12])).

tff(c_181,plain,(
    ! [A_230,B_231,C_232,D_233] :
      ( k2_partfun1(A_230,B_231,C_232,D_233) = k7_relat_1(C_232,D_233)
      | ~ m1_subset_1(C_232,k1_zfmisc_1(k2_zfmisc_1(A_230,B_231)))
      | ~ v1_funct_1(C_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_185,plain,(
    ! [D_233] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_233) = k7_relat_1('#skF_5',D_233)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_181])).

tff(c_191,plain,(
    ! [D_233] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_233) = k7_relat_1('#skF_5',D_233) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_185])).

tff(c_183,plain,(
    ! [D_233] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_233) = k7_relat_1('#skF_6',D_233)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_34,c_181])).

tff(c_188,plain,(
    ! [D_233] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_233) = k7_relat_1('#skF_6',D_233) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_183])).

tff(c_131,plain,(
    ! [A_223,B_224,C_225] :
      ( k9_subset_1(A_223,B_224,C_225) = k3_xboole_0(B_224,C_225)
      | ~ m1_subset_1(C_225,k1_zfmisc_1(A_223)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_142,plain,(
    ! [B_224] : k9_subset_1('#skF_1',B_224,'#skF_4') = k3_xboole_0(B_224,'#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_131])).

tff(c_32,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_99,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_144,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_142,c_99])).

tff(c_227,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_216,c_107,c_216,c_191,c_188,c_144])).

tff(c_228,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_361,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_228])).

tff(c_794,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_783,c_361])).

tff(c_808,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_233,c_355,c_237,c_355,c_276,c_276,c_402,c_794])).

tff(c_810,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_808])).

tff(c_811,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_1273,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1264,c_811])).

tff(c_1284,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_237,c_233,c_355,c_276,c_355,c_276,c_857,c_1273])).

tff(c_1286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1284])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:00:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.62/1.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.62/1.86  
% 4.62/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.62/1.86  %$ v1_funct_2 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.62/1.86  
% 4.62/1.86  %Foreground sorts:
% 4.62/1.86  
% 4.62/1.86  
% 4.62/1.86  %Background operators:
% 4.62/1.86  
% 4.62/1.86  
% 4.62/1.86  %Foreground operators:
% 4.62/1.86  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 4.62/1.86  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.62/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.62/1.86  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.62/1.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.62/1.86  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.62/1.86  tff('#skF_5', type, '#skF_5': $i).
% 4.62/1.86  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.62/1.86  tff('#skF_6', type, '#skF_6': $i).
% 4.62/1.86  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.62/1.86  tff('#skF_2', type, '#skF_2': $i).
% 4.62/1.86  tff('#skF_3', type, '#skF_3': $i).
% 4.62/1.86  tff('#skF_1', type, '#skF_1': $i).
% 4.62/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.62/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.62/1.86  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.62/1.86  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.62/1.86  tff('#skF_4', type, '#skF_4': $i).
% 4.62/1.86  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.62/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.62/1.86  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 4.62/1.86  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.62/1.86  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.62/1.86  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.62/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.62/1.86  
% 4.62/1.89  tff(f_186, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 4.62/1.89  tff(f_42, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.62/1.89  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.62/1.89  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_relat_1)).
% 4.62/1.89  tff(f_56, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 4.62/1.89  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.62/1.89  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.62/1.89  tff(f_144, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 4.62/1.89  tff(f_62, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 4.62/1.89  tff(f_110, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 4.62/1.89  tff(c_58, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.62/1.89  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.62/1.89  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.62/1.89  tff(c_10, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.62/1.89  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.62/1.89  tff(c_78, plain, (![B_217, A_218]: (v1_relat_1(B_217) | ~m1_subset_1(B_217, k1_zfmisc_1(A_218)) | ~v1_relat_1(A_218))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.62/1.89  tff(c_84, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_78])).
% 4.62/1.89  tff(c_96, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_84])).
% 4.62/1.89  tff(c_12, plain, (![A_11]: (k7_relat_1(A_11, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.62/1.89  tff(c_237, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_96, c_12])).
% 4.62/1.89  tff(c_34, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.62/1.89  tff(c_81, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_78])).
% 4.62/1.89  tff(c_93, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_81])).
% 4.62/1.89  tff(c_233, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_93, c_12])).
% 4.62/1.89  tff(c_54, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.62/1.89  tff(c_50, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.62/1.89  tff(c_46, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.62/1.89  tff(c_256, plain, (![A_242, B_243]: (r1_xboole_0(A_242, B_243) | ~r1_subset_1(A_242, B_243) | v1_xboole_0(B_243) | v1_xboole_0(A_242))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.62/1.89  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.62/1.89  tff(c_345, plain, (![A_259, B_260]: (k3_xboole_0(A_259, B_260)=k1_xboole_0 | ~r1_subset_1(A_259, B_260) | v1_xboole_0(B_260) | v1_xboole_0(A_259))), inference(resolution, [status(thm)], [c_256, c_2])).
% 4.62/1.89  tff(c_351, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_46, c_345])).
% 4.62/1.89  tff(c_355, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_54, c_50, c_351])).
% 4.62/1.89  tff(c_265, plain, (![A_244, B_245, C_246]: (k9_subset_1(A_244, B_245, C_246)=k3_xboole_0(B_245, C_246) | ~m1_subset_1(C_246, k1_zfmisc_1(A_244)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.62/1.89  tff(c_276, plain, (![B_245]: (k9_subset_1('#skF_1', B_245, '#skF_4')=k3_xboole_0(B_245, '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_265])).
% 4.62/1.89  tff(c_44, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.62/1.89  tff(c_42, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.62/1.89  tff(c_56, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.62/1.89  tff(c_38, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.62/1.89  tff(c_36, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.62/1.89  tff(c_817, plain, (![D_376, E_381, B_379, F_380, A_378, C_377]: (v1_funct_1(k1_tmap_1(A_378, B_379, C_377, D_376, E_381, F_380)) | ~m1_subset_1(F_380, k1_zfmisc_1(k2_zfmisc_1(D_376, B_379))) | ~v1_funct_2(F_380, D_376, B_379) | ~v1_funct_1(F_380) | ~m1_subset_1(E_381, k1_zfmisc_1(k2_zfmisc_1(C_377, B_379))) | ~v1_funct_2(E_381, C_377, B_379) | ~v1_funct_1(E_381) | ~m1_subset_1(D_376, k1_zfmisc_1(A_378)) | v1_xboole_0(D_376) | ~m1_subset_1(C_377, k1_zfmisc_1(A_378)) | v1_xboole_0(C_377) | v1_xboole_0(B_379) | v1_xboole_0(A_378))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.62/1.89  tff(c_819, plain, (![A_378, C_377, E_381]: (v1_funct_1(k1_tmap_1(A_378, '#skF_2', C_377, '#skF_4', E_381, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_381, k1_zfmisc_1(k2_zfmisc_1(C_377, '#skF_2'))) | ~v1_funct_2(E_381, C_377, '#skF_2') | ~v1_funct_1(E_381) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_378)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_377, k1_zfmisc_1(A_378)) | v1_xboole_0(C_377) | v1_xboole_0('#skF_2') | v1_xboole_0(A_378))), inference(resolution, [status(thm)], [c_34, c_817])).
% 4.62/1.89  tff(c_824, plain, (![A_378, C_377, E_381]: (v1_funct_1(k1_tmap_1(A_378, '#skF_2', C_377, '#skF_4', E_381, '#skF_6')) | ~m1_subset_1(E_381, k1_zfmisc_1(k2_zfmisc_1(C_377, '#skF_2'))) | ~v1_funct_2(E_381, C_377, '#skF_2') | ~v1_funct_1(E_381) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_378)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_377, k1_zfmisc_1(A_378)) | v1_xboole_0(C_377) | v1_xboole_0('#skF_2') | v1_xboole_0(A_378))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_819])).
% 4.62/1.89  tff(c_830, plain, (![A_382, C_383, E_384]: (v1_funct_1(k1_tmap_1(A_382, '#skF_2', C_383, '#skF_4', E_384, '#skF_6')) | ~m1_subset_1(E_384, k1_zfmisc_1(k2_zfmisc_1(C_383, '#skF_2'))) | ~v1_funct_2(E_384, C_383, '#skF_2') | ~v1_funct_1(E_384) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_382)) | ~m1_subset_1(C_383, k1_zfmisc_1(A_382)) | v1_xboole_0(C_383) | v1_xboole_0(A_382))), inference(negUnitSimplification, [status(thm)], [c_56, c_50, c_824])).
% 4.62/1.89  tff(c_834, plain, (![A_382]: (v1_funct_1(k1_tmap_1(A_382, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_382)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_382)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_382))), inference(resolution, [status(thm)], [c_40, c_830])).
% 4.62/1.89  tff(c_841, plain, (![A_382]: (v1_funct_1(k1_tmap_1(A_382, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_382)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_382)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_382))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_834])).
% 4.62/1.89  tff(c_850, plain, (![A_386]: (v1_funct_1(k1_tmap_1(A_386, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_386)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_386)) | v1_xboole_0(A_386))), inference(negUnitSimplification, [status(thm)], [c_54, c_841])).
% 4.62/1.89  tff(c_853, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_52, c_850])).
% 4.62/1.89  tff(c_856, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_853])).
% 4.62/1.89  tff(c_857, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_58, c_856])).
% 4.62/1.89  tff(c_297, plain, (![A_249, B_250, C_251, D_252]: (k2_partfun1(A_249, B_250, C_251, D_252)=k7_relat_1(C_251, D_252) | ~m1_subset_1(C_251, k1_zfmisc_1(k2_zfmisc_1(A_249, B_250))) | ~v1_funct_1(C_251))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.62/1.89  tff(c_301, plain, (![D_252]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_252)=k7_relat_1('#skF_5', D_252) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_297])).
% 4.62/1.89  tff(c_307, plain, (![D_252]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_252)=k7_relat_1('#skF_5', D_252))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_301])).
% 4.62/1.89  tff(c_299, plain, (![D_252]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_252)=k7_relat_1('#skF_6', D_252) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_34, c_297])).
% 4.62/1.89  tff(c_304, plain, (![D_252]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_252)=k7_relat_1('#skF_6', D_252))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_299])).
% 4.62/1.89  tff(c_28, plain, (![E_149, C_147, A_145, D_148, F_150, B_146]: (v1_funct_2(k1_tmap_1(A_145, B_146, C_147, D_148, E_149, F_150), k4_subset_1(A_145, C_147, D_148), B_146) | ~m1_subset_1(F_150, k1_zfmisc_1(k2_zfmisc_1(D_148, B_146))) | ~v1_funct_2(F_150, D_148, B_146) | ~v1_funct_1(F_150) | ~m1_subset_1(E_149, k1_zfmisc_1(k2_zfmisc_1(C_147, B_146))) | ~v1_funct_2(E_149, C_147, B_146) | ~v1_funct_1(E_149) | ~m1_subset_1(D_148, k1_zfmisc_1(A_145)) | v1_xboole_0(D_148) | ~m1_subset_1(C_147, k1_zfmisc_1(A_145)) | v1_xboole_0(C_147) | v1_xboole_0(B_146) | v1_xboole_0(A_145))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.62/1.89  tff(c_26, plain, (![E_149, C_147, A_145, D_148, F_150, B_146]: (m1_subset_1(k1_tmap_1(A_145, B_146, C_147, D_148, E_149, F_150), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_145, C_147, D_148), B_146))) | ~m1_subset_1(F_150, k1_zfmisc_1(k2_zfmisc_1(D_148, B_146))) | ~v1_funct_2(F_150, D_148, B_146) | ~v1_funct_1(F_150) | ~m1_subset_1(E_149, k1_zfmisc_1(k2_zfmisc_1(C_147, B_146))) | ~v1_funct_2(E_149, C_147, B_146) | ~v1_funct_1(E_149) | ~m1_subset_1(D_148, k1_zfmisc_1(A_145)) | v1_xboole_0(D_148) | ~m1_subset_1(C_147, k1_zfmisc_1(A_145)) | v1_xboole_0(C_147) | v1_xboole_0(B_146) | v1_xboole_0(A_145))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.62/1.89  tff(c_965, plain, (![B_419, A_415, C_417, D_418, F_414, E_416]: (k2_partfun1(k4_subset_1(A_415, C_417, D_418), B_419, k1_tmap_1(A_415, B_419, C_417, D_418, E_416, F_414), C_417)=E_416 | ~m1_subset_1(k1_tmap_1(A_415, B_419, C_417, D_418, E_416, F_414), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_415, C_417, D_418), B_419))) | ~v1_funct_2(k1_tmap_1(A_415, B_419, C_417, D_418, E_416, F_414), k4_subset_1(A_415, C_417, D_418), B_419) | ~v1_funct_1(k1_tmap_1(A_415, B_419, C_417, D_418, E_416, F_414)) | k2_partfun1(D_418, B_419, F_414, k9_subset_1(A_415, C_417, D_418))!=k2_partfun1(C_417, B_419, E_416, k9_subset_1(A_415, C_417, D_418)) | ~m1_subset_1(F_414, k1_zfmisc_1(k2_zfmisc_1(D_418, B_419))) | ~v1_funct_2(F_414, D_418, B_419) | ~v1_funct_1(F_414) | ~m1_subset_1(E_416, k1_zfmisc_1(k2_zfmisc_1(C_417, B_419))) | ~v1_funct_2(E_416, C_417, B_419) | ~v1_funct_1(E_416) | ~m1_subset_1(D_418, k1_zfmisc_1(A_415)) | v1_xboole_0(D_418) | ~m1_subset_1(C_417, k1_zfmisc_1(A_415)) | v1_xboole_0(C_417) | v1_xboole_0(B_419) | v1_xboole_0(A_415))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.62/1.89  tff(c_1188, plain, (![A_475, F_477, C_474, E_478, D_473, B_476]: (k2_partfun1(k4_subset_1(A_475, C_474, D_473), B_476, k1_tmap_1(A_475, B_476, C_474, D_473, E_478, F_477), C_474)=E_478 | ~v1_funct_2(k1_tmap_1(A_475, B_476, C_474, D_473, E_478, F_477), k4_subset_1(A_475, C_474, D_473), B_476) | ~v1_funct_1(k1_tmap_1(A_475, B_476, C_474, D_473, E_478, F_477)) | k2_partfun1(D_473, B_476, F_477, k9_subset_1(A_475, C_474, D_473))!=k2_partfun1(C_474, B_476, E_478, k9_subset_1(A_475, C_474, D_473)) | ~m1_subset_1(F_477, k1_zfmisc_1(k2_zfmisc_1(D_473, B_476))) | ~v1_funct_2(F_477, D_473, B_476) | ~v1_funct_1(F_477) | ~m1_subset_1(E_478, k1_zfmisc_1(k2_zfmisc_1(C_474, B_476))) | ~v1_funct_2(E_478, C_474, B_476) | ~v1_funct_1(E_478) | ~m1_subset_1(D_473, k1_zfmisc_1(A_475)) | v1_xboole_0(D_473) | ~m1_subset_1(C_474, k1_zfmisc_1(A_475)) | v1_xboole_0(C_474) | v1_xboole_0(B_476) | v1_xboole_0(A_475))), inference(resolution, [status(thm)], [c_26, c_965])).
% 4.62/1.89  tff(c_1192, plain, (![A_481, B_482, C_480, F_483, D_479, E_484]: (k2_partfun1(k4_subset_1(A_481, C_480, D_479), B_482, k1_tmap_1(A_481, B_482, C_480, D_479, E_484, F_483), C_480)=E_484 | ~v1_funct_1(k1_tmap_1(A_481, B_482, C_480, D_479, E_484, F_483)) | k2_partfun1(D_479, B_482, F_483, k9_subset_1(A_481, C_480, D_479))!=k2_partfun1(C_480, B_482, E_484, k9_subset_1(A_481, C_480, D_479)) | ~m1_subset_1(F_483, k1_zfmisc_1(k2_zfmisc_1(D_479, B_482))) | ~v1_funct_2(F_483, D_479, B_482) | ~v1_funct_1(F_483) | ~m1_subset_1(E_484, k1_zfmisc_1(k2_zfmisc_1(C_480, B_482))) | ~v1_funct_2(E_484, C_480, B_482) | ~v1_funct_1(E_484) | ~m1_subset_1(D_479, k1_zfmisc_1(A_481)) | v1_xboole_0(D_479) | ~m1_subset_1(C_480, k1_zfmisc_1(A_481)) | v1_xboole_0(C_480) | v1_xboole_0(B_482) | v1_xboole_0(A_481))), inference(resolution, [status(thm)], [c_28, c_1188])).
% 4.62/1.89  tff(c_1196, plain, (![A_481, C_480, E_484]: (k2_partfun1(k4_subset_1(A_481, C_480, '#skF_4'), '#skF_2', k1_tmap_1(A_481, '#skF_2', C_480, '#skF_4', E_484, '#skF_6'), C_480)=E_484 | ~v1_funct_1(k1_tmap_1(A_481, '#skF_2', C_480, '#skF_4', E_484, '#skF_6')) | k2_partfun1(C_480, '#skF_2', E_484, k9_subset_1(A_481, C_480, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_481, C_480, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_484, k1_zfmisc_1(k2_zfmisc_1(C_480, '#skF_2'))) | ~v1_funct_2(E_484, C_480, '#skF_2') | ~v1_funct_1(E_484) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_481)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_480, k1_zfmisc_1(A_481)) | v1_xboole_0(C_480) | v1_xboole_0('#skF_2') | v1_xboole_0(A_481))), inference(resolution, [status(thm)], [c_34, c_1192])).
% 4.62/1.89  tff(c_1202, plain, (![A_481, C_480, E_484]: (k2_partfun1(k4_subset_1(A_481, C_480, '#skF_4'), '#skF_2', k1_tmap_1(A_481, '#skF_2', C_480, '#skF_4', E_484, '#skF_6'), C_480)=E_484 | ~v1_funct_1(k1_tmap_1(A_481, '#skF_2', C_480, '#skF_4', E_484, '#skF_6')) | k2_partfun1(C_480, '#skF_2', E_484, k9_subset_1(A_481, C_480, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_481, C_480, '#skF_4')) | ~m1_subset_1(E_484, k1_zfmisc_1(k2_zfmisc_1(C_480, '#skF_2'))) | ~v1_funct_2(E_484, C_480, '#skF_2') | ~v1_funct_1(E_484) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_481)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_480, k1_zfmisc_1(A_481)) | v1_xboole_0(C_480) | v1_xboole_0('#skF_2') | v1_xboole_0(A_481))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_304, c_1196])).
% 4.62/1.89  tff(c_1208, plain, (![A_485, C_486, E_487]: (k2_partfun1(k4_subset_1(A_485, C_486, '#skF_4'), '#skF_2', k1_tmap_1(A_485, '#skF_2', C_486, '#skF_4', E_487, '#skF_6'), C_486)=E_487 | ~v1_funct_1(k1_tmap_1(A_485, '#skF_2', C_486, '#skF_4', E_487, '#skF_6')) | k2_partfun1(C_486, '#skF_2', E_487, k9_subset_1(A_485, C_486, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_485, C_486, '#skF_4')) | ~m1_subset_1(E_487, k1_zfmisc_1(k2_zfmisc_1(C_486, '#skF_2'))) | ~v1_funct_2(E_487, C_486, '#skF_2') | ~v1_funct_1(E_487) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_485)) | ~m1_subset_1(C_486, k1_zfmisc_1(A_485)) | v1_xboole_0(C_486) | v1_xboole_0(A_485))), inference(negUnitSimplification, [status(thm)], [c_56, c_50, c_1202])).
% 4.62/1.89  tff(c_1215, plain, (![A_485]: (k2_partfun1(k4_subset_1(A_485, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_485, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_485, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_485, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_485, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_485)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_485)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_485))), inference(resolution, [status(thm)], [c_40, c_1208])).
% 4.62/1.89  tff(c_1225, plain, (![A_485]: (k2_partfun1(k4_subset_1(A_485, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_485, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_485, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_485, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_485, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_485)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_485)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_485))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_307, c_1215])).
% 4.62/1.89  tff(c_1264, plain, (![A_496]: (k2_partfun1(k4_subset_1(A_496, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_496, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_496, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_496, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_496, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_496)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_496)) | v1_xboole_0(A_496))), inference(negUnitSimplification, [status(thm)], [c_54, c_1225])).
% 4.62/1.89  tff(c_362, plain, (![A_263, E_266, F_265, D_261, B_264, C_262]: (v1_funct_1(k1_tmap_1(A_263, B_264, C_262, D_261, E_266, F_265)) | ~m1_subset_1(F_265, k1_zfmisc_1(k2_zfmisc_1(D_261, B_264))) | ~v1_funct_2(F_265, D_261, B_264) | ~v1_funct_1(F_265) | ~m1_subset_1(E_266, k1_zfmisc_1(k2_zfmisc_1(C_262, B_264))) | ~v1_funct_2(E_266, C_262, B_264) | ~v1_funct_1(E_266) | ~m1_subset_1(D_261, k1_zfmisc_1(A_263)) | v1_xboole_0(D_261) | ~m1_subset_1(C_262, k1_zfmisc_1(A_263)) | v1_xboole_0(C_262) | v1_xboole_0(B_264) | v1_xboole_0(A_263))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.62/1.89  tff(c_364, plain, (![A_263, C_262, E_266]: (v1_funct_1(k1_tmap_1(A_263, '#skF_2', C_262, '#skF_4', E_266, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_266, k1_zfmisc_1(k2_zfmisc_1(C_262, '#skF_2'))) | ~v1_funct_2(E_266, C_262, '#skF_2') | ~v1_funct_1(E_266) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_263)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_262, k1_zfmisc_1(A_263)) | v1_xboole_0(C_262) | v1_xboole_0('#skF_2') | v1_xboole_0(A_263))), inference(resolution, [status(thm)], [c_34, c_362])).
% 4.62/1.89  tff(c_369, plain, (![A_263, C_262, E_266]: (v1_funct_1(k1_tmap_1(A_263, '#skF_2', C_262, '#skF_4', E_266, '#skF_6')) | ~m1_subset_1(E_266, k1_zfmisc_1(k2_zfmisc_1(C_262, '#skF_2'))) | ~v1_funct_2(E_266, C_262, '#skF_2') | ~v1_funct_1(E_266) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_263)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_262, k1_zfmisc_1(A_263)) | v1_xboole_0(C_262) | v1_xboole_0('#skF_2') | v1_xboole_0(A_263))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_364])).
% 4.62/1.89  tff(c_375, plain, (![A_267, C_268, E_269]: (v1_funct_1(k1_tmap_1(A_267, '#skF_2', C_268, '#skF_4', E_269, '#skF_6')) | ~m1_subset_1(E_269, k1_zfmisc_1(k2_zfmisc_1(C_268, '#skF_2'))) | ~v1_funct_2(E_269, C_268, '#skF_2') | ~v1_funct_1(E_269) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_267)) | ~m1_subset_1(C_268, k1_zfmisc_1(A_267)) | v1_xboole_0(C_268) | v1_xboole_0(A_267))), inference(negUnitSimplification, [status(thm)], [c_56, c_50, c_369])).
% 4.62/1.89  tff(c_379, plain, (![A_267]: (v1_funct_1(k1_tmap_1(A_267, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_267)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_267)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_267))), inference(resolution, [status(thm)], [c_40, c_375])).
% 4.62/1.89  tff(c_386, plain, (![A_267]: (v1_funct_1(k1_tmap_1(A_267, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_267)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_267)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_267))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_379])).
% 4.62/1.89  tff(c_395, plain, (![A_271]: (v1_funct_1(k1_tmap_1(A_271, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_271)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_271)) | v1_xboole_0(A_271))), inference(negUnitSimplification, [status(thm)], [c_54, c_386])).
% 4.62/1.89  tff(c_398, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_52, c_395])).
% 4.62/1.89  tff(c_401, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_398])).
% 4.62/1.89  tff(c_402, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_58, c_401])).
% 4.62/1.89  tff(c_577, plain, (![D_321, C_320, E_319, A_318, B_322, F_317]: (k2_partfun1(k4_subset_1(A_318, C_320, D_321), B_322, k1_tmap_1(A_318, B_322, C_320, D_321, E_319, F_317), D_321)=F_317 | ~m1_subset_1(k1_tmap_1(A_318, B_322, C_320, D_321, E_319, F_317), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_318, C_320, D_321), B_322))) | ~v1_funct_2(k1_tmap_1(A_318, B_322, C_320, D_321, E_319, F_317), k4_subset_1(A_318, C_320, D_321), B_322) | ~v1_funct_1(k1_tmap_1(A_318, B_322, C_320, D_321, E_319, F_317)) | k2_partfun1(D_321, B_322, F_317, k9_subset_1(A_318, C_320, D_321))!=k2_partfun1(C_320, B_322, E_319, k9_subset_1(A_318, C_320, D_321)) | ~m1_subset_1(F_317, k1_zfmisc_1(k2_zfmisc_1(D_321, B_322))) | ~v1_funct_2(F_317, D_321, B_322) | ~v1_funct_1(F_317) | ~m1_subset_1(E_319, k1_zfmisc_1(k2_zfmisc_1(C_320, B_322))) | ~v1_funct_2(E_319, C_320, B_322) | ~v1_funct_1(E_319) | ~m1_subset_1(D_321, k1_zfmisc_1(A_318)) | v1_xboole_0(D_321) | ~m1_subset_1(C_320, k1_zfmisc_1(A_318)) | v1_xboole_0(C_320) | v1_xboole_0(B_322) | v1_xboole_0(A_318))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.62/1.89  tff(c_711, plain, (![B_361, F_362, C_359, A_360, E_363, D_358]: (k2_partfun1(k4_subset_1(A_360, C_359, D_358), B_361, k1_tmap_1(A_360, B_361, C_359, D_358, E_363, F_362), D_358)=F_362 | ~v1_funct_2(k1_tmap_1(A_360, B_361, C_359, D_358, E_363, F_362), k4_subset_1(A_360, C_359, D_358), B_361) | ~v1_funct_1(k1_tmap_1(A_360, B_361, C_359, D_358, E_363, F_362)) | k2_partfun1(D_358, B_361, F_362, k9_subset_1(A_360, C_359, D_358))!=k2_partfun1(C_359, B_361, E_363, k9_subset_1(A_360, C_359, D_358)) | ~m1_subset_1(F_362, k1_zfmisc_1(k2_zfmisc_1(D_358, B_361))) | ~v1_funct_2(F_362, D_358, B_361) | ~v1_funct_1(F_362) | ~m1_subset_1(E_363, k1_zfmisc_1(k2_zfmisc_1(C_359, B_361))) | ~v1_funct_2(E_363, C_359, B_361) | ~v1_funct_1(E_363) | ~m1_subset_1(D_358, k1_zfmisc_1(A_360)) | v1_xboole_0(D_358) | ~m1_subset_1(C_359, k1_zfmisc_1(A_360)) | v1_xboole_0(C_359) | v1_xboole_0(B_361) | v1_xboole_0(A_360))), inference(resolution, [status(thm)], [c_26, c_577])).
% 4.62/1.89  tff(c_715, plain, (![C_365, B_367, F_368, A_366, D_364, E_369]: (k2_partfun1(k4_subset_1(A_366, C_365, D_364), B_367, k1_tmap_1(A_366, B_367, C_365, D_364, E_369, F_368), D_364)=F_368 | ~v1_funct_1(k1_tmap_1(A_366, B_367, C_365, D_364, E_369, F_368)) | k2_partfun1(D_364, B_367, F_368, k9_subset_1(A_366, C_365, D_364))!=k2_partfun1(C_365, B_367, E_369, k9_subset_1(A_366, C_365, D_364)) | ~m1_subset_1(F_368, k1_zfmisc_1(k2_zfmisc_1(D_364, B_367))) | ~v1_funct_2(F_368, D_364, B_367) | ~v1_funct_1(F_368) | ~m1_subset_1(E_369, k1_zfmisc_1(k2_zfmisc_1(C_365, B_367))) | ~v1_funct_2(E_369, C_365, B_367) | ~v1_funct_1(E_369) | ~m1_subset_1(D_364, k1_zfmisc_1(A_366)) | v1_xboole_0(D_364) | ~m1_subset_1(C_365, k1_zfmisc_1(A_366)) | v1_xboole_0(C_365) | v1_xboole_0(B_367) | v1_xboole_0(A_366))), inference(resolution, [status(thm)], [c_28, c_711])).
% 4.62/1.89  tff(c_719, plain, (![A_366, C_365, E_369]: (k2_partfun1(k4_subset_1(A_366, C_365, '#skF_4'), '#skF_2', k1_tmap_1(A_366, '#skF_2', C_365, '#skF_4', E_369, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_366, '#skF_2', C_365, '#skF_4', E_369, '#skF_6')) | k2_partfun1(C_365, '#skF_2', E_369, k9_subset_1(A_366, C_365, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_366, C_365, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_369, k1_zfmisc_1(k2_zfmisc_1(C_365, '#skF_2'))) | ~v1_funct_2(E_369, C_365, '#skF_2') | ~v1_funct_1(E_369) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_366)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_365, k1_zfmisc_1(A_366)) | v1_xboole_0(C_365) | v1_xboole_0('#skF_2') | v1_xboole_0(A_366))), inference(resolution, [status(thm)], [c_34, c_715])).
% 4.62/1.89  tff(c_725, plain, (![A_366, C_365, E_369]: (k2_partfun1(k4_subset_1(A_366, C_365, '#skF_4'), '#skF_2', k1_tmap_1(A_366, '#skF_2', C_365, '#skF_4', E_369, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_366, '#skF_2', C_365, '#skF_4', E_369, '#skF_6')) | k2_partfun1(C_365, '#skF_2', E_369, k9_subset_1(A_366, C_365, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_366, C_365, '#skF_4')) | ~m1_subset_1(E_369, k1_zfmisc_1(k2_zfmisc_1(C_365, '#skF_2'))) | ~v1_funct_2(E_369, C_365, '#skF_2') | ~v1_funct_1(E_369) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_366)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_365, k1_zfmisc_1(A_366)) | v1_xboole_0(C_365) | v1_xboole_0('#skF_2') | v1_xboole_0(A_366))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_304, c_719])).
% 4.62/1.89  tff(c_731, plain, (![A_370, C_371, E_372]: (k2_partfun1(k4_subset_1(A_370, C_371, '#skF_4'), '#skF_2', k1_tmap_1(A_370, '#skF_2', C_371, '#skF_4', E_372, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_370, '#skF_2', C_371, '#skF_4', E_372, '#skF_6')) | k2_partfun1(C_371, '#skF_2', E_372, k9_subset_1(A_370, C_371, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_370, C_371, '#skF_4')) | ~m1_subset_1(E_372, k1_zfmisc_1(k2_zfmisc_1(C_371, '#skF_2'))) | ~v1_funct_2(E_372, C_371, '#skF_2') | ~v1_funct_1(E_372) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_370)) | ~m1_subset_1(C_371, k1_zfmisc_1(A_370)) | v1_xboole_0(C_371) | v1_xboole_0(A_370))), inference(negUnitSimplification, [status(thm)], [c_56, c_50, c_725])).
% 4.62/1.89  tff(c_738, plain, (![A_370]: (k2_partfun1(k4_subset_1(A_370, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_370, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_370, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_370, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_370, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_370)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_370)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_370))), inference(resolution, [status(thm)], [c_40, c_731])).
% 4.62/1.89  tff(c_748, plain, (![A_370]: (k2_partfun1(k4_subset_1(A_370, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_370, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_370, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_370, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_370, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_370)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_370)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_370))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_307, c_738])).
% 4.62/1.89  tff(c_783, plain, (![A_375]: (k2_partfun1(k4_subset_1(A_375, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_375, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_375, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_375, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_375, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_375)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_375)) | v1_xboole_0(A_375))), inference(negUnitSimplification, [status(thm)], [c_54, c_748])).
% 4.62/1.89  tff(c_103, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_93, c_12])).
% 4.62/1.89  tff(c_122, plain, (![A_221, B_222]: (r1_xboole_0(A_221, B_222) | ~r1_subset_1(A_221, B_222) | v1_xboole_0(B_222) | v1_xboole_0(A_221))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.62/1.89  tff(c_210, plain, (![A_236, B_237]: (k3_xboole_0(A_236, B_237)=k1_xboole_0 | ~r1_subset_1(A_236, B_237) | v1_xboole_0(B_237) | v1_xboole_0(A_236))), inference(resolution, [status(thm)], [c_122, c_2])).
% 4.62/1.89  tff(c_213, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_46, c_210])).
% 4.62/1.89  tff(c_216, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_54, c_50, c_213])).
% 4.62/1.89  tff(c_107, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_96, c_12])).
% 4.62/1.89  tff(c_181, plain, (![A_230, B_231, C_232, D_233]: (k2_partfun1(A_230, B_231, C_232, D_233)=k7_relat_1(C_232, D_233) | ~m1_subset_1(C_232, k1_zfmisc_1(k2_zfmisc_1(A_230, B_231))) | ~v1_funct_1(C_232))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.62/1.89  tff(c_185, plain, (![D_233]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_233)=k7_relat_1('#skF_5', D_233) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_181])).
% 4.62/1.89  tff(c_191, plain, (![D_233]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_233)=k7_relat_1('#skF_5', D_233))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_185])).
% 4.62/1.89  tff(c_183, plain, (![D_233]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_233)=k7_relat_1('#skF_6', D_233) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_34, c_181])).
% 4.62/1.89  tff(c_188, plain, (![D_233]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_233)=k7_relat_1('#skF_6', D_233))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_183])).
% 4.62/1.89  tff(c_131, plain, (![A_223, B_224, C_225]: (k9_subset_1(A_223, B_224, C_225)=k3_xboole_0(B_224, C_225) | ~m1_subset_1(C_225, k1_zfmisc_1(A_223)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.62/1.89  tff(c_142, plain, (![B_224]: (k9_subset_1('#skF_1', B_224, '#skF_4')=k3_xboole_0(B_224, '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_131])).
% 4.62/1.89  tff(c_32, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.62/1.89  tff(c_99, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_32])).
% 4.62/1.89  tff(c_144, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_142, c_99])).
% 4.62/1.89  tff(c_227, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_216, c_107, c_216, c_191, c_188, c_144])).
% 4.62/1.89  tff(c_228, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_32])).
% 4.62/1.89  tff(c_361, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_228])).
% 4.62/1.89  tff(c_794, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_783, c_361])).
% 4.62/1.89  tff(c_808, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_233, c_355, c_237, c_355, c_276, c_276, c_402, c_794])).
% 4.62/1.89  tff(c_810, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_808])).
% 4.62/1.89  tff(c_811, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_228])).
% 4.62/1.89  tff(c_1273, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1264, c_811])).
% 4.62/1.89  tff(c_1284, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_237, c_233, c_355, c_276, c_355, c_276, c_857, c_1273])).
% 4.62/1.89  tff(c_1286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1284])).
% 4.62/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.62/1.89  
% 4.62/1.89  Inference rules
% 4.62/1.89  ----------------------
% 4.62/1.89  #Ref     : 0
% 4.62/1.89  #Sup     : 255
% 4.62/1.89  #Fact    : 0
% 4.62/1.89  #Define  : 0
% 4.62/1.89  #Split   : 4
% 4.62/1.89  #Chain   : 0
% 4.62/1.89  #Close   : 0
% 4.62/1.89  
% 4.62/1.89  Ordering : KBO
% 4.62/1.89  
% 4.62/1.89  Simplification rules
% 4.62/1.89  ----------------------
% 4.62/1.89  #Subsume      : 9
% 4.62/1.89  #Demod        : 182
% 4.62/1.89  #Tautology    : 97
% 4.62/1.89  #SimpNegUnit  : 96
% 4.62/1.89  #BackRed      : 2
% 4.62/1.89  
% 4.62/1.89  #Partial instantiations: 0
% 4.62/1.89  #Strategies tried      : 1
% 4.62/1.89  
% 4.62/1.89  Timing (in seconds)
% 4.62/1.89  ----------------------
% 4.62/1.89  Preprocessing        : 0.42
% 4.62/1.89  Parsing              : 0.21
% 4.62/1.89  CNF conversion       : 0.06
% 4.62/1.89  Main loop            : 0.65
% 4.62/1.89  Inferencing          : 0.25
% 4.62/1.89  Reduction            : 0.20
% 4.62/1.89  Demodulation         : 0.14
% 4.62/1.89  BG Simplification    : 0.04
% 4.62/1.89  Subsumption          : 0.12
% 4.62/1.89  Abstraction          : 0.04
% 4.62/1.89  MUC search           : 0.00
% 4.62/1.89  Cooper               : 0.00
% 4.62/1.89  Total                : 1.11
% 4.62/1.89  Index Insertion      : 0.00
% 4.62/1.89  Index Deletion       : 0.00
% 4.62/1.89  Index Matching       : 0.00
% 4.62/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
