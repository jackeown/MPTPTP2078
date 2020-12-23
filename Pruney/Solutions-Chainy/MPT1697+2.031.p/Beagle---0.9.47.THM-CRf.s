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
% DateTime   : Thu Dec  3 10:26:14 EST 2020

% Result     : Theorem 9.44s
% Output     : CNFRefutation 9.44s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 432 expanded)
%              Number of leaves         :   38 ( 176 expanded)
%              Depth                    :   12
%              Number of atoms          :  576 (2480 expanded)
%              Number of equality atoms :   98 ( 444 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_215,negated_conjecture,(
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

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_30,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_53,axiom,(
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

tff(f_75,axiom,(
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

tff(f_38,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_173,axiom,(
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

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_139,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_1006,plain,(
    ! [C_317,A_318,B_319] :
      ( v1_relat_1(C_317)
      | ~ m1_subset_1(C_317,k1_zfmisc_1(k2_zfmisc_1(A_318,B_319))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1014,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_1006])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_1019,plain,(
    ! [A_320,B_321] :
      ( v1_xboole_0(k7_relat_1(A_320,B_321))
      | ~ v1_xboole_0(B_321)
      | ~ v1_relat_1(A_320) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1024,plain,(
    ! [A_322,B_323] :
      ( k7_relat_1(A_322,B_323) = k1_xboole_0
      | ~ v1_xboole_0(B_323)
      | ~ v1_relat_1(A_322) ) ),
    inference(resolution,[status(thm)],[c_1019,c_8])).

tff(c_1031,plain,(
    ! [A_324] :
      ( k7_relat_1(A_324,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_324) ) ),
    inference(resolution,[status(thm)],[c_6,c_1024])).

tff(c_1041,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1014,c_1031])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_1013,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_1006])).

tff(c_1042,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1013,c_1031])).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_60,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_1154,plain,(
    ! [A_335,B_336] :
      ( r1_xboole_0(A_335,B_336)
      | ~ r1_subset_1(A_335,B_336)
      | v1_xboole_0(B_336)
      | v1_xboole_0(A_335) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_5169,plain,(
    ! [A_955,B_956] :
      ( k3_xboole_0(A_955,B_956) = k1_xboole_0
      | ~ r1_subset_1(A_955,B_956)
      | v1_xboole_0(B_956)
      | v1_xboole_0(A_955) ) ),
    inference(resolution,[status(thm)],[c_1154,c_2])).

tff(c_5172,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_5169])).

tff(c_5175,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_64,c_5172])).

tff(c_4891,plain,(
    ! [A_940,B_941,C_942] :
      ( k9_subset_1(A_940,B_941,C_942) = k3_xboole_0(B_941,C_942)
      | ~ m1_subset_1(C_942,k1_zfmisc_1(A_940)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4902,plain,(
    ! [B_941] : k9_subset_1('#skF_1',B_941,'#skF_4') = k3_xboole_0(B_941,'#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_4891])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_56,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_52,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_50,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_5431,plain,(
    ! [E_983,A_987,B_985,D_986,F_982,C_984] :
      ( v1_funct_1(k1_tmap_1(A_987,B_985,C_984,D_986,E_983,F_982))
      | ~ m1_subset_1(F_982,k1_zfmisc_1(k2_zfmisc_1(D_986,B_985)))
      | ~ v1_funct_2(F_982,D_986,B_985)
      | ~ v1_funct_1(F_982)
      | ~ m1_subset_1(E_983,k1_zfmisc_1(k2_zfmisc_1(C_984,B_985)))
      | ~ v1_funct_2(E_983,C_984,B_985)
      | ~ v1_funct_1(E_983)
      | ~ m1_subset_1(D_986,k1_zfmisc_1(A_987))
      | v1_xboole_0(D_986)
      | ~ m1_subset_1(C_984,k1_zfmisc_1(A_987))
      | v1_xboole_0(C_984)
      | v1_xboole_0(B_985)
      | v1_xboole_0(A_987) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_5433,plain,(
    ! [A_987,C_984,E_983] :
      ( v1_funct_1(k1_tmap_1(A_987,'#skF_2',C_984,'#skF_4',E_983,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_983,k1_zfmisc_1(k2_zfmisc_1(C_984,'#skF_2')))
      | ~ v1_funct_2(E_983,C_984,'#skF_2')
      | ~ v1_funct_1(E_983)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_987))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_984,k1_zfmisc_1(A_987))
      | v1_xboole_0(C_984)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_987) ) ),
    inference(resolution,[status(thm)],[c_48,c_5431])).

tff(c_5438,plain,(
    ! [A_987,C_984,E_983] :
      ( v1_funct_1(k1_tmap_1(A_987,'#skF_2',C_984,'#skF_4',E_983,'#skF_6'))
      | ~ m1_subset_1(E_983,k1_zfmisc_1(k2_zfmisc_1(C_984,'#skF_2')))
      | ~ v1_funct_2(E_983,C_984,'#skF_2')
      | ~ v1_funct_1(E_983)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_987))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_984,k1_zfmisc_1(A_987))
      | v1_xboole_0(C_984)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_987) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_5433])).

tff(c_5670,plain,(
    ! [A_1039,C_1040,E_1041] :
      ( v1_funct_1(k1_tmap_1(A_1039,'#skF_2',C_1040,'#skF_4',E_1041,'#skF_6'))
      | ~ m1_subset_1(E_1041,k1_zfmisc_1(k2_zfmisc_1(C_1040,'#skF_2')))
      | ~ v1_funct_2(E_1041,C_1040,'#skF_2')
      | ~ v1_funct_1(E_1041)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1039))
      | ~ m1_subset_1(C_1040,k1_zfmisc_1(A_1039))
      | v1_xboole_0(C_1040)
      | v1_xboole_0(A_1039) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_5438])).

tff(c_5677,plain,(
    ! [A_1039] :
      ( v1_funct_1(k1_tmap_1(A_1039,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1039))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1039))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1039) ) ),
    inference(resolution,[status(thm)],[c_54,c_5670])).

tff(c_5687,plain,(
    ! [A_1039] :
      ( v1_funct_1(k1_tmap_1(A_1039,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1039))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1039))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1039) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_5677])).

tff(c_5793,plain,(
    ! [A_1061] :
      ( v1_funct_1(k1_tmap_1(A_1061,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1061))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1061))
      | v1_xboole_0(A_1061) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_5687])).

tff(c_5796,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_5793])).

tff(c_5799,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_5796])).

tff(c_5800,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_5799])).

tff(c_5230,plain,(
    ! [A_965,B_966,C_967,D_968] :
      ( k2_partfun1(A_965,B_966,C_967,D_968) = k7_relat_1(C_967,D_968)
      | ~ m1_subset_1(C_967,k1_zfmisc_1(k2_zfmisc_1(A_965,B_966)))
      | ~ v1_funct_1(C_967) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_5234,plain,(
    ! [D_968] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_968) = k7_relat_1('#skF_5',D_968)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_5230])).

tff(c_5240,plain,(
    ! [D_968] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_968) = k7_relat_1('#skF_5',D_968) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_5234])).

tff(c_5232,plain,(
    ! [D_968] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_968) = k7_relat_1('#skF_6',D_968)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_48,c_5230])).

tff(c_5237,plain,(
    ! [D_968] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_968) = k7_relat_1('#skF_6',D_968) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_5232])).

tff(c_42,plain,(
    ! [C_158,A_156,D_159,B_157,F_161,E_160] :
      ( v1_funct_2(k1_tmap_1(A_156,B_157,C_158,D_159,E_160,F_161),k4_subset_1(A_156,C_158,D_159),B_157)
      | ~ m1_subset_1(F_161,k1_zfmisc_1(k2_zfmisc_1(D_159,B_157)))
      | ~ v1_funct_2(F_161,D_159,B_157)
      | ~ v1_funct_1(F_161)
      | ~ m1_subset_1(E_160,k1_zfmisc_1(k2_zfmisc_1(C_158,B_157)))
      | ~ v1_funct_2(E_160,C_158,B_157)
      | ~ v1_funct_1(E_160)
      | ~ m1_subset_1(D_159,k1_zfmisc_1(A_156))
      | v1_xboole_0(D_159)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(A_156))
      | v1_xboole_0(C_158)
      | v1_xboole_0(B_157)
      | v1_xboole_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_40,plain,(
    ! [C_158,A_156,D_159,B_157,F_161,E_160] :
      ( m1_subset_1(k1_tmap_1(A_156,B_157,C_158,D_159,E_160,F_161),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_156,C_158,D_159),B_157)))
      | ~ m1_subset_1(F_161,k1_zfmisc_1(k2_zfmisc_1(D_159,B_157)))
      | ~ v1_funct_2(F_161,D_159,B_157)
      | ~ v1_funct_1(F_161)
      | ~ m1_subset_1(E_160,k1_zfmisc_1(k2_zfmisc_1(C_158,B_157)))
      | ~ v1_funct_2(E_160,C_158,B_157)
      | ~ v1_funct_1(E_160)
      | ~ m1_subset_1(D_159,k1_zfmisc_1(A_156))
      | v1_xboole_0(D_159)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(A_156))
      | v1_xboole_0(C_158)
      | v1_xboole_0(B_157)
      | v1_xboole_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_5810,plain,(
    ! [F_1067,B_1071,C_1066,A_1069,E_1070,D_1068] :
      ( k2_partfun1(k4_subset_1(A_1069,C_1066,D_1068),B_1071,k1_tmap_1(A_1069,B_1071,C_1066,D_1068,E_1070,F_1067),C_1066) = E_1070
      | ~ m1_subset_1(k1_tmap_1(A_1069,B_1071,C_1066,D_1068,E_1070,F_1067),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1069,C_1066,D_1068),B_1071)))
      | ~ v1_funct_2(k1_tmap_1(A_1069,B_1071,C_1066,D_1068,E_1070,F_1067),k4_subset_1(A_1069,C_1066,D_1068),B_1071)
      | ~ v1_funct_1(k1_tmap_1(A_1069,B_1071,C_1066,D_1068,E_1070,F_1067))
      | k2_partfun1(D_1068,B_1071,F_1067,k9_subset_1(A_1069,C_1066,D_1068)) != k2_partfun1(C_1066,B_1071,E_1070,k9_subset_1(A_1069,C_1066,D_1068))
      | ~ m1_subset_1(F_1067,k1_zfmisc_1(k2_zfmisc_1(D_1068,B_1071)))
      | ~ v1_funct_2(F_1067,D_1068,B_1071)
      | ~ v1_funct_1(F_1067)
      | ~ m1_subset_1(E_1070,k1_zfmisc_1(k2_zfmisc_1(C_1066,B_1071)))
      | ~ v1_funct_2(E_1070,C_1066,B_1071)
      | ~ v1_funct_1(E_1070)
      | ~ m1_subset_1(D_1068,k1_zfmisc_1(A_1069))
      | v1_xboole_0(D_1068)
      | ~ m1_subset_1(C_1066,k1_zfmisc_1(A_1069))
      | v1_xboole_0(C_1066)
      | v1_xboole_0(B_1071)
      | v1_xboole_0(A_1069) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_6856,plain,(
    ! [B_1242,E_1240,D_1243,C_1241,A_1244,F_1239] :
      ( k2_partfun1(k4_subset_1(A_1244,C_1241,D_1243),B_1242,k1_tmap_1(A_1244,B_1242,C_1241,D_1243,E_1240,F_1239),C_1241) = E_1240
      | ~ v1_funct_2(k1_tmap_1(A_1244,B_1242,C_1241,D_1243,E_1240,F_1239),k4_subset_1(A_1244,C_1241,D_1243),B_1242)
      | ~ v1_funct_1(k1_tmap_1(A_1244,B_1242,C_1241,D_1243,E_1240,F_1239))
      | k2_partfun1(D_1243,B_1242,F_1239,k9_subset_1(A_1244,C_1241,D_1243)) != k2_partfun1(C_1241,B_1242,E_1240,k9_subset_1(A_1244,C_1241,D_1243))
      | ~ m1_subset_1(F_1239,k1_zfmisc_1(k2_zfmisc_1(D_1243,B_1242)))
      | ~ v1_funct_2(F_1239,D_1243,B_1242)
      | ~ v1_funct_1(F_1239)
      | ~ m1_subset_1(E_1240,k1_zfmisc_1(k2_zfmisc_1(C_1241,B_1242)))
      | ~ v1_funct_2(E_1240,C_1241,B_1242)
      | ~ v1_funct_1(E_1240)
      | ~ m1_subset_1(D_1243,k1_zfmisc_1(A_1244))
      | v1_xboole_0(D_1243)
      | ~ m1_subset_1(C_1241,k1_zfmisc_1(A_1244))
      | v1_xboole_0(C_1241)
      | v1_xboole_0(B_1242)
      | v1_xboole_0(A_1244) ) ),
    inference(resolution,[status(thm)],[c_40,c_5810])).

tff(c_7419,plain,(
    ! [B_1365,F_1362,D_1366,E_1363,A_1367,C_1364] :
      ( k2_partfun1(k4_subset_1(A_1367,C_1364,D_1366),B_1365,k1_tmap_1(A_1367,B_1365,C_1364,D_1366,E_1363,F_1362),C_1364) = E_1363
      | ~ v1_funct_1(k1_tmap_1(A_1367,B_1365,C_1364,D_1366,E_1363,F_1362))
      | k2_partfun1(D_1366,B_1365,F_1362,k9_subset_1(A_1367,C_1364,D_1366)) != k2_partfun1(C_1364,B_1365,E_1363,k9_subset_1(A_1367,C_1364,D_1366))
      | ~ m1_subset_1(F_1362,k1_zfmisc_1(k2_zfmisc_1(D_1366,B_1365)))
      | ~ v1_funct_2(F_1362,D_1366,B_1365)
      | ~ v1_funct_1(F_1362)
      | ~ m1_subset_1(E_1363,k1_zfmisc_1(k2_zfmisc_1(C_1364,B_1365)))
      | ~ v1_funct_2(E_1363,C_1364,B_1365)
      | ~ v1_funct_1(E_1363)
      | ~ m1_subset_1(D_1366,k1_zfmisc_1(A_1367))
      | v1_xboole_0(D_1366)
      | ~ m1_subset_1(C_1364,k1_zfmisc_1(A_1367))
      | v1_xboole_0(C_1364)
      | v1_xboole_0(B_1365)
      | v1_xboole_0(A_1367) ) ),
    inference(resolution,[status(thm)],[c_42,c_6856])).

tff(c_7423,plain,(
    ! [A_1367,C_1364,E_1363] :
      ( k2_partfun1(k4_subset_1(A_1367,C_1364,'#skF_4'),'#skF_2',k1_tmap_1(A_1367,'#skF_2',C_1364,'#skF_4',E_1363,'#skF_6'),C_1364) = E_1363
      | ~ v1_funct_1(k1_tmap_1(A_1367,'#skF_2',C_1364,'#skF_4',E_1363,'#skF_6'))
      | k2_partfun1(C_1364,'#skF_2',E_1363,k9_subset_1(A_1367,C_1364,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_1367,C_1364,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1363,k1_zfmisc_1(k2_zfmisc_1(C_1364,'#skF_2')))
      | ~ v1_funct_2(E_1363,C_1364,'#skF_2')
      | ~ v1_funct_1(E_1363)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1367))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1364,k1_zfmisc_1(A_1367))
      | v1_xboole_0(C_1364)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1367) ) ),
    inference(resolution,[status(thm)],[c_48,c_7419])).

tff(c_7429,plain,(
    ! [A_1367,C_1364,E_1363] :
      ( k2_partfun1(k4_subset_1(A_1367,C_1364,'#skF_4'),'#skF_2',k1_tmap_1(A_1367,'#skF_2',C_1364,'#skF_4',E_1363,'#skF_6'),C_1364) = E_1363
      | ~ v1_funct_1(k1_tmap_1(A_1367,'#skF_2',C_1364,'#skF_4',E_1363,'#skF_6'))
      | k2_partfun1(C_1364,'#skF_2',E_1363,k9_subset_1(A_1367,C_1364,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1367,C_1364,'#skF_4'))
      | ~ m1_subset_1(E_1363,k1_zfmisc_1(k2_zfmisc_1(C_1364,'#skF_2')))
      | ~ v1_funct_2(E_1363,C_1364,'#skF_2')
      | ~ v1_funct_1(E_1363)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1367))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1364,k1_zfmisc_1(A_1367))
      | v1_xboole_0(C_1364)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1367) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_5237,c_7423])).

tff(c_8503,plain,(
    ! [A_1537,C_1538,E_1539] :
      ( k2_partfun1(k4_subset_1(A_1537,C_1538,'#skF_4'),'#skF_2',k1_tmap_1(A_1537,'#skF_2',C_1538,'#skF_4',E_1539,'#skF_6'),C_1538) = E_1539
      | ~ v1_funct_1(k1_tmap_1(A_1537,'#skF_2',C_1538,'#skF_4',E_1539,'#skF_6'))
      | k2_partfun1(C_1538,'#skF_2',E_1539,k9_subset_1(A_1537,C_1538,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1537,C_1538,'#skF_4'))
      | ~ m1_subset_1(E_1539,k1_zfmisc_1(k2_zfmisc_1(C_1538,'#skF_2')))
      | ~ v1_funct_2(E_1539,C_1538,'#skF_2')
      | ~ v1_funct_1(E_1539)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1537))
      | ~ m1_subset_1(C_1538,k1_zfmisc_1(A_1537))
      | v1_xboole_0(C_1538)
      | v1_xboole_0(A_1537) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_7429])).

tff(c_8510,plain,(
    ! [A_1537] :
      ( k2_partfun1(k4_subset_1(A_1537,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1537,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1537,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1537,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1537,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1537))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1537))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1537) ) ),
    inference(resolution,[status(thm)],[c_54,c_8503])).

tff(c_8520,plain,(
    ! [A_1537] :
      ( k2_partfun1(k4_subset_1(A_1537,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1537,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1537,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1537,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1537,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1537))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1537))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1537) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_5240,c_8510])).

tff(c_9074,plain,(
    ! [A_1662] :
      ( k2_partfun1(k4_subset_1(A_1662,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1662,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1662,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1662,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1662,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1662))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1662))
      | v1_xboole_0(A_1662) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_8520])).

tff(c_1623,plain,(
    ! [A_366,B_367] :
      ( k3_xboole_0(A_366,B_367) = k1_xboole_0
      | ~ r1_subset_1(A_366,B_367)
      | v1_xboole_0(B_367)
      | v1_xboole_0(A_366) ) ),
    inference(resolution,[status(thm)],[c_1154,c_2])).

tff(c_1626,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_1623])).

tff(c_1629,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_64,c_1626])).

tff(c_1320,plain,(
    ! [A_345,B_346,C_347] :
      ( k9_subset_1(A_345,B_346,C_347) = k3_xboole_0(B_346,C_347)
      | ~ m1_subset_1(C_347,k1_zfmisc_1(A_345)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1331,plain,(
    ! [B_346] : k9_subset_1('#skF_1',B_346,'#skF_4') = k3_xboole_0(B_346,'#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_1320])).

tff(c_1675,plain,(
    ! [E_375,C_376,A_379,B_377,F_374,D_378] :
      ( v1_funct_1(k1_tmap_1(A_379,B_377,C_376,D_378,E_375,F_374))
      | ~ m1_subset_1(F_374,k1_zfmisc_1(k2_zfmisc_1(D_378,B_377)))
      | ~ v1_funct_2(F_374,D_378,B_377)
      | ~ v1_funct_1(F_374)
      | ~ m1_subset_1(E_375,k1_zfmisc_1(k2_zfmisc_1(C_376,B_377)))
      | ~ v1_funct_2(E_375,C_376,B_377)
      | ~ v1_funct_1(E_375)
      | ~ m1_subset_1(D_378,k1_zfmisc_1(A_379))
      | v1_xboole_0(D_378)
      | ~ m1_subset_1(C_376,k1_zfmisc_1(A_379))
      | v1_xboole_0(C_376)
      | v1_xboole_0(B_377)
      | v1_xboole_0(A_379) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_1677,plain,(
    ! [A_379,C_376,E_375] :
      ( v1_funct_1(k1_tmap_1(A_379,'#skF_2',C_376,'#skF_4',E_375,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_375,k1_zfmisc_1(k2_zfmisc_1(C_376,'#skF_2')))
      | ~ v1_funct_2(E_375,C_376,'#skF_2')
      | ~ v1_funct_1(E_375)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_379))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_376,k1_zfmisc_1(A_379))
      | v1_xboole_0(C_376)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_379) ) ),
    inference(resolution,[status(thm)],[c_48,c_1675])).

tff(c_1682,plain,(
    ! [A_379,C_376,E_375] :
      ( v1_funct_1(k1_tmap_1(A_379,'#skF_2',C_376,'#skF_4',E_375,'#skF_6'))
      | ~ m1_subset_1(E_375,k1_zfmisc_1(k2_zfmisc_1(C_376,'#skF_2')))
      | ~ v1_funct_2(E_375,C_376,'#skF_2')
      | ~ v1_funct_1(E_375)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_379))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_376,k1_zfmisc_1(A_379))
      | v1_xboole_0(C_376)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_379) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1677])).

tff(c_1851,plain,(
    ! [A_385,C_386,E_387] :
      ( v1_funct_1(k1_tmap_1(A_385,'#skF_2',C_386,'#skF_4',E_387,'#skF_6'))
      | ~ m1_subset_1(E_387,k1_zfmisc_1(k2_zfmisc_1(C_386,'#skF_2')))
      | ~ v1_funct_2(E_387,C_386,'#skF_2')
      | ~ v1_funct_1(E_387)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_385))
      | ~ m1_subset_1(C_386,k1_zfmisc_1(A_385))
      | v1_xboole_0(C_386)
      | v1_xboole_0(A_385) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_1682])).

tff(c_1855,plain,(
    ! [A_385] :
      ( v1_funct_1(k1_tmap_1(A_385,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_385))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_385))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_385) ) ),
    inference(resolution,[status(thm)],[c_54,c_1851])).

tff(c_1862,plain,(
    ! [A_385] :
      ( v1_funct_1(k1_tmap_1(A_385,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_385))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_385))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_385) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1855])).

tff(c_1889,plain,(
    ! [A_403] :
      ( v1_funct_1(k1_tmap_1(A_403,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_403))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_403))
      | v1_xboole_0(A_403) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1862])).

tff(c_1892,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_1889])).

tff(c_1895,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1892])).

tff(c_1896,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1895])).

tff(c_1548,plain,(
    ! [A_358,B_359,C_360,D_361] :
      ( k2_partfun1(A_358,B_359,C_360,D_361) = k7_relat_1(C_360,D_361)
      | ~ m1_subset_1(C_360,k1_zfmisc_1(k2_zfmisc_1(A_358,B_359)))
      | ~ v1_funct_1(C_360) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1552,plain,(
    ! [D_361] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_361) = k7_relat_1('#skF_5',D_361)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_1548])).

tff(c_1558,plain,(
    ! [D_361] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_361) = k7_relat_1('#skF_5',D_361) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1552])).

tff(c_1550,plain,(
    ! [D_361] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_361) = k7_relat_1('#skF_6',D_361)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_48,c_1548])).

tff(c_1555,plain,(
    ! [D_361] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_361) = k7_relat_1('#skF_6',D_361) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1550])).

tff(c_2096,plain,(
    ! [E_446,D_444,C_442,B_447,A_445,F_443] :
      ( k2_partfun1(k4_subset_1(A_445,C_442,D_444),B_447,k1_tmap_1(A_445,B_447,C_442,D_444,E_446,F_443),D_444) = F_443
      | ~ m1_subset_1(k1_tmap_1(A_445,B_447,C_442,D_444,E_446,F_443),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_445,C_442,D_444),B_447)))
      | ~ v1_funct_2(k1_tmap_1(A_445,B_447,C_442,D_444,E_446,F_443),k4_subset_1(A_445,C_442,D_444),B_447)
      | ~ v1_funct_1(k1_tmap_1(A_445,B_447,C_442,D_444,E_446,F_443))
      | k2_partfun1(D_444,B_447,F_443,k9_subset_1(A_445,C_442,D_444)) != k2_partfun1(C_442,B_447,E_446,k9_subset_1(A_445,C_442,D_444))
      | ~ m1_subset_1(F_443,k1_zfmisc_1(k2_zfmisc_1(D_444,B_447)))
      | ~ v1_funct_2(F_443,D_444,B_447)
      | ~ v1_funct_1(F_443)
      | ~ m1_subset_1(E_446,k1_zfmisc_1(k2_zfmisc_1(C_442,B_447)))
      | ~ v1_funct_2(E_446,C_442,B_447)
      | ~ v1_funct_1(E_446)
      | ~ m1_subset_1(D_444,k1_zfmisc_1(A_445))
      | v1_xboole_0(D_444)
      | ~ m1_subset_1(C_442,k1_zfmisc_1(A_445))
      | v1_xboole_0(C_442)
      | v1_xboole_0(B_447)
      | v1_xboole_0(A_445) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_3170,plain,(
    ! [E_605,D_608,C_606,F_604,A_609,B_607] :
      ( k2_partfun1(k4_subset_1(A_609,C_606,D_608),B_607,k1_tmap_1(A_609,B_607,C_606,D_608,E_605,F_604),D_608) = F_604
      | ~ v1_funct_2(k1_tmap_1(A_609,B_607,C_606,D_608,E_605,F_604),k4_subset_1(A_609,C_606,D_608),B_607)
      | ~ v1_funct_1(k1_tmap_1(A_609,B_607,C_606,D_608,E_605,F_604))
      | k2_partfun1(D_608,B_607,F_604,k9_subset_1(A_609,C_606,D_608)) != k2_partfun1(C_606,B_607,E_605,k9_subset_1(A_609,C_606,D_608))
      | ~ m1_subset_1(F_604,k1_zfmisc_1(k2_zfmisc_1(D_608,B_607)))
      | ~ v1_funct_2(F_604,D_608,B_607)
      | ~ v1_funct_1(F_604)
      | ~ m1_subset_1(E_605,k1_zfmisc_1(k2_zfmisc_1(C_606,B_607)))
      | ~ v1_funct_2(E_605,C_606,B_607)
      | ~ v1_funct_1(E_605)
      | ~ m1_subset_1(D_608,k1_zfmisc_1(A_609))
      | v1_xboole_0(D_608)
      | ~ m1_subset_1(C_606,k1_zfmisc_1(A_609))
      | v1_xboole_0(C_606)
      | v1_xboole_0(B_607)
      | v1_xboole_0(A_609) ) ),
    inference(resolution,[status(thm)],[c_40,c_2096])).

tff(c_3495,plain,(
    ! [F_695,A_700,E_696,D_699,C_697,B_698] :
      ( k2_partfun1(k4_subset_1(A_700,C_697,D_699),B_698,k1_tmap_1(A_700,B_698,C_697,D_699,E_696,F_695),D_699) = F_695
      | ~ v1_funct_1(k1_tmap_1(A_700,B_698,C_697,D_699,E_696,F_695))
      | k2_partfun1(D_699,B_698,F_695,k9_subset_1(A_700,C_697,D_699)) != k2_partfun1(C_697,B_698,E_696,k9_subset_1(A_700,C_697,D_699))
      | ~ m1_subset_1(F_695,k1_zfmisc_1(k2_zfmisc_1(D_699,B_698)))
      | ~ v1_funct_2(F_695,D_699,B_698)
      | ~ v1_funct_1(F_695)
      | ~ m1_subset_1(E_696,k1_zfmisc_1(k2_zfmisc_1(C_697,B_698)))
      | ~ v1_funct_2(E_696,C_697,B_698)
      | ~ v1_funct_1(E_696)
      | ~ m1_subset_1(D_699,k1_zfmisc_1(A_700))
      | v1_xboole_0(D_699)
      | ~ m1_subset_1(C_697,k1_zfmisc_1(A_700))
      | v1_xboole_0(C_697)
      | v1_xboole_0(B_698)
      | v1_xboole_0(A_700) ) ),
    inference(resolution,[status(thm)],[c_42,c_3170])).

tff(c_3499,plain,(
    ! [A_700,C_697,E_696] :
      ( k2_partfun1(k4_subset_1(A_700,C_697,'#skF_4'),'#skF_2',k1_tmap_1(A_700,'#skF_2',C_697,'#skF_4',E_696,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_700,'#skF_2',C_697,'#skF_4',E_696,'#skF_6'))
      | k2_partfun1(C_697,'#skF_2',E_696,k9_subset_1(A_700,C_697,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_700,C_697,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_696,k1_zfmisc_1(k2_zfmisc_1(C_697,'#skF_2')))
      | ~ v1_funct_2(E_696,C_697,'#skF_2')
      | ~ v1_funct_1(E_696)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_700))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_697,k1_zfmisc_1(A_700))
      | v1_xboole_0(C_697)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_700) ) ),
    inference(resolution,[status(thm)],[c_48,c_3495])).

tff(c_3505,plain,(
    ! [A_700,C_697,E_696] :
      ( k2_partfun1(k4_subset_1(A_700,C_697,'#skF_4'),'#skF_2',k1_tmap_1(A_700,'#skF_2',C_697,'#skF_4',E_696,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_700,'#skF_2',C_697,'#skF_4',E_696,'#skF_6'))
      | k2_partfun1(C_697,'#skF_2',E_696,k9_subset_1(A_700,C_697,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_700,C_697,'#skF_4'))
      | ~ m1_subset_1(E_696,k1_zfmisc_1(k2_zfmisc_1(C_697,'#skF_2')))
      | ~ v1_funct_2(E_696,C_697,'#skF_2')
      | ~ v1_funct_1(E_696)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_700))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_697,k1_zfmisc_1(A_700))
      | v1_xboole_0(C_697)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_700) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1555,c_3499])).

tff(c_4315,plain,(
    ! [A_857,C_858,E_859] :
      ( k2_partfun1(k4_subset_1(A_857,C_858,'#skF_4'),'#skF_2',k1_tmap_1(A_857,'#skF_2',C_858,'#skF_4',E_859,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_857,'#skF_2',C_858,'#skF_4',E_859,'#skF_6'))
      | k2_partfun1(C_858,'#skF_2',E_859,k9_subset_1(A_857,C_858,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_857,C_858,'#skF_4'))
      | ~ m1_subset_1(E_859,k1_zfmisc_1(k2_zfmisc_1(C_858,'#skF_2')))
      | ~ v1_funct_2(E_859,C_858,'#skF_2')
      | ~ v1_funct_1(E_859)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_857))
      | ~ m1_subset_1(C_858,k1_zfmisc_1(A_857))
      | v1_xboole_0(C_858)
      | v1_xboole_0(A_857) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_3505])).

tff(c_4322,plain,(
    ! [A_857] :
      ( k2_partfun1(k4_subset_1(A_857,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_857,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_857,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_857,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_857,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_857))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_857))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_857) ) ),
    inference(resolution,[status(thm)],[c_54,c_4315])).

tff(c_4332,plain,(
    ! [A_857] :
      ( k2_partfun1(k4_subset_1(A_857,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_857,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_857,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_857,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_857,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_857))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_857))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_857) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1558,c_4322])).

tff(c_4759,plain,(
    ! [A_933] :
      ( k2_partfun1(k4_subset_1(A_933,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_933,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_933,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_933,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_933,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_933))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_933))
      | v1_xboole_0(A_933) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_4332])).

tff(c_113,plain,(
    ! [C_230,A_231,B_232] :
      ( v1_relat_1(C_230)
      | ~ m1_subset_1(C_230,k1_zfmisc_1(k2_zfmisc_1(A_231,B_232))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_120,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_113])).

tff(c_108,plain,(
    ! [A_228,B_229] :
      ( v1_xboole_0(k7_relat_1(A_228,B_229))
      | ~ v1_xboole_0(B_229)
      | ~ v1_relat_1(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_122,plain,(
    ! [A_233,B_234] :
      ( k7_relat_1(A_233,B_234) = k1_xboole_0
      | ~ v1_xboole_0(B_234)
      | ~ v1_relat_1(A_233) ) ),
    inference(resolution,[status(thm)],[c_108,c_8])).

tff(c_129,plain,(
    ! [A_235] :
      ( k7_relat_1(A_235,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_235) ) ),
    inference(resolution,[status(thm)],[c_6,c_122])).

tff(c_140,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_120,c_129])).

tff(c_252,plain,(
    ! [A_246,B_247] :
      ( r1_xboole_0(A_246,B_247)
      | ~ r1_subset_1(A_246,B_247)
      | v1_xboole_0(B_247)
      | v1_xboole_0(A_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_734,plain,(
    ! [A_289,B_290] :
      ( k3_xboole_0(A_289,B_290) = k1_xboole_0
      | ~ r1_subset_1(A_289,B_290)
      | v1_xboole_0(B_290)
      | v1_xboole_0(A_289) ) ),
    inference(resolution,[status(thm)],[c_252,c_2])).

tff(c_737,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_734])).

tff(c_740,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_64,c_737])).

tff(c_121,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_113])).

tff(c_139,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_121,c_129])).

tff(c_455,plain,(
    ! [A_262,B_263,C_264,D_265] :
      ( k2_partfun1(A_262,B_263,C_264,D_265) = k7_relat_1(C_264,D_265)
      | ~ m1_subset_1(C_264,k1_zfmisc_1(k2_zfmisc_1(A_262,B_263)))
      | ~ v1_funct_1(C_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_459,plain,(
    ! [D_265] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_265) = k7_relat_1('#skF_5',D_265)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_455])).

tff(c_465,plain,(
    ! [D_265] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_265) = k7_relat_1('#skF_5',D_265) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_459])).

tff(c_457,plain,(
    ! [D_265] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_265) = k7_relat_1('#skF_6',D_265)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_48,c_455])).

tff(c_462,plain,(
    ! [D_265] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_265) = k7_relat_1('#skF_6',D_265) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_457])).

tff(c_315,plain,(
    ! [A_250,B_251,C_252] :
      ( k9_subset_1(A_250,B_251,C_252) = k3_xboole_0(B_251,C_252)
      | ~ m1_subset_1(C_252,k1_zfmisc_1(A_250)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_326,plain,(
    ! [B_251] : k9_subset_1('#skF_1',B_251,'#skF_4') = k3_xboole_0(B_251,'#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_315])).

tff(c_46,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_105,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_328,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_326,c_105])).

tff(c_1001,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_740,c_139,c_740,c_465,c_462,c_328])).

tff(c_1002,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1217,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1002])).

tff(c_4770,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4759,c_1217])).

tff(c_4784,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_1041,c_1042,c_1629,c_1331,c_1629,c_1331,c_1896,c_4770])).

tff(c_4786,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_4784])).

tff(c_4787,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1002])).

tff(c_9083,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_9074,c_4787])).

tff(c_9094,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_1041,c_1042,c_5175,c_4902,c_5175,c_4902,c_5800,c_9083])).

tff(c_9096,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_9094])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:47:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.44/3.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.44/3.73  
% 9.44/3.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.44/3.73  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.44/3.73  
% 9.44/3.73  %Foreground sorts:
% 9.44/3.73  
% 9.44/3.73  
% 9.44/3.73  %Background operators:
% 9.44/3.73  
% 9.44/3.73  
% 9.44/3.73  %Foreground operators:
% 9.44/3.73  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 9.44/3.73  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.44/3.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.44/3.73  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.44/3.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.44/3.73  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 9.44/3.73  tff('#skF_5', type, '#skF_5': $i).
% 9.44/3.73  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.44/3.73  tff('#skF_6', type, '#skF_6': $i).
% 9.44/3.73  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.44/3.73  tff('#skF_2', type, '#skF_2': $i).
% 9.44/3.73  tff('#skF_3', type, '#skF_3': $i).
% 9.44/3.73  tff('#skF_1', type, '#skF_1': $i).
% 9.44/3.73  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.44/3.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.44/3.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.44/3.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.44/3.73  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.44/3.73  tff('#skF_4', type, '#skF_4': $i).
% 9.44/3.73  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.44/3.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.44/3.73  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 9.44/3.73  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.44/3.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.44/3.73  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.44/3.73  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 9.44/3.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.44/3.73  
% 9.44/3.75  tff(f_215, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 9.44/3.75  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.44/3.75  tff(f_30, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.44/3.75  tff(f_53, axiom, (![A, B]: ((v1_relat_1(A) & v1_xboole_0(B)) => (v1_xboole_0(k7_relat_1(A, B)) & v1_relat_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc16_relat_1)).
% 9.44/3.75  tff(f_34, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 9.44/3.75  tff(f_75, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 9.44/3.75  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 9.44/3.75  tff(f_38, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 9.44/3.75  tff(f_173, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 9.44/3.75  tff(f_91, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 9.44/3.75  tff(f_139, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 9.44/3.75  tff(c_72, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_215])).
% 9.44/3.75  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_215])).
% 9.44/3.75  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_215])).
% 9.44/3.75  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_215])).
% 9.44/3.75  tff(c_1006, plain, (![C_317, A_318, B_319]: (v1_relat_1(C_317) | ~m1_subset_1(C_317, k1_zfmisc_1(k2_zfmisc_1(A_318, B_319))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.44/3.75  tff(c_1014, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_1006])).
% 9.44/3.75  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 9.44/3.75  tff(c_1019, plain, (![A_320, B_321]: (v1_xboole_0(k7_relat_1(A_320, B_321)) | ~v1_xboole_0(B_321) | ~v1_relat_1(A_320))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.44/3.75  tff(c_8, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.44/3.75  tff(c_1024, plain, (![A_322, B_323]: (k7_relat_1(A_322, B_323)=k1_xboole_0 | ~v1_xboole_0(B_323) | ~v1_relat_1(A_322))), inference(resolution, [status(thm)], [c_1019, c_8])).
% 9.44/3.75  tff(c_1031, plain, (![A_324]: (k7_relat_1(A_324, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_324))), inference(resolution, [status(thm)], [c_6, c_1024])).
% 9.44/3.75  tff(c_1041, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_1014, c_1031])).
% 9.44/3.75  tff(c_48, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_215])).
% 9.44/3.75  tff(c_1013, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_48, c_1006])).
% 9.44/3.75  tff(c_1042, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_1013, c_1031])).
% 9.44/3.75  tff(c_68, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_215])).
% 9.44/3.75  tff(c_64, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_215])).
% 9.44/3.75  tff(c_60, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_215])).
% 9.44/3.75  tff(c_1154, plain, (![A_335, B_336]: (r1_xboole_0(A_335, B_336) | ~r1_subset_1(A_335, B_336) | v1_xboole_0(B_336) | v1_xboole_0(A_335))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.44/3.75  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.44/3.75  tff(c_5169, plain, (![A_955, B_956]: (k3_xboole_0(A_955, B_956)=k1_xboole_0 | ~r1_subset_1(A_955, B_956) | v1_xboole_0(B_956) | v1_xboole_0(A_955))), inference(resolution, [status(thm)], [c_1154, c_2])).
% 9.44/3.75  tff(c_5172, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_5169])).
% 9.44/3.75  tff(c_5175, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_68, c_64, c_5172])).
% 9.44/3.75  tff(c_4891, plain, (![A_940, B_941, C_942]: (k9_subset_1(A_940, B_941, C_942)=k3_xboole_0(B_941, C_942) | ~m1_subset_1(C_942, k1_zfmisc_1(A_940)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.44/3.75  tff(c_4902, plain, (![B_941]: (k9_subset_1('#skF_1', B_941, '#skF_4')=k3_xboole_0(B_941, '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_4891])).
% 9.44/3.75  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_215])).
% 9.44/3.75  tff(c_56, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_215])).
% 9.44/3.75  tff(c_70, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_215])).
% 9.44/3.75  tff(c_52, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_215])).
% 9.44/3.75  tff(c_50, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_215])).
% 9.44/3.75  tff(c_5431, plain, (![E_983, A_987, B_985, D_986, F_982, C_984]: (v1_funct_1(k1_tmap_1(A_987, B_985, C_984, D_986, E_983, F_982)) | ~m1_subset_1(F_982, k1_zfmisc_1(k2_zfmisc_1(D_986, B_985))) | ~v1_funct_2(F_982, D_986, B_985) | ~v1_funct_1(F_982) | ~m1_subset_1(E_983, k1_zfmisc_1(k2_zfmisc_1(C_984, B_985))) | ~v1_funct_2(E_983, C_984, B_985) | ~v1_funct_1(E_983) | ~m1_subset_1(D_986, k1_zfmisc_1(A_987)) | v1_xboole_0(D_986) | ~m1_subset_1(C_984, k1_zfmisc_1(A_987)) | v1_xboole_0(C_984) | v1_xboole_0(B_985) | v1_xboole_0(A_987))), inference(cnfTransformation, [status(thm)], [f_173])).
% 9.44/3.75  tff(c_5433, plain, (![A_987, C_984, E_983]: (v1_funct_1(k1_tmap_1(A_987, '#skF_2', C_984, '#skF_4', E_983, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_983, k1_zfmisc_1(k2_zfmisc_1(C_984, '#skF_2'))) | ~v1_funct_2(E_983, C_984, '#skF_2') | ~v1_funct_1(E_983) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_987)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_984, k1_zfmisc_1(A_987)) | v1_xboole_0(C_984) | v1_xboole_0('#skF_2') | v1_xboole_0(A_987))), inference(resolution, [status(thm)], [c_48, c_5431])).
% 9.44/3.75  tff(c_5438, plain, (![A_987, C_984, E_983]: (v1_funct_1(k1_tmap_1(A_987, '#skF_2', C_984, '#skF_4', E_983, '#skF_6')) | ~m1_subset_1(E_983, k1_zfmisc_1(k2_zfmisc_1(C_984, '#skF_2'))) | ~v1_funct_2(E_983, C_984, '#skF_2') | ~v1_funct_1(E_983) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_987)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_984, k1_zfmisc_1(A_987)) | v1_xboole_0(C_984) | v1_xboole_0('#skF_2') | v1_xboole_0(A_987))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_5433])).
% 9.44/3.75  tff(c_5670, plain, (![A_1039, C_1040, E_1041]: (v1_funct_1(k1_tmap_1(A_1039, '#skF_2', C_1040, '#skF_4', E_1041, '#skF_6')) | ~m1_subset_1(E_1041, k1_zfmisc_1(k2_zfmisc_1(C_1040, '#skF_2'))) | ~v1_funct_2(E_1041, C_1040, '#skF_2') | ~v1_funct_1(E_1041) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1039)) | ~m1_subset_1(C_1040, k1_zfmisc_1(A_1039)) | v1_xboole_0(C_1040) | v1_xboole_0(A_1039))), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_5438])).
% 9.44/3.75  tff(c_5677, plain, (![A_1039]: (v1_funct_1(k1_tmap_1(A_1039, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1039)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1039)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1039))), inference(resolution, [status(thm)], [c_54, c_5670])).
% 9.44/3.75  tff(c_5687, plain, (![A_1039]: (v1_funct_1(k1_tmap_1(A_1039, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1039)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1039)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1039))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_5677])).
% 9.44/3.75  tff(c_5793, plain, (![A_1061]: (v1_funct_1(k1_tmap_1(A_1061, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1061)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1061)) | v1_xboole_0(A_1061))), inference(negUnitSimplification, [status(thm)], [c_68, c_5687])).
% 9.44/3.75  tff(c_5796, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_66, c_5793])).
% 9.44/3.75  tff(c_5799, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_5796])).
% 9.44/3.75  tff(c_5800, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_72, c_5799])).
% 9.44/3.75  tff(c_5230, plain, (![A_965, B_966, C_967, D_968]: (k2_partfun1(A_965, B_966, C_967, D_968)=k7_relat_1(C_967, D_968) | ~m1_subset_1(C_967, k1_zfmisc_1(k2_zfmisc_1(A_965, B_966))) | ~v1_funct_1(C_967))), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.44/3.75  tff(c_5234, plain, (![D_968]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_968)=k7_relat_1('#skF_5', D_968) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_5230])).
% 9.44/3.75  tff(c_5240, plain, (![D_968]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_968)=k7_relat_1('#skF_5', D_968))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_5234])).
% 9.44/3.75  tff(c_5232, plain, (![D_968]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_968)=k7_relat_1('#skF_6', D_968) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_48, c_5230])).
% 9.44/3.75  tff(c_5237, plain, (![D_968]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_968)=k7_relat_1('#skF_6', D_968))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_5232])).
% 9.44/3.75  tff(c_42, plain, (![C_158, A_156, D_159, B_157, F_161, E_160]: (v1_funct_2(k1_tmap_1(A_156, B_157, C_158, D_159, E_160, F_161), k4_subset_1(A_156, C_158, D_159), B_157) | ~m1_subset_1(F_161, k1_zfmisc_1(k2_zfmisc_1(D_159, B_157))) | ~v1_funct_2(F_161, D_159, B_157) | ~v1_funct_1(F_161) | ~m1_subset_1(E_160, k1_zfmisc_1(k2_zfmisc_1(C_158, B_157))) | ~v1_funct_2(E_160, C_158, B_157) | ~v1_funct_1(E_160) | ~m1_subset_1(D_159, k1_zfmisc_1(A_156)) | v1_xboole_0(D_159) | ~m1_subset_1(C_158, k1_zfmisc_1(A_156)) | v1_xboole_0(C_158) | v1_xboole_0(B_157) | v1_xboole_0(A_156))), inference(cnfTransformation, [status(thm)], [f_173])).
% 9.44/3.75  tff(c_40, plain, (![C_158, A_156, D_159, B_157, F_161, E_160]: (m1_subset_1(k1_tmap_1(A_156, B_157, C_158, D_159, E_160, F_161), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_156, C_158, D_159), B_157))) | ~m1_subset_1(F_161, k1_zfmisc_1(k2_zfmisc_1(D_159, B_157))) | ~v1_funct_2(F_161, D_159, B_157) | ~v1_funct_1(F_161) | ~m1_subset_1(E_160, k1_zfmisc_1(k2_zfmisc_1(C_158, B_157))) | ~v1_funct_2(E_160, C_158, B_157) | ~v1_funct_1(E_160) | ~m1_subset_1(D_159, k1_zfmisc_1(A_156)) | v1_xboole_0(D_159) | ~m1_subset_1(C_158, k1_zfmisc_1(A_156)) | v1_xboole_0(C_158) | v1_xboole_0(B_157) | v1_xboole_0(A_156))), inference(cnfTransformation, [status(thm)], [f_173])).
% 9.44/3.75  tff(c_5810, plain, (![F_1067, B_1071, C_1066, A_1069, E_1070, D_1068]: (k2_partfun1(k4_subset_1(A_1069, C_1066, D_1068), B_1071, k1_tmap_1(A_1069, B_1071, C_1066, D_1068, E_1070, F_1067), C_1066)=E_1070 | ~m1_subset_1(k1_tmap_1(A_1069, B_1071, C_1066, D_1068, E_1070, F_1067), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1069, C_1066, D_1068), B_1071))) | ~v1_funct_2(k1_tmap_1(A_1069, B_1071, C_1066, D_1068, E_1070, F_1067), k4_subset_1(A_1069, C_1066, D_1068), B_1071) | ~v1_funct_1(k1_tmap_1(A_1069, B_1071, C_1066, D_1068, E_1070, F_1067)) | k2_partfun1(D_1068, B_1071, F_1067, k9_subset_1(A_1069, C_1066, D_1068))!=k2_partfun1(C_1066, B_1071, E_1070, k9_subset_1(A_1069, C_1066, D_1068)) | ~m1_subset_1(F_1067, k1_zfmisc_1(k2_zfmisc_1(D_1068, B_1071))) | ~v1_funct_2(F_1067, D_1068, B_1071) | ~v1_funct_1(F_1067) | ~m1_subset_1(E_1070, k1_zfmisc_1(k2_zfmisc_1(C_1066, B_1071))) | ~v1_funct_2(E_1070, C_1066, B_1071) | ~v1_funct_1(E_1070) | ~m1_subset_1(D_1068, k1_zfmisc_1(A_1069)) | v1_xboole_0(D_1068) | ~m1_subset_1(C_1066, k1_zfmisc_1(A_1069)) | v1_xboole_0(C_1066) | v1_xboole_0(B_1071) | v1_xboole_0(A_1069))), inference(cnfTransformation, [status(thm)], [f_139])).
% 9.44/3.75  tff(c_6856, plain, (![B_1242, E_1240, D_1243, C_1241, A_1244, F_1239]: (k2_partfun1(k4_subset_1(A_1244, C_1241, D_1243), B_1242, k1_tmap_1(A_1244, B_1242, C_1241, D_1243, E_1240, F_1239), C_1241)=E_1240 | ~v1_funct_2(k1_tmap_1(A_1244, B_1242, C_1241, D_1243, E_1240, F_1239), k4_subset_1(A_1244, C_1241, D_1243), B_1242) | ~v1_funct_1(k1_tmap_1(A_1244, B_1242, C_1241, D_1243, E_1240, F_1239)) | k2_partfun1(D_1243, B_1242, F_1239, k9_subset_1(A_1244, C_1241, D_1243))!=k2_partfun1(C_1241, B_1242, E_1240, k9_subset_1(A_1244, C_1241, D_1243)) | ~m1_subset_1(F_1239, k1_zfmisc_1(k2_zfmisc_1(D_1243, B_1242))) | ~v1_funct_2(F_1239, D_1243, B_1242) | ~v1_funct_1(F_1239) | ~m1_subset_1(E_1240, k1_zfmisc_1(k2_zfmisc_1(C_1241, B_1242))) | ~v1_funct_2(E_1240, C_1241, B_1242) | ~v1_funct_1(E_1240) | ~m1_subset_1(D_1243, k1_zfmisc_1(A_1244)) | v1_xboole_0(D_1243) | ~m1_subset_1(C_1241, k1_zfmisc_1(A_1244)) | v1_xboole_0(C_1241) | v1_xboole_0(B_1242) | v1_xboole_0(A_1244))), inference(resolution, [status(thm)], [c_40, c_5810])).
% 9.44/3.75  tff(c_7419, plain, (![B_1365, F_1362, D_1366, E_1363, A_1367, C_1364]: (k2_partfun1(k4_subset_1(A_1367, C_1364, D_1366), B_1365, k1_tmap_1(A_1367, B_1365, C_1364, D_1366, E_1363, F_1362), C_1364)=E_1363 | ~v1_funct_1(k1_tmap_1(A_1367, B_1365, C_1364, D_1366, E_1363, F_1362)) | k2_partfun1(D_1366, B_1365, F_1362, k9_subset_1(A_1367, C_1364, D_1366))!=k2_partfun1(C_1364, B_1365, E_1363, k9_subset_1(A_1367, C_1364, D_1366)) | ~m1_subset_1(F_1362, k1_zfmisc_1(k2_zfmisc_1(D_1366, B_1365))) | ~v1_funct_2(F_1362, D_1366, B_1365) | ~v1_funct_1(F_1362) | ~m1_subset_1(E_1363, k1_zfmisc_1(k2_zfmisc_1(C_1364, B_1365))) | ~v1_funct_2(E_1363, C_1364, B_1365) | ~v1_funct_1(E_1363) | ~m1_subset_1(D_1366, k1_zfmisc_1(A_1367)) | v1_xboole_0(D_1366) | ~m1_subset_1(C_1364, k1_zfmisc_1(A_1367)) | v1_xboole_0(C_1364) | v1_xboole_0(B_1365) | v1_xboole_0(A_1367))), inference(resolution, [status(thm)], [c_42, c_6856])).
% 9.44/3.75  tff(c_7423, plain, (![A_1367, C_1364, E_1363]: (k2_partfun1(k4_subset_1(A_1367, C_1364, '#skF_4'), '#skF_2', k1_tmap_1(A_1367, '#skF_2', C_1364, '#skF_4', E_1363, '#skF_6'), C_1364)=E_1363 | ~v1_funct_1(k1_tmap_1(A_1367, '#skF_2', C_1364, '#skF_4', E_1363, '#skF_6')) | k2_partfun1(C_1364, '#skF_2', E_1363, k9_subset_1(A_1367, C_1364, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_1367, C_1364, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1363, k1_zfmisc_1(k2_zfmisc_1(C_1364, '#skF_2'))) | ~v1_funct_2(E_1363, C_1364, '#skF_2') | ~v1_funct_1(E_1363) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1367)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1364, k1_zfmisc_1(A_1367)) | v1_xboole_0(C_1364) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1367))), inference(resolution, [status(thm)], [c_48, c_7419])).
% 9.44/3.75  tff(c_7429, plain, (![A_1367, C_1364, E_1363]: (k2_partfun1(k4_subset_1(A_1367, C_1364, '#skF_4'), '#skF_2', k1_tmap_1(A_1367, '#skF_2', C_1364, '#skF_4', E_1363, '#skF_6'), C_1364)=E_1363 | ~v1_funct_1(k1_tmap_1(A_1367, '#skF_2', C_1364, '#skF_4', E_1363, '#skF_6')) | k2_partfun1(C_1364, '#skF_2', E_1363, k9_subset_1(A_1367, C_1364, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1367, C_1364, '#skF_4')) | ~m1_subset_1(E_1363, k1_zfmisc_1(k2_zfmisc_1(C_1364, '#skF_2'))) | ~v1_funct_2(E_1363, C_1364, '#skF_2') | ~v1_funct_1(E_1363) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1367)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1364, k1_zfmisc_1(A_1367)) | v1_xboole_0(C_1364) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1367))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_5237, c_7423])).
% 9.44/3.75  tff(c_8503, plain, (![A_1537, C_1538, E_1539]: (k2_partfun1(k4_subset_1(A_1537, C_1538, '#skF_4'), '#skF_2', k1_tmap_1(A_1537, '#skF_2', C_1538, '#skF_4', E_1539, '#skF_6'), C_1538)=E_1539 | ~v1_funct_1(k1_tmap_1(A_1537, '#skF_2', C_1538, '#skF_4', E_1539, '#skF_6')) | k2_partfun1(C_1538, '#skF_2', E_1539, k9_subset_1(A_1537, C_1538, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1537, C_1538, '#skF_4')) | ~m1_subset_1(E_1539, k1_zfmisc_1(k2_zfmisc_1(C_1538, '#skF_2'))) | ~v1_funct_2(E_1539, C_1538, '#skF_2') | ~v1_funct_1(E_1539) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1537)) | ~m1_subset_1(C_1538, k1_zfmisc_1(A_1537)) | v1_xboole_0(C_1538) | v1_xboole_0(A_1537))), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_7429])).
% 9.44/3.75  tff(c_8510, plain, (![A_1537]: (k2_partfun1(k4_subset_1(A_1537, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1537, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1537, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_1537, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1537, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1537)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1537)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1537))), inference(resolution, [status(thm)], [c_54, c_8503])).
% 9.44/3.75  tff(c_8520, plain, (![A_1537]: (k2_partfun1(k4_subset_1(A_1537, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1537, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1537, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1537, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1537, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1537)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1537)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1537))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_5240, c_8510])).
% 9.44/3.75  tff(c_9074, plain, (![A_1662]: (k2_partfun1(k4_subset_1(A_1662, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1662, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1662, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1662, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1662, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1662)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1662)) | v1_xboole_0(A_1662))), inference(negUnitSimplification, [status(thm)], [c_68, c_8520])).
% 9.44/3.75  tff(c_1623, plain, (![A_366, B_367]: (k3_xboole_0(A_366, B_367)=k1_xboole_0 | ~r1_subset_1(A_366, B_367) | v1_xboole_0(B_367) | v1_xboole_0(A_366))), inference(resolution, [status(thm)], [c_1154, c_2])).
% 9.44/3.75  tff(c_1626, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_1623])).
% 9.44/3.75  tff(c_1629, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_68, c_64, c_1626])).
% 9.44/3.75  tff(c_1320, plain, (![A_345, B_346, C_347]: (k9_subset_1(A_345, B_346, C_347)=k3_xboole_0(B_346, C_347) | ~m1_subset_1(C_347, k1_zfmisc_1(A_345)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.44/3.75  tff(c_1331, plain, (![B_346]: (k9_subset_1('#skF_1', B_346, '#skF_4')=k3_xboole_0(B_346, '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_1320])).
% 9.44/3.75  tff(c_1675, plain, (![E_375, C_376, A_379, B_377, F_374, D_378]: (v1_funct_1(k1_tmap_1(A_379, B_377, C_376, D_378, E_375, F_374)) | ~m1_subset_1(F_374, k1_zfmisc_1(k2_zfmisc_1(D_378, B_377))) | ~v1_funct_2(F_374, D_378, B_377) | ~v1_funct_1(F_374) | ~m1_subset_1(E_375, k1_zfmisc_1(k2_zfmisc_1(C_376, B_377))) | ~v1_funct_2(E_375, C_376, B_377) | ~v1_funct_1(E_375) | ~m1_subset_1(D_378, k1_zfmisc_1(A_379)) | v1_xboole_0(D_378) | ~m1_subset_1(C_376, k1_zfmisc_1(A_379)) | v1_xboole_0(C_376) | v1_xboole_0(B_377) | v1_xboole_0(A_379))), inference(cnfTransformation, [status(thm)], [f_173])).
% 9.44/3.75  tff(c_1677, plain, (![A_379, C_376, E_375]: (v1_funct_1(k1_tmap_1(A_379, '#skF_2', C_376, '#skF_4', E_375, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_375, k1_zfmisc_1(k2_zfmisc_1(C_376, '#skF_2'))) | ~v1_funct_2(E_375, C_376, '#skF_2') | ~v1_funct_1(E_375) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_379)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_376, k1_zfmisc_1(A_379)) | v1_xboole_0(C_376) | v1_xboole_0('#skF_2') | v1_xboole_0(A_379))), inference(resolution, [status(thm)], [c_48, c_1675])).
% 9.44/3.75  tff(c_1682, plain, (![A_379, C_376, E_375]: (v1_funct_1(k1_tmap_1(A_379, '#skF_2', C_376, '#skF_4', E_375, '#skF_6')) | ~m1_subset_1(E_375, k1_zfmisc_1(k2_zfmisc_1(C_376, '#skF_2'))) | ~v1_funct_2(E_375, C_376, '#skF_2') | ~v1_funct_1(E_375) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_379)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_376, k1_zfmisc_1(A_379)) | v1_xboole_0(C_376) | v1_xboole_0('#skF_2') | v1_xboole_0(A_379))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1677])).
% 9.44/3.75  tff(c_1851, plain, (![A_385, C_386, E_387]: (v1_funct_1(k1_tmap_1(A_385, '#skF_2', C_386, '#skF_4', E_387, '#skF_6')) | ~m1_subset_1(E_387, k1_zfmisc_1(k2_zfmisc_1(C_386, '#skF_2'))) | ~v1_funct_2(E_387, C_386, '#skF_2') | ~v1_funct_1(E_387) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_385)) | ~m1_subset_1(C_386, k1_zfmisc_1(A_385)) | v1_xboole_0(C_386) | v1_xboole_0(A_385))), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_1682])).
% 9.44/3.75  tff(c_1855, plain, (![A_385]: (v1_funct_1(k1_tmap_1(A_385, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_385)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_385)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_385))), inference(resolution, [status(thm)], [c_54, c_1851])).
% 9.44/3.75  tff(c_1862, plain, (![A_385]: (v1_funct_1(k1_tmap_1(A_385, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_385)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_385)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_385))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_1855])).
% 9.44/3.75  tff(c_1889, plain, (![A_403]: (v1_funct_1(k1_tmap_1(A_403, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_403)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_403)) | v1_xboole_0(A_403))), inference(negUnitSimplification, [status(thm)], [c_68, c_1862])).
% 9.44/3.75  tff(c_1892, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_66, c_1889])).
% 9.44/3.75  tff(c_1895, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1892])).
% 9.44/3.75  tff(c_1896, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_72, c_1895])).
% 9.44/3.75  tff(c_1548, plain, (![A_358, B_359, C_360, D_361]: (k2_partfun1(A_358, B_359, C_360, D_361)=k7_relat_1(C_360, D_361) | ~m1_subset_1(C_360, k1_zfmisc_1(k2_zfmisc_1(A_358, B_359))) | ~v1_funct_1(C_360))), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.44/3.75  tff(c_1552, plain, (![D_361]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_361)=k7_relat_1('#skF_5', D_361) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_1548])).
% 9.44/3.75  tff(c_1558, plain, (![D_361]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_361)=k7_relat_1('#skF_5', D_361))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1552])).
% 9.44/3.75  tff(c_1550, plain, (![D_361]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_361)=k7_relat_1('#skF_6', D_361) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_48, c_1548])).
% 9.44/3.75  tff(c_1555, plain, (![D_361]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_361)=k7_relat_1('#skF_6', D_361))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1550])).
% 9.44/3.75  tff(c_2096, plain, (![E_446, D_444, C_442, B_447, A_445, F_443]: (k2_partfun1(k4_subset_1(A_445, C_442, D_444), B_447, k1_tmap_1(A_445, B_447, C_442, D_444, E_446, F_443), D_444)=F_443 | ~m1_subset_1(k1_tmap_1(A_445, B_447, C_442, D_444, E_446, F_443), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_445, C_442, D_444), B_447))) | ~v1_funct_2(k1_tmap_1(A_445, B_447, C_442, D_444, E_446, F_443), k4_subset_1(A_445, C_442, D_444), B_447) | ~v1_funct_1(k1_tmap_1(A_445, B_447, C_442, D_444, E_446, F_443)) | k2_partfun1(D_444, B_447, F_443, k9_subset_1(A_445, C_442, D_444))!=k2_partfun1(C_442, B_447, E_446, k9_subset_1(A_445, C_442, D_444)) | ~m1_subset_1(F_443, k1_zfmisc_1(k2_zfmisc_1(D_444, B_447))) | ~v1_funct_2(F_443, D_444, B_447) | ~v1_funct_1(F_443) | ~m1_subset_1(E_446, k1_zfmisc_1(k2_zfmisc_1(C_442, B_447))) | ~v1_funct_2(E_446, C_442, B_447) | ~v1_funct_1(E_446) | ~m1_subset_1(D_444, k1_zfmisc_1(A_445)) | v1_xboole_0(D_444) | ~m1_subset_1(C_442, k1_zfmisc_1(A_445)) | v1_xboole_0(C_442) | v1_xboole_0(B_447) | v1_xboole_0(A_445))), inference(cnfTransformation, [status(thm)], [f_139])).
% 9.44/3.75  tff(c_3170, plain, (![E_605, D_608, C_606, F_604, A_609, B_607]: (k2_partfun1(k4_subset_1(A_609, C_606, D_608), B_607, k1_tmap_1(A_609, B_607, C_606, D_608, E_605, F_604), D_608)=F_604 | ~v1_funct_2(k1_tmap_1(A_609, B_607, C_606, D_608, E_605, F_604), k4_subset_1(A_609, C_606, D_608), B_607) | ~v1_funct_1(k1_tmap_1(A_609, B_607, C_606, D_608, E_605, F_604)) | k2_partfun1(D_608, B_607, F_604, k9_subset_1(A_609, C_606, D_608))!=k2_partfun1(C_606, B_607, E_605, k9_subset_1(A_609, C_606, D_608)) | ~m1_subset_1(F_604, k1_zfmisc_1(k2_zfmisc_1(D_608, B_607))) | ~v1_funct_2(F_604, D_608, B_607) | ~v1_funct_1(F_604) | ~m1_subset_1(E_605, k1_zfmisc_1(k2_zfmisc_1(C_606, B_607))) | ~v1_funct_2(E_605, C_606, B_607) | ~v1_funct_1(E_605) | ~m1_subset_1(D_608, k1_zfmisc_1(A_609)) | v1_xboole_0(D_608) | ~m1_subset_1(C_606, k1_zfmisc_1(A_609)) | v1_xboole_0(C_606) | v1_xboole_0(B_607) | v1_xboole_0(A_609))), inference(resolution, [status(thm)], [c_40, c_2096])).
% 9.44/3.75  tff(c_3495, plain, (![F_695, A_700, E_696, D_699, C_697, B_698]: (k2_partfun1(k4_subset_1(A_700, C_697, D_699), B_698, k1_tmap_1(A_700, B_698, C_697, D_699, E_696, F_695), D_699)=F_695 | ~v1_funct_1(k1_tmap_1(A_700, B_698, C_697, D_699, E_696, F_695)) | k2_partfun1(D_699, B_698, F_695, k9_subset_1(A_700, C_697, D_699))!=k2_partfun1(C_697, B_698, E_696, k9_subset_1(A_700, C_697, D_699)) | ~m1_subset_1(F_695, k1_zfmisc_1(k2_zfmisc_1(D_699, B_698))) | ~v1_funct_2(F_695, D_699, B_698) | ~v1_funct_1(F_695) | ~m1_subset_1(E_696, k1_zfmisc_1(k2_zfmisc_1(C_697, B_698))) | ~v1_funct_2(E_696, C_697, B_698) | ~v1_funct_1(E_696) | ~m1_subset_1(D_699, k1_zfmisc_1(A_700)) | v1_xboole_0(D_699) | ~m1_subset_1(C_697, k1_zfmisc_1(A_700)) | v1_xboole_0(C_697) | v1_xboole_0(B_698) | v1_xboole_0(A_700))), inference(resolution, [status(thm)], [c_42, c_3170])).
% 9.44/3.75  tff(c_3499, plain, (![A_700, C_697, E_696]: (k2_partfun1(k4_subset_1(A_700, C_697, '#skF_4'), '#skF_2', k1_tmap_1(A_700, '#skF_2', C_697, '#skF_4', E_696, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_700, '#skF_2', C_697, '#skF_4', E_696, '#skF_6')) | k2_partfun1(C_697, '#skF_2', E_696, k9_subset_1(A_700, C_697, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_700, C_697, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_696, k1_zfmisc_1(k2_zfmisc_1(C_697, '#skF_2'))) | ~v1_funct_2(E_696, C_697, '#skF_2') | ~v1_funct_1(E_696) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_700)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_697, k1_zfmisc_1(A_700)) | v1_xboole_0(C_697) | v1_xboole_0('#skF_2') | v1_xboole_0(A_700))), inference(resolution, [status(thm)], [c_48, c_3495])).
% 9.44/3.75  tff(c_3505, plain, (![A_700, C_697, E_696]: (k2_partfun1(k4_subset_1(A_700, C_697, '#skF_4'), '#skF_2', k1_tmap_1(A_700, '#skF_2', C_697, '#skF_4', E_696, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_700, '#skF_2', C_697, '#skF_4', E_696, '#skF_6')) | k2_partfun1(C_697, '#skF_2', E_696, k9_subset_1(A_700, C_697, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_700, C_697, '#skF_4')) | ~m1_subset_1(E_696, k1_zfmisc_1(k2_zfmisc_1(C_697, '#skF_2'))) | ~v1_funct_2(E_696, C_697, '#skF_2') | ~v1_funct_1(E_696) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_700)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_697, k1_zfmisc_1(A_700)) | v1_xboole_0(C_697) | v1_xboole_0('#skF_2') | v1_xboole_0(A_700))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1555, c_3499])).
% 9.44/3.75  tff(c_4315, plain, (![A_857, C_858, E_859]: (k2_partfun1(k4_subset_1(A_857, C_858, '#skF_4'), '#skF_2', k1_tmap_1(A_857, '#skF_2', C_858, '#skF_4', E_859, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_857, '#skF_2', C_858, '#skF_4', E_859, '#skF_6')) | k2_partfun1(C_858, '#skF_2', E_859, k9_subset_1(A_857, C_858, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_857, C_858, '#skF_4')) | ~m1_subset_1(E_859, k1_zfmisc_1(k2_zfmisc_1(C_858, '#skF_2'))) | ~v1_funct_2(E_859, C_858, '#skF_2') | ~v1_funct_1(E_859) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_857)) | ~m1_subset_1(C_858, k1_zfmisc_1(A_857)) | v1_xboole_0(C_858) | v1_xboole_0(A_857))), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_3505])).
% 9.44/3.75  tff(c_4322, plain, (![A_857]: (k2_partfun1(k4_subset_1(A_857, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_857, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_857, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_857, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_857, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_857)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_857)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_857))), inference(resolution, [status(thm)], [c_54, c_4315])).
% 9.44/3.75  tff(c_4332, plain, (![A_857]: (k2_partfun1(k4_subset_1(A_857, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_857, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_857, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_857, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_857, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_857)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_857)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_857))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_1558, c_4322])).
% 9.44/3.75  tff(c_4759, plain, (![A_933]: (k2_partfun1(k4_subset_1(A_933, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_933, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_933, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_933, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_933, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_933)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_933)) | v1_xboole_0(A_933))), inference(negUnitSimplification, [status(thm)], [c_68, c_4332])).
% 9.44/3.75  tff(c_113, plain, (![C_230, A_231, B_232]: (v1_relat_1(C_230) | ~m1_subset_1(C_230, k1_zfmisc_1(k2_zfmisc_1(A_231, B_232))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.44/3.75  tff(c_120, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_48, c_113])).
% 9.44/3.75  tff(c_108, plain, (![A_228, B_229]: (v1_xboole_0(k7_relat_1(A_228, B_229)) | ~v1_xboole_0(B_229) | ~v1_relat_1(A_228))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.44/3.75  tff(c_122, plain, (![A_233, B_234]: (k7_relat_1(A_233, B_234)=k1_xboole_0 | ~v1_xboole_0(B_234) | ~v1_relat_1(A_233))), inference(resolution, [status(thm)], [c_108, c_8])).
% 9.44/3.75  tff(c_129, plain, (![A_235]: (k7_relat_1(A_235, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_235))), inference(resolution, [status(thm)], [c_6, c_122])).
% 9.44/3.75  tff(c_140, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_120, c_129])).
% 9.44/3.75  tff(c_252, plain, (![A_246, B_247]: (r1_xboole_0(A_246, B_247) | ~r1_subset_1(A_246, B_247) | v1_xboole_0(B_247) | v1_xboole_0(A_246))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.44/3.75  tff(c_734, plain, (![A_289, B_290]: (k3_xboole_0(A_289, B_290)=k1_xboole_0 | ~r1_subset_1(A_289, B_290) | v1_xboole_0(B_290) | v1_xboole_0(A_289))), inference(resolution, [status(thm)], [c_252, c_2])).
% 9.44/3.75  tff(c_737, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_734])).
% 9.44/3.75  tff(c_740, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_68, c_64, c_737])).
% 9.44/3.75  tff(c_121, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_113])).
% 9.44/3.75  tff(c_139, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_121, c_129])).
% 9.44/3.75  tff(c_455, plain, (![A_262, B_263, C_264, D_265]: (k2_partfun1(A_262, B_263, C_264, D_265)=k7_relat_1(C_264, D_265) | ~m1_subset_1(C_264, k1_zfmisc_1(k2_zfmisc_1(A_262, B_263))) | ~v1_funct_1(C_264))), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.44/3.75  tff(c_459, plain, (![D_265]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_265)=k7_relat_1('#skF_5', D_265) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_455])).
% 9.44/3.75  tff(c_465, plain, (![D_265]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_265)=k7_relat_1('#skF_5', D_265))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_459])).
% 9.44/3.75  tff(c_457, plain, (![D_265]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_265)=k7_relat_1('#skF_6', D_265) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_48, c_455])).
% 9.44/3.75  tff(c_462, plain, (![D_265]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_265)=k7_relat_1('#skF_6', D_265))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_457])).
% 9.44/3.75  tff(c_315, plain, (![A_250, B_251, C_252]: (k9_subset_1(A_250, B_251, C_252)=k3_xboole_0(B_251, C_252) | ~m1_subset_1(C_252, k1_zfmisc_1(A_250)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.44/3.75  tff(c_326, plain, (![B_251]: (k9_subset_1('#skF_1', B_251, '#skF_4')=k3_xboole_0(B_251, '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_315])).
% 9.44/3.75  tff(c_46, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_215])).
% 9.44/3.75  tff(c_105, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_46])).
% 9.44/3.75  tff(c_328, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_326, c_326, c_105])).
% 9.44/3.75  tff(c_1001, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_140, c_740, c_139, c_740, c_465, c_462, c_328])).
% 9.44/3.75  tff(c_1002, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_46])).
% 9.44/3.75  tff(c_1217, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_1002])).
% 9.44/3.75  tff(c_4770, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4759, c_1217])).
% 9.44/3.75  tff(c_4784, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_1041, c_1042, c_1629, c_1331, c_1629, c_1331, c_1896, c_4770])).
% 9.44/3.75  tff(c_4786, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_4784])).
% 9.44/3.75  tff(c_4787, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_1002])).
% 9.44/3.75  tff(c_9083, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_9074, c_4787])).
% 9.44/3.75  tff(c_9094, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_1041, c_1042, c_5175, c_4902, c_5175, c_4902, c_5800, c_9083])).
% 9.44/3.75  tff(c_9096, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_9094])).
% 9.44/3.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.44/3.75  
% 9.44/3.75  Inference rules
% 9.44/3.75  ----------------------
% 9.44/3.75  #Ref     : 0
% 9.44/3.75  #Sup     : 1909
% 9.44/3.75  #Fact    : 0
% 9.44/3.75  #Define  : 0
% 9.44/3.75  #Split   : 64
% 9.44/3.75  #Chain   : 0
% 9.44/3.75  #Close   : 0
% 9.44/3.75  
% 9.44/3.75  Ordering : KBO
% 9.44/3.75  
% 9.44/3.75  Simplification rules
% 9.44/3.75  ----------------------
% 9.44/3.75  #Subsume      : 1231
% 9.44/3.75  #Demod        : 1662
% 9.44/3.75  #Tautology    : 519
% 9.44/3.75  #SimpNegUnit  : 681
% 9.44/3.75  #BackRed      : 332
% 9.44/3.75  
% 9.44/3.75  #Partial instantiations: 0
% 9.44/3.75  #Strategies tried      : 1
% 9.44/3.75  
% 9.44/3.76  Timing (in seconds)
% 9.44/3.76  ----------------------
% 9.44/3.76  Preprocessing        : 0.40
% 9.44/3.76  Parsing              : 0.19
% 9.44/3.76  CNF conversion       : 0.06
% 9.44/3.76  Main loop            : 2.47
% 9.44/3.76  Inferencing          : 0.71
% 9.44/3.76  Reduction            : 0.77
% 9.44/3.76  Demodulation         : 0.54
% 9.44/3.76  BG Simplification    : 0.06
% 9.44/3.76  Subsumption          : 0.80
% 9.44/3.76  Abstraction          : 0.09
% 9.44/3.76  MUC search           : 0.00
% 9.44/3.76  Cooper               : 0.00
% 9.44/3.76  Total                : 2.92
% 9.44/3.76  Index Insertion      : 0.00
% 9.44/3.76  Index Deletion       : 0.00
% 9.44/3.76  Index Matching       : 0.00
% 9.44/3.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
