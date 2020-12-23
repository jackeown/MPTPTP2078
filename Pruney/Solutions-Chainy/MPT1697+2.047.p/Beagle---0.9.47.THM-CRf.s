%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:16 EST 2020

% Result     : Theorem 8.78s
% Output     : CNFRefutation 8.78s
% Verified   : 
% Statistics : Number of formulae       :  195 ( 532 expanded)
%              Number of leaves         :   46 ( 213 expanded)
%              Depth                    :   12
%              Number of atoms          :  649 (2717 expanded)
%              Number of equality atoms :  122 ( 489 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(f_240,negated_conjecture,(
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

tff(f_55,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_53,axiom,(
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

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_198,axiom,(
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

tff(f_116,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_164,axiom,(
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

tff(c_82,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_76,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_72,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_16,plain,(
    ! [A_12] : k3_xboole_0(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_xboole_0(A_5,B_6)
      | k3_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_466,plain,(
    ! [A_323,B_324,C_325] :
      ( ~ r1_xboole_0(A_323,B_324)
      | ~ r2_hidden(C_325,B_324)
      | ~ r2_hidden(C_325,A_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3691,plain,(
    ! [C_795,B_796,A_797] :
      ( ~ r2_hidden(C_795,B_796)
      | ~ r2_hidden(C_795,A_797)
      | k3_xboole_0(A_797,B_796) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_466])).

tff(c_3705,plain,(
    ! [A_798,A_799] :
      ( ~ r2_hidden('#skF_1'(A_798),A_799)
      | k3_xboole_0(A_799,A_798) != k1_xboole_0
      | v1_xboole_0(A_798) ) ),
    inference(resolution,[status(thm)],[c_4,c_3691])).

tff(c_3710,plain,(
    ! [A_800] :
      ( k3_xboole_0(A_800,A_800) != k1_xboole_0
      | v1_xboole_0(A_800) ) ),
    inference(resolution,[status(thm)],[c_4,c_3705])).

tff(c_3714,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_3710])).

tff(c_58,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_422,plain,(
    ! [C_305,A_306,B_307] :
      ( v1_relat_1(C_305)
      | ~ m1_subset_1(C_305,k1_zfmisc_1(k2_zfmisc_1(A_306,B_307))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_429,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_422])).

tff(c_431,plain,(
    ! [A_308,B_309] :
      ( r2_hidden('#skF_2'(A_308,B_309),A_308)
      | r1_xboole_0(A_308,B_309) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_435,plain,(
    ! [A_308,B_309] :
      ( ~ v1_xboole_0(A_308)
      | r1_xboole_0(A_308,B_309) ) ),
    inference(resolution,[status(thm)],[c_431,c_2])).

tff(c_3647,plain,(
    ! [A_784,B_785] :
      ( k7_relat_1(A_784,B_785) = k1_xboole_0
      | ~ r1_xboole_0(B_785,k1_relat_1(A_784))
      | ~ v1_relat_1(A_784) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_3663,plain,(
    ! [A_786,A_787] :
      ( k7_relat_1(A_786,A_787) = k1_xboole_0
      | ~ v1_relat_1(A_786)
      | ~ v1_xboole_0(A_787) ) ),
    inference(resolution,[status(thm)],[c_435,c_3647])).

tff(c_3669,plain,(
    ! [A_787] :
      ( k7_relat_1('#skF_8',A_787) = k1_xboole_0
      | ~ v1_xboole_0(A_787) ) ),
    inference(resolution,[status(thm)],[c_429,c_3663])).

tff(c_3725,plain,(
    k7_relat_1('#skF_8',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3714,c_3669])).

tff(c_64,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_430,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_422])).

tff(c_3668,plain,(
    ! [A_787] :
      ( k7_relat_1('#skF_7',A_787) = k1_xboole_0
      | ~ v1_xboole_0(A_787) ) ),
    inference(resolution,[status(thm)],[c_430,c_3663])).

tff(c_3726,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3714,c_3668])).

tff(c_78,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_70,plain,(
    r1_subset_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_3674,plain,(
    ! [A_793,B_794] :
      ( r1_xboole_0(A_793,B_794)
      | ~ r1_subset_1(A_793,B_794)
      | v1_xboole_0(B_794)
      | v1_xboole_0(A_793) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4557,plain,(
    ! [A_902,B_903] :
      ( k3_xboole_0(A_902,B_903) = k1_xboole_0
      | ~ r1_subset_1(A_902,B_903)
      | v1_xboole_0(B_903)
      | v1_xboole_0(A_902) ) ),
    inference(resolution,[status(thm)],[c_3674,c_6])).

tff(c_4560,plain,
    ( k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0
    | v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_4557])).

tff(c_4563,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_74,c_4560])).

tff(c_4506,plain,(
    ! [A_894,B_895,C_896] :
      ( k9_subset_1(A_894,B_895,C_896) = k3_xboole_0(B_895,C_896)
      | ~ m1_subset_1(C_896,k1_zfmisc_1(A_894)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4517,plain,(
    ! [B_895] : k9_subset_1('#skF_3',B_895,'#skF_6') = k3_xboole_0(B_895,'#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_4506])).

tff(c_68,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_66,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_80,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_62,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_60,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_4883,plain,(
    ! [E_942,C_941,A_943,F_939,B_938,D_940] :
      ( v1_funct_1(k1_tmap_1(A_943,B_938,C_941,D_940,E_942,F_939))
      | ~ m1_subset_1(F_939,k1_zfmisc_1(k2_zfmisc_1(D_940,B_938)))
      | ~ v1_funct_2(F_939,D_940,B_938)
      | ~ v1_funct_1(F_939)
      | ~ m1_subset_1(E_942,k1_zfmisc_1(k2_zfmisc_1(C_941,B_938)))
      | ~ v1_funct_2(E_942,C_941,B_938)
      | ~ v1_funct_1(E_942)
      | ~ m1_subset_1(D_940,k1_zfmisc_1(A_943))
      | v1_xboole_0(D_940)
      | ~ m1_subset_1(C_941,k1_zfmisc_1(A_943))
      | v1_xboole_0(C_941)
      | v1_xboole_0(B_938)
      | v1_xboole_0(A_943) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_4885,plain,(
    ! [A_943,C_941,E_942] :
      ( v1_funct_1(k1_tmap_1(A_943,'#skF_4',C_941,'#skF_6',E_942,'#skF_8'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_942,k1_zfmisc_1(k2_zfmisc_1(C_941,'#skF_4')))
      | ~ v1_funct_2(E_942,C_941,'#skF_4')
      | ~ v1_funct_1(E_942)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_943))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_941,k1_zfmisc_1(A_943))
      | v1_xboole_0(C_941)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_943) ) ),
    inference(resolution,[status(thm)],[c_58,c_4883])).

tff(c_4890,plain,(
    ! [A_943,C_941,E_942] :
      ( v1_funct_1(k1_tmap_1(A_943,'#skF_4',C_941,'#skF_6',E_942,'#skF_8'))
      | ~ m1_subset_1(E_942,k1_zfmisc_1(k2_zfmisc_1(C_941,'#skF_4')))
      | ~ v1_funct_2(E_942,C_941,'#skF_4')
      | ~ v1_funct_1(E_942)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_943))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_941,k1_zfmisc_1(A_943))
      | v1_xboole_0(C_941)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_943) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_4885])).

tff(c_4911,plain,(
    ! [A_949,C_950,E_951] :
      ( v1_funct_1(k1_tmap_1(A_949,'#skF_4',C_950,'#skF_6',E_951,'#skF_8'))
      | ~ m1_subset_1(E_951,k1_zfmisc_1(k2_zfmisc_1(C_950,'#skF_4')))
      | ~ v1_funct_2(E_951,C_950,'#skF_4')
      | ~ v1_funct_1(E_951)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_949))
      | ~ m1_subset_1(C_950,k1_zfmisc_1(A_949))
      | v1_xboole_0(C_950)
      | v1_xboole_0(A_949) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_4890])).

tff(c_4915,plain,(
    ! [A_949] :
      ( v1_funct_1(k1_tmap_1(A_949,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_949))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_949))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_949) ) ),
    inference(resolution,[status(thm)],[c_64,c_4911])).

tff(c_4922,plain,(
    ! [A_949] :
      ( v1_funct_1(k1_tmap_1(A_949,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_949))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_949))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_949) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_4915])).

tff(c_5309,plain,(
    ! [A_1021] :
      ( v1_funct_1(k1_tmap_1(A_1021,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1021))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1021))
      | v1_xboole_0(A_1021) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4922])).

tff(c_5312,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_5309])).

tff(c_5315,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_5312])).

tff(c_5316,plain,(
    v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_5315])).

tff(c_4595,plain,(
    ! [A_907,B_908,C_909,D_910] :
      ( k2_partfun1(A_907,B_908,C_909,D_910) = k7_relat_1(C_909,D_910)
      | ~ m1_subset_1(C_909,k1_zfmisc_1(k2_zfmisc_1(A_907,B_908)))
      | ~ v1_funct_1(C_909) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_4599,plain,(
    ! [D_910] :
      ( k2_partfun1('#skF_5','#skF_4','#skF_7',D_910) = k7_relat_1('#skF_7',D_910)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_64,c_4595])).

tff(c_4605,plain,(
    ! [D_910] : k2_partfun1('#skF_5','#skF_4','#skF_7',D_910) = k7_relat_1('#skF_7',D_910) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_4599])).

tff(c_4597,plain,(
    ! [D_910] :
      ( k2_partfun1('#skF_6','#skF_4','#skF_8',D_910) = k7_relat_1('#skF_8',D_910)
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_58,c_4595])).

tff(c_4602,plain,(
    ! [D_910] : k2_partfun1('#skF_6','#skF_4','#skF_8',D_910) = k7_relat_1('#skF_8',D_910) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_4597])).

tff(c_52,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_50,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_5264,plain,(
    ! [D_1008,E_1009,B_1012,F_1010,A_1007,C_1011] :
      ( k2_partfun1(k4_subset_1(A_1007,C_1011,D_1008),B_1012,k1_tmap_1(A_1007,B_1012,C_1011,D_1008,E_1009,F_1010),C_1011) = E_1009
      | ~ m1_subset_1(k1_tmap_1(A_1007,B_1012,C_1011,D_1008,E_1009,F_1010),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1007,C_1011,D_1008),B_1012)))
      | ~ v1_funct_2(k1_tmap_1(A_1007,B_1012,C_1011,D_1008,E_1009,F_1010),k4_subset_1(A_1007,C_1011,D_1008),B_1012)
      | ~ v1_funct_1(k1_tmap_1(A_1007,B_1012,C_1011,D_1008,E_1009,F_1010))
      | k2_partfun1(D_1008,B_1012,F_1010,k9_subset_1(A_1007,C_1011,D_1008)) != k2_partfun1(C_1011,B_1012,E_1009,k9_subset_1(A_1007,C_1011,D_1008))
      | ~ m1_subset_1(F_1010,k1_zfmisc_1(k2_zfmisc_1(D_1008,B_1012)))
      | ~ v1_funct_2(F_1010,D_1008,B_1012)
      | ~ v1_funct_1(F_1010)
      | ~ m1_subset_1(E_1009,k1_zfmisc_1(k2_zfmisc_1(C_1011,B_1012)))
      | ~ v1_funct_2(E_1009,C_1011,B_1012)
      | ~ v1_funct_1(E_1009)
      | ~ m1_subset_1(D_1008,k1_zfmisc_1(A_1007))
      | v1_xboole_0(D_1008)
      | ~ m1_subset_1(C_1011,k1_zfmisc_1(A_1007))
      | v1_xboole_0(C_1011)
      | v1_xboole_0(B_1012)
      | v1_xboole_0(A_1007) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_5976,plain,(
    ! [B_1140,D_1142,A_1145,C_1143,F_1141,E_1144] :
      ( k2_partfun1(k4_subset_1(A_1145,C_1143,D_1142),B_1140,k1_tmap_1(A_1145,B_1140,C_1143,D_1142,E_1144,F_1141),C_1143) = E_1144
      | ~ v1_funct_2(k1_tmap_1(A_1145,B_1140,C_1143,D_1142,E_1144,F_1141),k4_subset_1(A_1145,C_1143,D_1142),B_1140)
      | ~ v1_funct_1(k1_tmap_1(A_1145,B_1140,C_1143,D_1142,E_1144,F_1141))
      | k2_partfun1(D_1142,B_1140,F_1141,k9_subset_1(A_1145,C_1143,D_1142)) != k2_partfun1(C_1143,B_1140,E_1144,k9_subset_1(A_1145,C_1143,D_1142))
      | ~ m1_subset_1(F_1141,k1_zfmisc_1(k2_zfmisc_1(D_1142,B_1140)))
      | ~ v1_funct_2(F_1141,D_1142,B_1140)
      | ~ v1_funct_1(F_1141)
      | ~ m1_subset_1(E_1144,k1_zfmisc_1(k2_zfmisc_1(C_1143,B_1140)))
      | ~ v1_funct_2(E_1144,C_1143,B_1140)
      | ~ v1_funct_1(E_1144)
      | ~ m1_subset_1(D_1142,k1_zfmisc_1(A_1145))
      | v1_xboole_0(D_1142)
      | ~ m1_subset_1(C_1143,k1_zfmisc_1(A_1145))
      | v1_xboole_0(C_1143)
      | v1_xboole_0(B_1140)
      | v1_xboole_0(A_1145) ) ),
    inference(resolution,[status(thm)],[c_50,c_5264])).

tff(c_6503,plain,(
    ! [D_1202,C_1203,B_1200,F_1201,E_1204,A_1205] :
      ( k2_partfun1(k4_subset_1(A_1205,C_1203,D_1202),B_1200,k1_tmap_1(A_1205,B_1200,C_1203,D_1202,E_1204,F_1201),C_1203) = E_1204
      | ~ v1_funct_1(k1_tmap_1(A_1205,B_1200,C_1203,D_1202,E_1204,F_1201))
      | k2_partfun1(D_1202,B_1200,F_1201,k9_subset_1(A_1205,C_1203,D_1202)) != k2_partfun1(C_1203,B_1200,E_1204,k9_subset_1(A_1205,C_1203,D_1202))
      | ~ m1_subset_1(F_1201,k1_zfmisc_1(k2_zfmisc_1(D_1202,B_1200)))
      | ~ v1_funct_2(F_1201,D_1202,B_1200)
      | ~ v1_funct_1(F_1201)
      | ~ m1_subset_1(E_1204,k1_zfmisc_1(k2_zfmisc_1(C_1203,B_1200)))
      | ~ v1_funct_2(E_1204,C_1203,B_1200)
      | ~ v1_funct_1(E_1204)
      | ~ m1_subset_1(D_1202,k1_zfmisc_1(A_1205))
      | v1_xboole_0(D_1202)
      | ~ m1_subset_1(C_1203,k1_zfmisc_1(A_1205))
      | v1_xboole_0(C_1203)
      | v1_xboole_0(B_1200)
      | v1_xboole_0(A_1205) ) ),
    inference(resolution,[status(thm)],[c_52,c_5976])).

tff(c_6507,plain,(
    ! [A_1205,C_1203,E_1204] :
      ( k2_partfun1(k4_subset_1(A_1205,C_1203,'#skF_6'),'#skF_4',k1_tmap_1(A_1205,'#skF_4',C_1203,'#skF_6',E_1204,'#skF_8'),C_1203) = E_1204
      | ~ v1_funct_1(k1_tmap_1(A_1205,'#skF_4',C_1203,'#skF_6',E_1204,'#skF_8'))
      | k2_partfun1(C_1203,'#skF_4',E_1204,k9_subset_1(A_1205,C_1203,'#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1(A_1205,C_1203,'#skF_6'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_1204,k1_zfmisc_1(k2_zfmisc_1(C_1203,'#skF_4')))
      | ~ v1_funct_2(E_1204,C_1203,'#skF_4')
      | ~ v1_funct_1(E_1204)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1205))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_1203,k1_zfmisc_1(A_1205))
      | v1_xboole_0(C_1203)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1205) ) ),
    inference(resolution,[status(thm)],[c_58,c_6503])).

tff(c_6513,plain,(
    ! [A_1205,C_1203,E_1204] :
      ( k2_partfun1(k4_subset_1(A_1205,C_1203,'#skF_6'),'#skF_4',k1_tmap_1(A_1205,'#skF_4',C_1203,'#skF_6',E_1204,'#skF_8'),C_1203) = E_1204
      | ~ v1_funct_1(k1_tmap_1(A_1205,'#skF_4',C_1203,'#skF_6',E_1204,'#skF_8'))
      | k2_partfun1(C_1203,'#skF_4',E_1204,k9_subset_1(A_1205,C_1203,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_1205,C_1203,'#skF_6'))
      | ~ m1_subset_1(E_1204,k1_zfmisc_1(k2_zfmisc_1(C_1203,'#skF_4')))
      | ~ v1_funct_2(E_1204,C_1203,'#skF_4')
      | ~ v1_funct_1(E_1204)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1205))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_1203,k1_zfmisc_1(A_1205))
      | v1_xboole_0(C_1203)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1205) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_4602,c_6507])).

tff(c_6683,plain,(
    ! [A_1234,C_1235,E_1236] :
      ( k2_partfun1(k4_subset_1(A_1234,C_1235,'#skF_6'),'#skF_4',k1_tmap_1(A_1234,'#skF_4',C_1235,'#skF_6',E_1236,'#skF_8'),C_1235) = E_1236
      | ~ v1_funct_1(k1_tmap_1(A_1234,'#skF_4',C_1235,'#skF_6',E_1236,'#skF_8'))
      | k2_partfun1(C_1235,'#skF_4',E_1236,k9_subset_1(A_1234,C_1235,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_1234,C_1235,'#skF_6'))
      | ~ m1_subset_1(E_1236,k1_zfmisc_1(k2_zfmisc_1(C_1235,'#skF_4')))
      | ~ v1_funct_2(E_1236,C_1235,'#skF_4')
      | ~ v1_funct_1(E_1236)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1234))
      | ~ m1_subset_1(C_1235,k1_zfmisc_1(A_1234))
      | v1_xboole_0(C_1235)
      | v1_xboole_0(A_1234) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_6513])).

tff(c_6690,plain,(
    ! [A_1234] :
      ( k2_partfun1(k4_subset_1(A_1234,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_1234,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1234,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1(A_1234,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_1234,'#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1234))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1234))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_1234) ) ),
    inference(resolution,[status(thm)],[c_64,c_6683])).

tff(c_6700,plain,(
    ! [A_1234] :
      ( k2_partfun1(k4_subset_1(A_1234,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_1234,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1234,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_1234,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_1234,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1234))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1234))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_1234) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_4605,c_6690])).

tff(c_7032,plain,(
    ! [A_1272] :
      ( k2_partfun1(k4_subset_1(A_1272,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_1272,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1272,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_1272,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_1272,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1272))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1272))
      | v1_xboole_0(A_1272) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_6700])).

tff(c_543,plain,(
    ! [C_342,B_343,A_344] :
      ( ~ r2_hidden(C_342,B_343)
      | ~ r2_hidden(C_342,A_344)
      | k3_xboole_0(A_344,B_343) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_466])).

tff(c_553,plain,(
    ! [A_345,A_346] :
      ( ~ r2_hidden('#skF_1'(A_345),A_346)
      | k3_xboole_0(A_346,A_345) != k1_xboole_0
      | v1_xboole_0(A_345) ) ),
    inference(resolution,[status(thm)],[c_4,c_543])).

tff(c_558,plain,(
    ! [A_347] :
      ( k3_xboole_0(A_347,A_347) != k1_xboole_0
      | v1_xboole_0(A_347) ) ),
    inference(resolution,[status(thm)],[c_4,c_553])).

tff(c_562,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_558])).

tff(c_499,plain,(
    ! [A_331,B_332] :
      ( k7_relat_1(A_331,B_332) = k1_xboole_0
      | ~ r1_xboole_0(B_332,k1_relat_1(A_331))
      | ~ v1_relat_1(A_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_515,plain,(
    ! [A_333,A_334] :
      ( k7_relat_1(A_333,A_334) = k1_xboole_0
      | ~ v1_relat_1(A_333)
      | ~ v1_xboole_0(A_334) ) ),
    inference(resolution,[status(thm)],[c_435,c_499])).

tff(c_521,plain,(
    ! [A_334] :
      ( k7_relat_1('#skF_8',A_334) = k1_xboole_0
      | ~ v1_xboole_0(A_334) ) ),
    inference(resolution,[status(thm)],[c_429,c_515])).

tff(c_573,plain,(
    k7_relat_1('#skF_8',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_562,c_521])).

tff(c_520,plain,(
    ! [A_334] :
      ( k7_relat_1('#skF_7',A_334) = k1_xboole_0
      | ~ v1_xboole_0(A_334) ) ),
    inference(resolution,[status(thm)],[c_430,c_515])).

tff(c_574,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_562,c_520])).

tff(c_526,plain,(
    ! [A_340,B_341] :
      ( r1_xboole_0(A_340,B_341)
      | ~ r1_subset_1(A_340,B_341)
      | v1_xboole_0(B_341)
      | v1_xboole_0(A_340) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1337,plain,(
    ! [A_437,B_438] :
      ( k3_xboole_0(A_437,B_438) = k1_xboole_0
      | ~ r1_subset_1(A_437,B_438)
      | v1_xboole_0(B_438)
      | v1_xboole_0(A_437) ) ),
    inference(resolution,[status(thm)],[c_526,c_6])).

tff(c_1340,plain,
    ( k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0
    | v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_1337])).

tff(c_1343,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_74,c_1340])).

tff(c_1286,plain,(
    ! [A_429,B_430,C_431] :
      ( k9_subset_1(A_429,B_430,C_431) = k3_xboole_0(B_430,C_431)
      | ~ m1_subset_1(C_431,k1_zfmisc_1(A_429)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1297,plain,(
    ! [B_430] : k9_subset_1('#skF_3',B_430,'#skF_6') = k3_xboole_0(B_430,'#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_1286])).

tff(c_1663,plain,(
    ! [C_476,B_473,D_475,F_474,E_477,A_478] :
      ( v1_funct_1(k1_tmap_1(A_478,B_473,C_476,D_475,E_477,F_474))
      | ~ m1_subset_1(F_474,k1_zfmisc_1(k2_zfmisc_1(D_475,B_473)))
      | ~ v1_funct_2(F_474,D_475,B_473)
      | ~ v1_funct_1(F_474)
      | ~ m1_subset_1(E_477,k1_zfmisc_1(k2_zfmisc_1(C_476,B_473)))
      | ~ v1_funct_2(E_477,C_476,B_473)
      | ~ v1_funct_1(E_477)
      | ~ m1_subset_1(D_475,k1_zfmisc_1(A_478))
      | v1_xboole_0(D_475)
      | ~ m1_subset_1(C_476,k1_zfmisc_1(A_478))
      | v1_xboole_0(C_476)
      | v1_xboole_0(B_473)
      | v1_xboole_0(A_478) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_1665,plain,(
    ! [A_478,C_476,E_477] :
      ( v1_funct_1(k1_tmap_1(A_478,'#skF_4',C_476,'#skF_6',E_477,'#skF_8'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_477,k1_zfmisc_1(k2_zfmisc_1(C_476,'#skF_4')))
      | ~ v1_funct_2(E_477,C_476,'#skF_4')
      | ~ v1_funct_1(E_477)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_478))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_476,k1_zfmisc_1(A_478))
      | v1_xboole_0(C_476)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_478) ) ),
    inference(resolution,[status(thm)],[c_58,c_1663])).

tff(c_1670,plain,(
    ! [A_478,C_476,E_477] :
      ( v1_funct_1(k1_tmap_1(A_478,'#skF_4',C_476,'#skF_6',E_477,'#skF_8'))
      | ~ m1_subset_1(E_477,k1_zfmisc_1(k2_zfmisc_1(C_476,'#skF_4')))
      | ~ v1_funct_2(E_477,C_476,'#skF_4')
      | ~ v1_funct_1(E_477)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_478))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_476,k1_zfmisc_1(A_478))
      | v1_xboole_0(C_476)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_478) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1665])).

tff(c_1691,plain,(
    ! [A_484,C_485,E_486] :
      ( v1_funct_1(k1_tmap_1(A_484,'#skF_4',C_485,'#skF_6',E_486,'#skF_8'))
      | ~ m1_subset_1(E_486,k1_zfmisc_1(k2_zfmisc_1(C_485,'#skF_4')))
      | ~ v1_funct_2(E_486,C_485,'#skF_4')
      | ~ v1_funct_1(E_486)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_484))
      | ~ m1_subset_1(C_485,k1_zfmisc_1(A_484))
      | v1_xboole_0(C_485)
      | v1_xboole_0(A_484) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_1670])).

tff(c_1695,plain,(
    ! [A_484] :
      ( v1_funct_1(k1_tmap_1(A_484,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_484))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_484))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_484) ) ),
    inference(resolution,[status(thm)],[c_64,c_1691])).

tff(c_1702,plain,(
    ! [A_484] :
      ( v1_funct_1(k1_tmap_1(A_484,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_484))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_484))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_484) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_1695])).

tff(c_2089,plain,(
    ! [A_556] :
      ( v1_funct_1(k1_tmap_1(A_556,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_556))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_556))
      | v1_xboole_0(A_556) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1702])).

tff(c_2092,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_2089])).

tff(c_2095,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2092])).

tff(c_2096,plain,(
    v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_2095])).

tff(c_1381,plain,(
    ! [A_443,B_444,C_445,D_446] :
      ( k2_partfun1(A_443,B_444,C_445,D_446) = k7_relat_1(C_445,D_446)
      | ~ m1_subset_1(C_445,k1_zfmisc_1(k2_zfmisc_1(A_443,B_444)))
      | ~ v1_funct_1(C_445) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1385,plain,(
    ! [D_446] :
      ( k2_partfun1('#skF_5','#skF_4','#skF_7',D_446) = k7_relat_1('#skF_7',D_446)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_64,c_1381])).

tff(c_1391,plain,(
    ! [D_446] : k2_partfun1('#skF_5','#skF_4','#skF_7',D_446) = k7_relat_1('#skF_7',D_446) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1385])).

tff(c_1383,plain,(
    ! [D_446] :
      ( k2_partfun1('#skF_6','#skF_4','#skF_8',D_446) = k7_relat_1('#skF_8',D_446)
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_58,c_1381])).

tff(c_1388,plain,(
    ! [D_446] : k2_partfun1('#skF_6','#skF_4','#skF_8',D_446) = k7_relat_1('#skF_8',D_446) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1383])).

tff(c_2131,plain,(
    ! [E_564,A_562,F_565,D_563,C_566,B_567] :
      ( k2_partfun1(k4_subset_1(A_562,C_566,D_563),B_567,k1_tmap_1(A_562,B_567,C_566,D_563,E_564,F_565),D_563) = F_565
      | ~ m1_subset_1(k1_tmap_1(A_562,B_567,C_566,D_563,E_564,F_565),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_562,C_566,D_563),B_567)))
      | ~ v1_funct_2(k1_tmap_1(A_562,B_567,C_566,D_563,E_564,F_565),k4_subset_1(A_562,C_566,D_563),B_567)
      | ~ v1_funct_1(k1_tmap_1(A_562,B_567,C_566,D_563,E_564,F_565))
      | k2_partfun1(D_563,B_567,F_565,k9_subset_1(A_562,C_566,D_563)) != k2_partfun1(C_566,B_567,E_564,k9_subset_1(A_562,C_566,D_563))
      | ~ m1_subset_1(F_565,k1_zfmisc_1(k2_zfmisc_1(D_563,B_567)))
      | ~ v1_funct_2(F_565,D_563,B_567)
      | ~ v1_funct_1(F_565)
      | ~ m1_subset_1(E_564,k1_zfmisc_1(k2_zfmisc_1(C_566,B_567)))
      | ~ v1_funct_2(E_564,C_566,B_567)
      | ~ v1_funct_1(E_564)
      | ~ m1_subset_1(D_563,k1_zfmisc_1(A_562))
      | v1_xboole_0(D_563)
      | ~ m1_subset_1(C_566,k1_zfmisc_1(A_562))
      | v1_xboole_0(C_566)
      | v1_xboole_0(B_567)
      | v1_xboole_0(A_562) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_2859,plain,(
    ! [E_688,A_689,B_684,D_686,F_685,C_687] :
      ( k2_partfun1(k4_subset_1(A_689,C_687,D_686),B_684,k1_tmap_1(A_689,B_684,C_687,D_686,E_688,F_685),D_686) = F_685
      | ~ v1_funct_2(k1_tmap_1(A_689,B_684,C_687,D_686,E_688,F_685),k4_subset_1(A_689,C_687,D_686),B_684)
      | ~ v1_funct_1(k1_tmap_1(A_689,B_684,C_687,D_686,E_688,F_685))
      | k2_partfun1(D_686,B_684,F_685,k9_subset_1(A_689,C_687,D_686)) != k2_partfun1(C_687,B_684,E_688,k9_subset_1(A_689,C_687,D_686))
      | ~ m1_subset_1(F_685,k1_zfmisc_1(k2_zfmisc_1(D_686,B_684)))
      | ~ v1_funct_2(F_685,D_686,B_684)
      | ~ v1_funct_1(F_685)
      | ~ m1_subset_1(E_688,k1_zfmisc_1(k2_zfmisc_1(C_687,B_684)))
      | ~ v1_funct_2(E_688,C_687,B_684)
      | ~ v1_funct_1(E_688)
      | ~ m1_subset_1(D_686,k1_zfmisc_1(A_689))
      | v1_xboole_0(D_686)
      | ~ m1_subset_1(C_687,k1_zfmisc_1(A_689))
      | v1_xboole_0(C_687)
      | v1_xboole_0(B_684)
      | v1_xboole_0(A_689) ) ),
    inference(resolution,[status(thm)],[c_50,c_2131])).

tff(c_3266,plain,(
    ! [A_737,F_733,C_735,B_732,D_734,E_736] :
      ( k2_partfun1(k4_subset_1(A_737,C_735,D_734),B_732,k1_tmap_1(A_737,B_732,C_735,D_734,E_736,F_733),D_734) = F_733
      | ~ v1_funct_1(k1_tmap_1(A_737,B_732,C_735,D_734,E_736,F_733))
      | k2_partfun1(D_734,B_732,F_733,k9_subset_1(A_737,C_735,D_734)) != k2_partfun1(C_735,B_732,E_736,k9_subset_1(A_737,C_735,D_734))
      | ~ m1_subset_1(F_733,k1_zfmisc_1(k2_zfmisc_1(D_734,B_732)))
      | ~ v1_funct_2(F_733,D_734,B_732)
      | ~ v1_funct_1(F_733)
      | ~ m1_subset_1(E_736,k1_zfmisc_1(k2_zfmisc_1(C_735,B_732)))
      | ~ v1_funct_2(E_736,C_735,B_732)
      | ~ v1_funct_1(E_736)
      | ~ m1_subset_1(D_734,k1_zfmisc_1(A_737))
      | v1_xboole_0(D_734)
      | ~ m1_subset_1(C_735,k1_zfmisc_1(A_737))
      | v1_xboole_0(C_735)
      | v1_xboole_0(B_732)
      | v1_xboole_0(A_737) ) ),
    inference(resolution,[status(thm)],[c_52,c_2859])).

tff(c_3270,plain,(
    ! [A_737,C_735,E_736] :
      ( k2_partfun1(k4_subset_1(A_737,C_735,'#skF_6'),'#skF_4',k1_tmap_1(A_737,'#skF_4',C_735,'#skF_6',E_736,'#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_737,'#skF_4',C_735,'#skF_6',E_736,'#skF_8'))
      | k2_partfun1(C_735,'#skF_4',E_736,k9_subset_1(A_737,C_735,'#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1(A_737,C_735,'#skF_6'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_736,k1_zfmisc_1(k2_zfmisc_1(C_735,'#skF_4')))
      | ~ v1_funct_2(E_736,C_735,'#skF_4')
      | ~ v1_funct_1(E_736)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_737))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_735,k1_zfmisc_1(A_737))
      | v1_xboole_0(C_735)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_737) ) ),
    inference(resolution,[status(thm)],[c_58,c_3266])).

tff(c_3276,plain,(
    ! [A_737,C_735,E_736] :
      ( k2_partfun1(k4_subset_1(A_737,C_735,'#skF_6'),'#skF_4',k1_tmap_1(A_737,'#skF_4',C_735,'#skF_6',E_736,'#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_737,'#skF_4',C_735,'#skF_6',E_736,'#skF_8'))
      | k2_partfun1(C_735,'#skF_4',E_736,k9_subset_1(A_737,C_735,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_737,C_735,'#skF_6'))
      | ~ m1_subset_1(E_736,k1_zfmisc_1(k2_zfmisc_1(C_735,'#skF_4')))
      | ~ v1_funct_2(E_736,C_735,'#skF_4')
      | ~ v1_funct_1(E_736)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_737))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_735,k1_zfmisc_1(A_737))
      | v1_xboole_0(C_735)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_737) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1388,c_3270])).

tff(c_3584,plain,(
    ! [A_778,C_779,E_780] :
      ( k2_partfun1(k4_subset_1(A_778,C_779,'#skF_6'),'#skF_4',k1_tmap_1(A_778,'#skF_4',C_779,'#skF_6',E_780,'#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_778,'#skF_4',C_779,'#skF_6',E_780,'#skF_8'))
      | k2_partfun1(C_779,'#skF_4',E_780,k9_subset_1(A_778,C_779,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_778,C_779,'#skF_6'))
      | ~ m1_subset_1(E_780,k1_zfmisc_1(k2_zfmisc_1(C_779,'#skF_4')))
      | ~ v1_funct_2(E_780,C_779,'#skF_4')
      | ~ v1_funct_1(E_780)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_778))
      | ~ m1_subset_1(C_779,k1_zfmisc_1(A_778))
      | v1_xboole_0(C_779)
      | v1_xboole_0(A_778) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_3276])).

tff(c_3591,plain,(
    ! [A_778] :
      ( k2_partfun1(k4_subset_1(A_778,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_778,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_778,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1(A_778,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_778,'#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_778))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_778))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_778) ) ),
    inference(resolution,[status(thm)],[c_64,c_3584])).

tff(c_3601,plain,(
    ! [A_778] :
      ( k2_partfun1(k4_subset_1(A_778,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_778,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_778,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_778,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_778,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_778))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_778))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_778) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_1391,c_3591])).

tff(c_3604,plain,(
    ! [A_781] :
      ( k2_partfun1(k4_subset_1(A_781,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_781,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_781,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_781,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_781,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_781))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_781))
      | v1_xboole_0(A_781) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3601])).

tff(c_143,plain,(
    ! [A_254,B_255,C_256] :
      ( ~ r1_xboole_0(A_254,B_255)
      | ~ r2_hidden(C_256,B_255)
      | ~ r2_hidden(C_256,A_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_278,plain,(
    ! [C_283,B_284,A_285] :
      ( ~ r2_hidden(C_283,B_284)
      | ~ r2_hidden(C_283,A_285)
      | k3_xboole_0(A_285,B_284) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_143])).

tff(c_288,plain,(
    ! [A_286,A_287] :
      ( ~ r2_hidden('#skF_1'(A_286),A_287)
      | k3_xboole_0(A_287,A_286) != k1_xboole_0
      | v1_xboole_0(A_286) ) ),
    inference(resolution,[status(thm)],[c_4,c_278])).

tff(c_293,plain,(
    ! [A_288] :
      ( k3_xboole_0(A_288,A_288) != k1_xboole_0
      | v1_xboole_0(A_288) ) ),
    inference(resolution,[status(thm)],[c_4,c_288])).

tff(c_297,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_293])).

tff(c_112,plain,(
    ! [C_239,A_240,B_241] :
      ( v1_relat_1(C_239)
      | ~ m1_subset_1(C_239,k1_zfmisc_1(k2_zfmisc_1(A_240,B_241))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_120,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_112])).

tff(c_121,plain,(
    ! [A_242,B_243] :
      ( r2_hidden('#skF_2'(A_242,B_243),A_242)
      | r1_xboole_0(A_242,B_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_125,plain,(
    ! [A_242,B_243] :
      ( ~ v1_xboole_0(A_242)
      | r1_xboole_0(A_242,B_243) ) ),
    inference(resolution,[status(thm)],[c_121,c_2])).

tff(c_171,plain,(
    ! [A_263,B_264] :
      ( k7_relat_1(A_263,B_264) = k1_xboole_0
      | ~ r1_xboole_0(B_264,k1_relat_1(A_263))
      | ~ v1_relat_1(A_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_187,plain,(
    ! [A_265,A_266] :
      ( k7_relat_1(A_265,A_266) = k1_xboole_0
      | ~ v1_relat_1(A_265)
      | ~ v1_xboole_0(A_266) ) ),
    inference(resolution,[status(thm)],[c_125,c_171])).

tff(c_192,plain,(
    ! [A_266] :
      ( k7_relat_1('#skF_7',A_266) = k1_xboole_0
      | ~ v1_xboole_0(A_266) ) ),
    inference(resolution,[status(thm)],[c_120,c_187])).

tff(c_309,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_297,c_192])).

tff(c_119,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_112])).

tff(c_193,plain,(
    ! [A_266] :
      ( k7_relat_1('#skF_8',A_266) = k1_xboole_0
      | ~ v1_xboole_0(A_266) ) ),
    inference(resolution,[status(thm)],[c_119,c_187])).

tff(c_308,plain,(
    k7_relat_1('#skF_8',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_297,c_193])).

tff(c_210,plain,(
    ! [A_273,B_274] :
      ( r1_xboole_0(A_273,B_274)
      | ~ r1_subset_1(A_273,B_274)
      | v1_xboole_0(B_274)
      | v1_xboole_0(A_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_405,plain,(
    ! [A_303,B_304] :
      ( k3_xboole_0(A_303,B_304) = k1_xboole_0
      | ~ r1_subset_1(A_303,B_304)
      | v1_xboole_0(B_304)
      | v1_xboole_0(A_303) ) ),
    inference(resolution,[status(thm)],[c_210,c_6])).

tff(c_411,plain,
    ( k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0
    | v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_405])).

tff(c_415,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_74,c_411])).

tff(c_373,plain,(
    ! [A_295,B_296,C_297,D_298] :
      ( k2_partfun1(A_295,B_296,C_297,D_298) = k7_relat_1(C_297,D_298)
      | ~ m1_subset_1(C_297,k1_zfmisc_1(k2_zfmisc_1(A_295,B_296)))
      | ~ v1_funct_1(C_297) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_377,plain,(
    ! [D_298] :
      ( k2_partfun1('#skF_5','#skF_4','#skF_7',D_298) = k7_relat_1('#skF_7',D_298)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_64,c_373])).

tff(c_383,plain,(
    ! [D_298] : k2_partfun1('#skF_5','#skF_4','#skF_7',D_298) = k7_relat_1('#skF_7',D_298) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_377])).

tff(c_375,plain,(
    ! [D_298] :
      ( k2_partfun1('#skF_6','#skF_4','#skF_8',D_298) = k7_relat_1('#skF_8',D_298)
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_58,c_373])).

tff(c_380,plain,(
    ! [D_298] : k2_partfun1('#skF_6','#skF_4','#skF_8',D_298) = k7_relat_1('#skF_8',D_298) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_375])).

tff(c_228,plain,(
    ! [A_276,B_277,C_278] :
      ( k9_subset_1(A_276,B_277,C_278) = k3_xboole_0(B_277,C_278)
      | ~ m1_subset_1(C_278,k1_zfmisc_1(A_276)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_239,plain,(
    ! [B_277] : k9_subset_1('#skF_3',B_277,'#skF_6') = k3_xboole_0(B_277,'#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_228])).

tff(c_56,plain,
    ( k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') != '#skF_8'
    | k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') != '#skF_7'
    | k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_111,plain,(
    k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_241,plain,(
    k2_partfun1('#skF_5','#skF_4','#skF_7',k3_xboole_0('#skF_5','#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_239,c_111])).

tff(c_384,plain,(
    k2_partfun1('#skF_5','#skF_4','#skF_7',k3_xboole_0('#skF_5','#skF_6')) != k7_relat_1('#skF_8',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_241])).

tff(c_404,plain,(
    k7_relat_1('#skF_7',k3_xboole_0('#skF_5','#skF_6')) != k7_relat_1('#skF_8',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_384])).

tff(c_416,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) != k7_relat_1('#skF_8',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_415,c_415,c_404])).

tff(c_419,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_308,c_416])).

tff(c_420,plain,
    ( k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') != '#skF_7'
    | k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_485,plain,(
    k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_420])).

tff(c_3615,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3604,c_485])).

tff(c_3629,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_573,c_574,c_1343,c_1297,c_1343,c_1297,c_2096,c_3615])).

tff(c_3631,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_3629])).

tff(c_3632,plain,(
    k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_420])).

tff(c_7041,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7032,c_3632])).

tff(c_7052,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_3725,c_3726,c_4563,c_4517,c_4563,c_4517,c_5316,c_7041])).

tff(c_7054,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_7052])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:12:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.78/3.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.78/3.10  
% 8.78/3.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.78/3.10  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2
% 8.78/3.10  
% 8.78/3.10  %Foreground sorts:
% 8.78/3.10  
% 8.78/3.10  
% 8.78/3.10  %Background operators:
% 8.78/3.10  
% 8.78/3.10  
% 8.78/3.10  %Foreground operators:
% 8.78/3.10  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 8.78/3.10  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.78/3.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.78/3.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.78/3.10  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.78/3.10  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.78/3.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.78/3.10  tff('#skF_7', type, '#skF_7': $i).
% 8.78/3.10  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.78/3.10  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 8.78/3.10  tff('#skF_5', type, '#skF_5': $i).
% 8.78/3.10  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.78/3.10  tff('#skF_6', type, '#skF_6': $i).
% 8.78/3.10  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.78/3.10  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 8.78/3.10  tff('#skF_3', type, '#skF_3': $i).
% 8.78/3.10  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.78/3.10  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.78/3.10  tff('#skF_8', type, '#skF_8': $i).
% 8.78/3.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.78/3.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.78/3.10  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.78/3.10  tff('#skF_4', type, '#skF_4': $i).
% 8.78/3.10  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.78/3.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.78/3.10  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.78/3.10  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 8.78/3.10  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.78/3.10  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.78/3.10  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.78/3.10  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.78/3.10  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 8.78/3.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.78/3.10  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.78/3.10  
% 8.78/3.13  tff(f_240, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 8.78/3.13  tff(f_55, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 8.78/3.13  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.78/3.13  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.78/3.13  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 8.78/3.13  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.78/3.13  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 8.78/3.13  tff(f_78, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 8.78/3.13  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 8.78/3.13  tff(f_198, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 8.78/3.13  tff(f_116, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 8.78/3.13  tff(f_164, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 8.78/3.13  tff(c_82, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_240])).
% 8.78/3.13  tff(c_76, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_240])).
% 8.78/3.13  tff(c_72, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_240])).
% 8.78/3.13  tff(c_16, plain, (![A_12]: (k3_xboole_0(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.78/3.13  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.78/3.13  tff(c_8, plain, (![A_5, B_6]: (r1_xboole_0(A_5, B_6) | k3_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.78/3.13  tff(c_466, plain, (![A_323, B_324, C_325]: (~r1_xboole_0(A_323, B_324) | ~r2_hidden(C_325, B_324) | ~r2_hidden(C_325, A_323))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.78/3.13  tff(c_3691, plain, (![C_795, B_796, A_797]: (~r2_hidden(C_795, B_796) | ~r2_hidden(C_795, A_797) | k3_xboole_0(A_797, B_796)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_466])).
% 8.78/3.13  tff(c_3705, plain, (![A_798, A_799]: (~r2_hidden('#skF_1'(A_798), A_799) | k3_xboole_0(A_799, A_798)!=k1_xboole_0 | v1_xboole_0(A_798))), inference(resolution, [status(thm)], [c_4, c_3691])).
% 8.78/3.13  tff(c_3710, plain, (![A_800]: (k3_xboole_0(A_800, A_800)!=k1_xboole_0 | v1_xboole_0(A_800))), inference(resolution, [status(thm)], [c_4, c_3705])).
% 8.78/3.13  tff(c_3714, plain, (v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_3710])).
% 8.78/3.13  tff(c_58, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_240])).
% 8.78/3.13  tff(c_422, plain, (![C_305, A_306, B_307]: (v1_relat_1(C_305) | ~m1_subset_1(C_305, k1_zfmisc_1(k2_zfmisc_1(A_306, B_307))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.78/3.13  tff(c_429, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_58, c_422])).
% 8.78/3.13  tff(c_431, plain, (![A_308, B_309]: (r2_hidden('#skF_2'(A_308, B_309), A_308) | r1_xboole_0(A_308, B_309))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.78/3.13  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.78/3.13  tff(c_435, plain, (![A_308, B_309]: (~v1_xboole_0(A_308) | r1_xboole_0(A_308, B_309))), inference(resolution, [status(thm)], [c_431, c_2])).
% 8.78/3.13  tff(c_3647, plain, (![A_784, B_785]: (k7_relat_1(A_784, B_785)=k1_xboole_0 | ~r1_xboole_0(B_785, k1_relat_1(A_784)) | ~v1_relat_1(A_784))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.78/3.13  tff(c_3663, plain, (![A_786, A_787]: (k7_relat_1(A_786, A_787)=k1_xboole_0 | ~v1_relat_1(A_786) | ~v1_xboole_0(A_787))), inference(resolution, [status(thm)], [c_435, c_3647])).
% 8.78/3.13  tff(c_3669, plain, (![A_787]: (k7_relat_1('#skF_8', A_787)=k1_xboole_0 | ~v1_xboole_0(A_787))), inference(resolution, [status(thm)], [c_429, c_3663])).
% 8.78/3.13  tff(c_3725, plain, (k7_relat_1('#skF_8', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_3714, c_3669])).
% 8.78/3.13  tff(c_64, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_240])).
% 8.78/3.13  tff(c_430, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_64, c_422])).
% 8.78/3.13  tff(c_3668, plain, (![A_787]: (k7_relat_1('#skF_7', A_787)=k1_xboole_0 | ~v1_xboole_0(A_787))), inference(resolution, [status(thm)], [c_430, c_3663])).
% 8.78/3.13  tff(c_3726, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_3714, c_3668])).
% 8.78/3.13  tff(c_78, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_240])).
% 8.78/3.13  tff(c_74, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_240])).
% 8.78/3.13  tff(c_70, plain, (r1_subset_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_240])).
% 8.78/3.13  tff(c_3674, plain, (![A_793, B_794]: (r1_xboole_0(A_793, B_794) | ~r1_subset_1(A_793, B_794) | v1_xboole_0(B_794) | v1_xboole_0(A_793))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.78/3.13  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.78/3.13  tff(c_4557, plain, (![A_902, B_903]: (k3_xboole_0(A_902, B_903)=k1_xboole_0 | ~r1_subset_1(A_902, B_903) | v1_xboole_0(B_903) | v1_xboole_0(A_902))), inference(resolution, [status(thm)], [c_3674, c_6])).
% 8.78/3.13  tff(c_4560, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0 | v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_70, c_4557])).
% 8.78/3.13  tff(c_4563, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_78, c_74, c_4560])).
% 8.78/3.13  tff(c_4506, plain, (![A_894, B_895, C_896]: (k9_subset_1(A_894, B_895, C_896)=k3_xboole_0(B_895, C_896) | ~m1_subset_1(C_896, k1_zfmisc_1(A_894)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.78/3.13  tff(c_4517, plain, (![B_895]: (k9_subset_1('#skF_3', B_895, '#skF_6')=k3_xboole_0(B_895, '#skF_6'))), inference(resolution, [status(thm)], [c_72, c_4506])).
% 8.78/3.13  tff(c_68, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_240])).
% 8.78/3.13  tff(c_66, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_240])).
% 8.78/3.13  tff(c_80, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_240])).
% 8.78/3.13  tff(c_62, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_240])).
% 8.78/3.13  tff(c_60, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_240])).
% 8.78/3.13  tff(c_4883, plain, (![E_942, C_941, A_943, F_939, B_938, D_940]: (v1_funct_1(k1_tmap_1(A_943, B_938, C_941, D_940, E_942, F_939)) | ~m1_subset_1(F_939, k1_zfmisc_1(k2_zfmisc_1(D_940, B_938))) | ~v1_funct_2(F_939, D_940, B_938) | ~v1_funct_1(F_939) | ~m1_subset_1(E_942, k1_zfmisc_1(k2_zfmisc_1(C_941, B_938))) | ~v1_funct_2(E_942, C_941, B_938) | ~v1_funct_1(E_942) | ~m1_subset_1(D_940, k1_zfmisc_1(A_943)) | v1_xboole_0(D_940) | ~m1_subset_1(C_941, k1_zfmisc_1(A_943)) | v1_xboole_0(C_941) | v1_xboole_0(B_938) | v1_xboole_0(A_943))), inference(cnfTransformation, [status(thm)], [f_198])).
% 8.78/3.13  tff(c_4885, plain, (![A_943, C_941, E_942]: (v1_funct_1(k1_tmap_1(A_943, '#skF_4', C_941, '#skF_6', E_942, '#skF_8')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_942, k1_zfmisc_1(k2_zfmisc_1(C_941, '#skF_4'))) | ~v1_funct_2(E_942, C_941, '#skF_4') | ~v1_funct_1(E_942) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_943)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_941, k1_zfmisc_1(A_943)) | v1_xboole_0(C_941) | v1_xboole_0('#skF_4') | v1_xboole_0(A_943))), inference(resolution, [status(thm)], [c_58, c_4883])).
% 8.78/3.13  tff(c_4890, plain, (![A_943, C_941, E_942]: (v1_funct_1(k1_tmap_1(A_943, '#skF_4', C_941, '#skF_6', E_942, '#skF_8')) | ~m1_subset_1(E_942, k1_zfmisc_1(k2_zfmisc_1(C_941, '#skF_4'))) | ~v1_funct_2(E_942, C_941, '#skF_4') | ~v1_funct_1(E_942) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_943)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_941, k1_zfmisc_1(A_943)) | v1_xboole_0(C_941) | v1_xboole_0('#skF_4') | v1_xboole_0(A_943))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_4885])).
% 8.78/3.13  tff(c_4911, plain, (![A_949, C_950, E_951]: (v1_funct_1(k1_tmap_1(A_949, '#skF_4', C_950, '#skF_6', E_951, '#skF_8')) | ~m1_subset_1(E_951, k1_zfmisc_1(k2_zfmisc_1(C_950, '#skF_4'))) | ~v1_funct_2(E_951, C_950, '#skF_4') | ~v1_funct_1(E_951) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_949)) | ~m1_subset_1(C_950, k1_zfmisc_1(A_949)) | v1_xboole_0(C_950) | v1_xboole_0(A_949))), inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_4890])).
% 8.78/3.13  tff(c_4915, plain, (![A_949]: (v1_funct_1(k1_tmap_1(A_949, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_949)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_949)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_949))), inference(resolution, [status(thm)], [c_64, c_4911])).
% 8.78/3.13  tff(c_4922, plain, (![A_949]: (v1_funct_1(k1_tmap_1(A_949, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_949)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_949)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_949))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_4915])).
% 8.78/3.13  tff(c_5309, plain, (![A_1021]: (v1_funct_1(k1_tmap_1(A_1021, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1021)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1021)) | v1_xboole_0(A_1021))), inference(negUnitSimplification, [status(thm)], [c_78, c_4922])).
% 8.78/3.13  tff(c_5312, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_76, c_5309])).
% 8.78/3.13  tff(c_5315, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_5312])).
% 8.78/3.13  tff(c_5316, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_82, c_5315])).
% 8.78/3.13  tff(c_4595, plain, (![A_907, B_908, C_909, D_910]: (k2_partfun1(A_907, B_908, C_909, D_910)=k7_relat_1(C_909, D_910) | ~m1_subset_1(C_909, k1_zfmisc_1(k2_zfmisc_1(A_907, B_908))) | ~v1_funct_1(C_909))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.78/3.13  tff(c_4599, plain, (![D_910]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_910)=k7_relat_1('#skF_7', D_910) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_64, c_4595])).
% 8.78/3.13  tff(c_4605, plain, (![D_910]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_910)=k7_relat_1('#skF_7', D_910))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_4599])).
% 8.78/3.13  tff(c_4597, plain, (![D_910]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_910)=k7_relat_1('#skF_8', D_910) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_58, c_4595])).
% 8.78/3.13  tff(c_4602, plain, (![D_910]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_910)=k7_relat_1('#skF_8', D_910))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_4597])).
% 8.78/3.13  tff(c_52, plain, (![D_169, E_170, A_166, B_167, C_168, F_171]: (v1_funct_2(k1_tmap_1(A_166, B_167, C_168, D_169, E_170, F_171), k4_subset_1(A_166, C_168, D_169), B_167) | ~m1_subset_1(F_171, k1_zfmisc_1(k2_zfmisc_1(D_169, B_167))) | ~v1_funct_2(F_171, D_169, B_167) | ~v1_funct_1(F_171) | ~m1_subset_1(E_170, k1_zfmisc_1(k2_zfmisc_1(C_168, B_167))) | ~v1_funct_2(E_170, C_168, B_167) | ~v1_funct_1(E_170) | ~m1_subset_1(D_169, k1_zfmisc_1(A_166)) | v1_xboole_0(D_169) | ~m1_subset_1(C_168, k1_zfmisc_1(A_166)) | v1_xboole_0(C_168) | v1_xboole_0(B_167) | v1_xboole_0(A_166))), inference(cnfTransformation, [status(thm)], [f_198])).
% 8.78/3.13  tff(c_50, plain, (![D_169, E_170, A_166, B_167, C_168, F_171]: (m1_subset_1(k1_tmap_1(A_166, B_167, C_168, D_169, E_170, F_171), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_166, C_168, D_169), B_167))) | ~m1_subset_1(F_171, k1_zfmisc_1(k2_zfmisc_1(D_169, B_167))) | ~v1_funct_2(F_171, D_169, B_167) | ~v1_funct_1(F_171) | ~m1_subset_1(E_170, k1_zfmisc_1(k2_zfmisc_1(C_168, B_167))) | ~v1_funct_2(E_170, C_168, B_167) | ~v1_funct_1(E_170) | ~m1_subset_1(D_169, k1_zfmisc_1(A_166)) | v1_xboole_0(D_169) | ~m1_subset_1(C_168, k1_zfmisc_1(A_166)) | v1_xboole_0(C_168) | v1_xboole_0(B_167) | v1_xboole_0(A_166))), inference(cnfTransformation, [status(thm)], [f_198])).
% 8.78/3.13  tff(c_5264, plain, (![D_1008, E_1009, B_1012, F_1010, A_1007, C_1011]: (k2_partfun1(k4_subset_1(A_1007, C_1011, D_1008), B_1012, k1_tmap_1(A_1007, B_1012, C_1011, D_1008, E_1009, F_1010), C_1011)=E_1009 | ~m1_subset_1(k1_tmap_1(A_1007, B_1012, C_1011, D_1008, E_1009, F_1010), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1007, C_1011, D_1008), B_1012))) | ~v1_funct_2(k1_tmap_1(A_1007, B_1012, C_1011, D_1008, E_1009, F_1010), k4_subset_1(A_1007, C_1011, D_1008), B_1012) | ~v1_funct_1(k1_tmap_1(A_1007, B_1012, C_1011, D_1008, E_1009, F_1010)) | k2_partfun1(D_1008, B_1012, F_1010, k9_subset_1(A_1007, C_1011, D_1008))!=k2_partfun1(C_1011, B_1012, E_1009, k9_subset_1(A_1007, C_1011, D_1008)) | ~m1_subset_1(F_1010, k1_zfmisc_1(k2_zfmisc_1(D_1008, B_1012))) | ~v1_funct_2(F_1010, D_1008, B_1012) | ~v1_funct_1(F_1010) | ~m1_subset_1(E_1009, k1_zfmisc_1(k2_zfmisc_1(C_1011, B_1012))) | ~v1_funct_2(E_1009, C_1011, B_1012) | ~v1_funct_1(E_1009) | ~m1_subset_1(D_1008, k1_zfmisc_1(A_1007)) | v1_xboole_0(D_1008) | ~m1_subset_1(C_1011, k1_zfmisc_1(A_1007)) | v1_xboole_0(C_1011) | v1_xboole_0(B_1012) | v1_xboole_0(A_1007))), inference(cnfTransformation, [status(thm)], [f_164])).
% 8.78/3.13  tff(c_5976, plain, (![B_1140, D_1142, A_1145, C_1143, F_1141, E_1144]: (k2_partfun1(k4_subset_1(A_1145, C_1143, D_1142), B_1140, k1_tmap_1(A_1145, B_1140, C_1143, D_1142, E_1144, F_1141), C_1143)=E_1144 | ~v1_funct_2(k1_tmap_1(A_1145, B_1140, C_1143, D_1142, E_1144, F_1141), k4_subset_1(A_1145, C_1143, D_1142), B_1140) | ~v1_funct_1(k1_tmap_1(A_1145, B_1140, C_1143, D_1142, E_1144, F_1141)) | k2_partfun1(D_1142, B_1140, F_1141, k9_subset_1(A_1145, C_1143, D_1142))!=k2_partfun1(C_1143, B_1140, E_1144, k9_subset_1(A_1145, C_1143, D_1142)) | ~m1_subset_1(F_1141, k1_zfmisc_1(k2_zfmisc_1(D_1142, B_1140))) | ~v1_funct_2(F_1141, D_1142, B_1140) | ~v1_funct_1(F_1141) | ~m1_subset_1(E_1144, k1_zfmisc_1(k2_zfmisc_1(C_1143, B_1140))) | ~v1_funct_2(E_1144, C_1143, B_1140) | ~v1_funct_1(E_1144) | ~m1_subset_1(D_1142, k1_zfmisc_1(A_1145)) | v1_xboole_0(D_1142) | ~m1_subset_1(C_1143, k1_zfmisc_1(A_1145)) | v1_xboole_0(C_1143) | v1_xboole_0(B_1140) | v1_xboole_0(A_1145))), inference(resolution, [status(thm)], [c_50, c_5264])).
% 8.78/3.13  tff(c_6503, plain, (![D_1202, C_1203, B_1200, F_1201, E_1204, A_1205]: (k2_partfun1(k4_subset_1(A_1205, C_1203, D_1202), B_1200, k1_tmap_1(A_1205, B_1200, C_1203, D_1202, E_1204, F_1201), C_1203)=E_1204 | ~v1_funct_1(k1_tmap_1(A_1205, B_1200, C_1203, D_1202, E_1204, F_1201)) | k2_partfun1(D_1202, B_1200, F_1201, k9_subset_1(A_1205, C_1203, D_1202))!=k2_partfun1(C_1203, B_1200, E_1204, k9_subset_1(A_1205, C_1203, D_1202)) | ~m1_subset_1(F_1201, k1_zfmisc_1(k2_zfmisc_1(D_1202, B_1200))) | ~v1_funct_2(F_1201, D_1202, B_1200) | ~v1_funct_1(F_1201) | ~m1_subset_1(E_1204, k1_zfmisc_1(k2_zfmisc_1(C_1203, B_1200))) | ~v1_funct_2(E_1204, C_1203, B_1200) | ~v1_funct_1(E_1204) | ~m1_subset_1(D_1202, k1_zfmisc_1(A_1205)) | v1_xboole_0(D_1202) | ~m1_subset_1(C_1203, k1_zfmisc_1(A_1205)) | v1_xboole_0(C_1203) | v1_xboole_0(B_1200) | v1_xboole_0(A_1205))), inference(resolution, [status(thm)], [c_52, c_5976])).
% 8.78/3.13  tff(c_6507, plain, (![A_1205, C_1203, E_1204]: (k2_partfun1(k4_subset_1(A_1205, C_1203, '#skF_6'), '#skF_4', k1_tmap_1(A_1205, '#skF_4', C_1203, '#skF_6', E_1204, '#skF_8'), C_1203)=E_1204 | ~v1_funct_1(k1_tmap_1(A_1205, '#skF_4', C_1203, '#skF_6', E_1204, '#skF_8')) | k2_partfun1(C_1203, '#skF_4', E_1204, k9_subset_1(A_1205, C_1203, '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1(A_1205, C_1203, '#skF_6')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_1204, k1_zfmisc_1(k2_zfmisc_1(C_1203, '#skF_4'))) | ~v1_funct_2(E_1204, C_1203, '#skF_4') | ~v1_funct_1(E_1204) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1205)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_1203, k1_zfmisc_1(A_1205)) | v1_xboole_0(C_1203) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1205))), inference(resolution, [status(thm)], [c_58, c_6503])).
% 8.78/3.13  tff(c_6513, plain, (![A_1205, C_1203, E_1204]: (k2_partfun1(k4_subset_1(A_1205, C_1203, '#skF_6'), '#skF_4', k1_tmap_1(A_1205, '#skF_4', C_1203, '#skF_6', E_1204, '#skF_8'), C_1203)=E_1204 | ~v1_funct_1(k1_tmap_1(A_1205, '#skF_4', C_1203, '#skF_6', E_1204, '#skF_8')) | k2_partfun1(C_1203, '#skF_4', E_1204, k9_subset_1(A_1205, C_1203, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_1205, C_1203, '#skF_6')) | ~m1_subset_1(E_1204, k1_zfmisc_1(k2_zfmisc_1(C_1203, '#skF_4'))) | ~v1_funct_2(E_1204, C_1203, '#skF_4') | ~v1_funct_1(E_1204) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1205)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_1203, k1_zfmisc_1(A_1205)) | v1_xboole_0(C_1203) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1205))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_4602, c_6507])).
% 8.78/3.13  tff(c_6683, plain, (![A_1234, C_1235, E_1236]: (k2_partfun1(k4_subset_1(A_1234, C_1235, '#skF_6'), '#skF_4', k1_tmap_1(A_1234, '#skF_4', C_1235, '#skF_6', E_1236, '#skF_8'), C_1235)=E_1236 | ~v1_funct_1(k1_tmap_1(A_1234, '#skF_4', C_1235, '#skF_6', E_1236, '#skF_8')) | k2_partfun1(C_1235, '#skF_4', E_1236, k9_subset_1(A_1234, C_1235, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_1234, C_1235, '#skF_6')) | ~m1_subset_1(E_1236, k1_zfmisc_1(k2_zfmisc_1(C_1235, '#skF_4'))) | ~v1_funct_2(E_1236, C_1235, '#skF_4') | ~v1_funct_1(E_1236) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1234)) | ~m1_subset_1(C_1235, k1_zfmisc_1(A_1234)) | v1_xboole_0(C_1235) | v1_xboole_0(A_1234))), inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_6513])).
% 8.78/3.13  tff(c_6690, plain, (![A_1234]: (k2_partfun1(k4_subset_1(A_1234, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_1234, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1234, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1(A_1234, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_1234, '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1234)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1234)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_1234))), inference(resolution, [status(thm)], [c_64, c_6683])).
% 8.78/3.13  tff(c_6700, plain, (![A_1234]: (k2_partfun1(k4_subset_1(A_1234, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_1234, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1234, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_1234, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_1234, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1234)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1234)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_1234))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_4605, c_6690])).
% 8.78/3.13  tff(c_7032, plain, (![A_1272]: (k2_partfun1(k4_subset_1(A_1272, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_1272, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1272, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_1272, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_1272, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1272)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1272)) | v1_xboole_0(A_1272))), inference(negUnitSimplification, [status(thm)], [c_78, c_6700])).
% 8.78/3.13  tff(c_543, plain, (![C_342, B_343, A_344]: (~r2_hidden(C_342, B_343) | ~r2_hidden(C_342, A_344) | k3_xboole_0(A_344, B_343)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_466])).
% 8.78/3.13  tff(c_553, plain, (![A_345, A_346]: (~r2_hidden('#skF_1'(A_345), A_346) | k3_xboole_0(A_346, A_345)!=k1_xboole_0 | v1_xboole_0(A_345))), inference(resolution, [status(thm)], [c_4, c_543])).
% 8.78/3.13  tff(c_558, plain, (![A_347]: (k3_xboole_0(A_347, A_347)!=k1_xboole_0 | v1_xboole_0(A_347))), inference(resolution, [status(thm)], [c_4, c_553])).
% 8.78/3.13  tff(c_562, plain, (v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_558])).
% 8.78/3.13  tff(c_499, plain, (![A_331, B_332]: (k7_relat_1(A_331, B_332)=k1_xboole_0 | ~r1_xboole_0(B_332, k1_relat_1(A_331)) | ~v1_relat_1(A_331))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.78/3.13  tff(c_515, plain, (![A_333, A_334]: (k7_relat_1(A_333, A_334)=k1_xboole_0 | ~v1_relat_1(A_333) | ~v1_xboole_0(A_334))), inference(resolution, [status(thm)], [c_435, c_499])).
% 8.78/3.13  tff(c_521, plain, (![A_334]: (k7_relat_1('#skF_8', A_334)=k1_xboole_0 | ~v1_xboole_0(A_334))), inference(resolution, [status(thm)], [c_429, c_515])).
% 8.78/3.13  tff(c_573, plain, (k7_relat_1('#skF_8', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_562, c_521])).
% 8.78/3.13  tff(c_520, plain, (![A_334]: (k7_relat_1('#skF_7', A_334)=k1_xboole_0 | ~v1_xboole_0(A_334))), inference(resolution, [status(thm)], [c_430, c_515])).
% 8.78/3.13  tff(c_574, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_562, c_520])).
% 8.78/3.13  tff(c_526, plain, (![A_340, B_341]: (r1_xboole_0(A_340, B_341) | ~r1_subset_1(A_340, B_341) | v1_xboole_0(B_341) | v1_xboole_0(A_340))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.78/3.13  tff(c_1337, plain, (![A_437, B_438]: (k3_xboole_0(A_437, B_438)=k1_xboole_0 | ~r1_subset_1(A_437, B_438) | v1_xboole_0(B_438) | v1_xboole_0(A_437))), inference(resolution, [status(thm)], [c_526, c_6])).
% 8.78/3.13  tff(c_1340, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0 | v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_70, c_1337])).
% 8.78/3.13  tff(c_1343, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_78, c_74, c_1340])).
% 8.78/3.13  tff(c_1286, plain, (![A_429, B_430, C_431]: (k9_subset_1(A_429, B_430, C_431)=k3_xboole_0(B_430, C_431) | ~m1_subset_1(C_431, k1_zfmisc_1(A_429)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.78/3.13  tff(c_1297, plain, (![B_430]: (k9_subset_1('#skF_3', B_430, '#skF_6')=k3_xboole_0(B_430, '#skF_6'))), inference(resolution, [status(thm)], [c_72, c_1286])).
% 8.78/3.13  tff(c_1663, plain, (![C_476, B_473, D_475, F_474, E_477, A_478]: (v1_funct_1(k1_tmap_1(A_478, B_473, C_476, D_475, E_477, F_474)) | ~m1_subset_1(F_474, k1_zfmisc_1(k2_zfmisc_1(D_475, B_473))) | ~v1_funct_2(F_474, D_475, B_473) | ~v1_funct_1(F_474) | ~m1_subset_1(E_477, k1_zfmisc_1(k2_zfmisc_1(C_476, B_473))) | ~v1_funct_2(E_477, C_476, B_473) | ~v1_funct_1(E_477) | ~m1_subset_1(D_475, k1_zfmisc_1(A_478)) | v1_xboole_0(D_475) | ~m1_subset_1(C_476, k1_zfmisc_1(A_478)) | v1_xboole_0(C_476) | v1_xboole_0(B_473) | v1_xboole_0(A_478))), inference(cnfTransformation, [status(thm)], [f_198])).
% 8.78/3.13  tff(c_1665, plain, (![A_478, C_476, E_477]: (v1_funct_1(k1_tmap_1(A_478, '#skF_4', C_476, '#skF_6', E_477, '#skF_8')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_477, k1_zfmisc_1(k2_zfmisc_1(C_476, '#skF_4'))) | ~v1_funct_2(E_477, C_476, '#skF_4') | ~v1_funct_1(E_477) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_478)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_476, k1_zfmisc_1(A_478)) | v1_xboole_0(C_476) | v1_xboole_0('#skF_4') | v1_xboole_0(A_478))), inference(resolution, [status(thm)], [c_58, c_1663])).
% 8.78/3.13  tff(c_1670, plain, (![A_478, C_476, E_477]: (v1_funct_1(k1_tmap_1(A_478, '#skF_4', C_476, '#skF_6', E_477, '#skF_8')) | ~m1_subset_1(E_477, k1_zfmisc_1(k2_zfmisc_1(C_476, '#skF_4'))) | ~v1_funct_2(E_477, C_476, '#skF_4') | ~v1_funct_1(E_477) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_478)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_476, k1_zfmisc_1(A_478)) | v1_xboole_0(C_476) | v1_xboole_0('#skF_4') | v1_xboole_0(A_478))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1665])).
% 8.78/3.13  tff(c_1691, plain, (![A_484, C_485, E_486]: (v1_funct_1(k1_tmap_1(A_484, '#skF_4', C_485, '#skF_6', E_486, '#skF_8')) | ~m1_subset_1(E_486, k1_zfmisc_1(k2_zfmisc_1(C_485, '#skF_4'))) | ~v1_funct_2(E_486, C_485, '#skF_4') | ~v1_funct_1(E_486) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_484)) | ~m1_subset_1(C_485, k1_zfmisc_1(A_484)) | v1_xboole_0(C_485) | v1_xboole_0(A_484))), inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_1670])).
% 8.78/3.13  tff(c_1695, plain, (![A_484]: (v1_funct_1(k1_tmap_1(A_484, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_484)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_484)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_484))), inference(resolution, [status(thm)], [c_64, c_1691])).
% 8.78/3.13  tff(c_1702, plain, (![A_484]: (v1_funct_1(k1_tmap_1(A_484, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_484)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_484)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_484))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_1695])).
% 8.78/3.13  tff(c_2089, plain, (![A_556]: (v1_funct_1(k1_tmap_1(A_556, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_556)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_556)) | v1_xboole_0(A_556))), inference(negUnitSimplification, [status(thm)], [c_78, c_1702])).
% 8.78/3.13  tff(c_2092, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_76, c_2089])).
% 8.78/3.13  tff(c_2095, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2092])).
% 8.78/3.13  tff(c_2096, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_82, c_2095])).
% 8.78/3.13  tff(c_1381, plain, (![A_443, B_444, C_445, D_446]: (k2_partfun1(A_443, B_444, C_445, D_446)=k7_relat_1(C_445, D_446) | ~m1_subset_1(C_445, k1_zfmisc_1(k2_zfmisc_1(A_443, B_444))) | ~v1_funct_1(C_445))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.78/3.13  tff(c_1385, plain, (![D_446]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_446)=k7_relat_1('#skF_7', D_446) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_64, c_1381])).
% 8.78/3.13  tff(c_1391, plain, (![D_446]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_446)=k7_relat_1('#skF_7', D_446))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1385])).
% 8.78/3.13  tff(c_1383, plain, (![D_446]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_446)=k7_relat_1('#skF_8', D_446) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_58, c_1381])).
% 8.78/3.13  tff(c_1388, plain, (![D_446]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_446)=k7_relat_1('#skF_8', D_446))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1383])).
% 8.78/3.13  tff(c_2131, plain, (![E_564, A_562, F_565, D_563, C_566, B_567]: (k2_partfun1(k4_subset_1(A_562, C_566, D_563), B_567, k1_tmap_1(A_562, B_567, C_566, D_563, E_564, F_565), D_563)=F_565 | ~m1_subset_1(k1_tmap_1(A_562, B_567, C_566, D_563, E_564, F_565), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_562, C_566, D_563), B_567))) | ~v1_funct_2(k1_tmap_1(A_562, B_567, C_566, D_563, E_564, F_565), k4_subset_1(A_562, C_566, D_563), B_567) | ~v1_funct_1(k1_tmap_1(A_562, B_567, C_566, D_563, E_564, F_565)) | k2_partfun1(D_563, B_567, F_565, k9_subset_1(A_562, C_566, D_563))!=k2_partfun1(C_566, B_567, E_564, k9_subset_1(A_562, C_566, D_563)) | ~m1_subset_1(F_565, k1_zfmisc_1(k2_zfmisc_1(D_563, B_567))) | ~v1_funct_2(F_565, D_563, B_567) | ~v1_funct_1(F_565) | ~m1_subset_1(E_564, k1_zfmisc_1(k2_zfmisc_1(C_566, B_567))) | ~v1_funct_2(E_564, C_566, B_567) | ~v1_funct_1(E_564) | ~m1_subset_1(D_563, k1_zfmisc_1(A_562)) | v1_xboole_0(D_563) | ~m1_subset_1(C_566, k1_zfmisc_1(A_562)) | v1_xboole_0(C_566) | v1_xboole_0(B_567) | v1_xboole_0(A_562))), inference(cnfTransformation, [status(thm)], [f_164])).
% 8.78/3.13  tff(c_2859, plain, (![E_688, A_689, B_684, D_686, F_685, C_687]: (k2_partfun1(k4_subset_1(A_689, C_687, D_686), B_684, k1_tmap_1(A_689, B_684, C_687, D_686, E_688, F_685), D_686)=F_685 | ~v1_funct_2(k1_tmap_1(A_689, B_684, C_687, D_686, E_688, F_685), k4_subset_1(A_689, C_687, D_686), B_684) | ~v1_funct_1(k1_tmap_1(A_689, B_684, C_687, D_686, E_688, F_685)) | k2_partfun1(D_686, B_684, F_685, k9_subset_1(A_689, C_687, D_686))!=k2_partfun1(C_687, B_684, E_688, k9_subset_1(A_689, C_687, D_686)) | ~m1_subset_1(F_685, k1_zfmisc_1(k2_zfmisc_1(D_686, B_684))) | ~v1_funct_2(F_685, D_686, B_684) | ~v1_funct_1(F_685) | ~m1_subset_1(E_688, k1_zfmisc_1(k2_zfmisc_1(C_687, B_684))) | ~v1_funct_2(E_688, C_687, B_684) | ~v1_funct_1(E_688) | ~m1_subset_1(D_686, k1_zfmisc_1(A_689)) | v1_xboole_0(D_686) | ~m1_subset_1(C_687, k1_zfmisc_1(A_689)) | v1_xboole_0(C_687) | v1_xboole_0(B_684) | v1_xboole_0(A_689))), inference(resolution, [status(thm)], [c_50, c_2131])).
% 8.78/3.13  tff(c_3266, plain, (![A_737, F_733, C_735, B_732, D_734, E_736]: (k2_partfun1(k4_subset_1(A_737, C_735, D_734), B_732, k1_tmap_1(A_737, B_732, C_735, D_734, E_736, F_733), D_734)=F_733 | ~v1_funct_1(k1_tmap_1(A_737, B_732, C_735, D_734, E_736, F_733)) | k2_partfun1(D_734, B_732, F_733, k9_subset_1(A_737, C_735, D_734))!=k2_partfun1(C_735, B_732, E_736, k9_subset_1(A_737, C_735, D_734)) | ~m1_subset_1(F_733, k1_zfmisc_1(k2_zfmisc_1(D_734, B_732))) | ~v1_funct_2(F_733, D_734, B_732) | ~v1_funct_1(F_733) | ~m1_subset_1(E_736, k1_zfmisc_1(k2_zfmisc_1(C_735, B_732))) | ~v1_funct_2(E_736, C_735, B_732) | ~v1_funct_1(E_736) | ~m1_subset_1(D_734, k1_zfmisc_1(A_737)) | v1_xboole_0(D_734) | ~m1_subset_1(C_735, k1_zfmisc_1(A_737)) | v1_xboole_0(C_735) | v1_xboole_0(B_732) | v1_xboole_0(A_737))), inference(resolution, [status(thm)], [c_52, c_2859])).
% 8.78/3.13  tff(c_3270, plain, (![A_737, C_735, E_736]: (k2_partfun1(k4_subset_1(A_737, C_735, '#skF_6'), '#skF_4', k1_tmap_1(A_737, '#skF_4', C_735, '#skF_6', E_736, '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_737, '#skF_4', C_735, '#skF_6', E_736, '#skF_8')) | k2_partfun1(C_735, '#skF_4', E_736, k9_subset_1(A_737, C_735, '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1(A_737, C_735, '#skF_6')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_736, k1_zfmisc_1(k2_zfmisc_1(C_735, '#skF_4'))) | ~v1_funct_2(E_736, C_735, '#skF_4') | ~v1_funct_1(E_736) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_737)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_735, k1_zfmisc_1(A_737)) | v1_xboole_0(C_735) | v1_xboole_0('#skF_4') | v1_xboole_0(A_737))), inference(resolution, [status(thm)], [c_58, c_3266])).
% 8.78/3.13  tff(c_3276, plain, (![A_737, C_735, E_736]: (k2_partfun1(k4_subset_1(A_737, C_735, '#skF_6'), '#skF_4', k1_tmap_1(A_737, '#skF_4', C_735, '#skF_6', E_736, '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_737, '#skF_4', C_735, '#skF_6', E_736, '#skF_8')) | k2_partfun1(C_735, '#skF_4', E_736, k9_subset_1(A_737, C_735, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_737, C_735, '#skF_6')) | ~m1_subset_1(E_736, k1_zfmisc_1(k2_zfmisc_1(C_735, '#skF_4'))) | ~v1_funct_2(E_736, C_735, '#skF_4') | ~v1_funct_1(E_736) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_737)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_735, k1_zfmisc_1(A_737)) | v1_xboole_0(C_735) | v1_xboole_0('#skF_4') | v1_xboole_0(A_737))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1388, c_3270])).
% 8.78/3.13  tff(c_3584, plain, (![A_778, C_779, E_780]: (k2_partfun1(k4_subset_1(A_778, C_779, '#skF_6'), '#skF_4', k1_tmap_1(A_778, '#skF_4', C_779, '#skF_6', E_780, '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_778, '#skF_4', C_779, '#skF_6', E_780, '#skF_8')) | k2_partfun1(C_779, '#skF_4', E_780, k9_subset_1(A_778, C_779, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_778, C_779, '#skF_6')) | ~m1_subset_1(E_780, k1_zfmisc_1(k2_zfmisc_1(C_779, '#skF_4'))) | ~v1_funct_2(E_780, C_779, '#skF_4') | ~v1_funct_1(E_780) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_778)) | ~m1_subset_1(C_779, k1_zfmisc_1(A_778)) | v1_xboole_0(C_779) | v1_xboole_0(A_778))), inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_3276])).
% 8.78/3.13  tff(c_3591, plain, (![A_778]: (k2_partfun1(k4_subset_1(A_778, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_778, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_778, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1(A_778, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_778, '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_778)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_778)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_778))), inference(resolution, [status(thm)], [c_64, c_3584])).
% 8.78/3.13  tff(c_3601, plain, (![A_778]: (k2_partfun1(k4_subset_1(A_778, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_778, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_778, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_778, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_778, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_778)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_778)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_778))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_1391, c_3591])).
% 8.78/3.13  tff(c_3604, plain, (![A_781]: (k2_partfun1(k4_subset_1(A_781, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_781, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_781, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_781, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_781, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_781)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_781)) | v1_xboole_0(A_781))), inference(negUnitSimplification, [status(thm)], [c_78, c_3601])).
% 8.78/3.13  tff(c_143, plain, (![A_254, B_255, C_256]: (~r1_xboole_0(A_254, B_255) | ~r2_hidden(C_256, B_255) | ~r2_hidden(C_256, A_254))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.78/3.13  tff(c_278, plain, (![C_283, B_284, A_285]: (~r2_hidden(C_283, B_284) | ~r2_hidden(C_283, A_285) | k3_xboole_0(A_285, B_284)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_143])).
% 8.78/3.13  tff(c_288, plain, (![A_286, A_287]: (~r2_hidden('#skF_1'(A_286), A_287) | k3_xboole_0(A_287, A_286)!=k1_xboole_0 | v1_xboole_0(A_286))), inference(resolution, [status(thm)], [c_4, c_278])).
% 8.78/3.13  tff(c_293, plain, (![A_288]: (k3_xboole_0(A_288, A_288)!=k1_xboole_0 | v1_xboole_0(A_288))), inference(resolution, [status(thm)], [c_4, c_288])).
% 8.78/3.13  tff(c_297, plain, (v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_293])).
% 8.78/3.13  tff(c_112, plain, (![C_239, A_240, B_241]: (v1_relat_1(C_239) | ~m1_subset_1(C_239, k1_zfmisc_1(k2_zfmisc_1(A_240, B_241))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.78/3.13  tff(c_120, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_64, c_112])).
% 8.78/3.13  tff(c_121, plain, (![A_242, B_243]: (r2_hidden('#skF_2'(A_242, B_243), A_242) | r1_xboole_0(A_242, B_243))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.78/3.13  tff(c_125, plain, (![A_242, B_243]: (~v1_xboole_0(A_242) | r1_xboole_0(A_242, B_243))), inference(resolution, [status(thm)], [c_121, c_2])).
% 8.78/3.13  tff(c_171, plain, (![A_263, B_264]: (k7_relat_1(A_263, B_264)=k1_xboole_0 | ~r1_xboole_0(B_264, k1_relat_1(A_263)) | ~v1_relat_1(A_263))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.78/3.13  tff(c_187, plain, (![A_265, A_266]: (k7_relat_1(A_265, A_266)=k1_xboole_0 | ~v1_relat_1(A_265) | ~v1_xboole_0(A_266))), inference(resolution, [status(thm)], [c_125, c_171])).
% 8.78/3.13  tff(c_192, plain, (![A_266]: (k7_relat_1('#skF_7', A_266)=k1_xboole_0 | ~v1_xboole_0(A_266))), inference(resolution, [status(thm)], [c_120, c_187])).
% 8.78/3.13  tff(c_309, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_297, c_192])).
% 8.78/3.13  tff(c_119, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_58, c_112])).
% 8.78/3.13  tff(c_193, plain, (![A_266]: (k7_relat_1('#skF_8', A_266)=k1_xboole_0 | ~v1_xboole_0(A_266))), inference(resolution, [status(thm)], [c_119, c_187])).
% 8.78/3.13  tff(c_308, plain, (k7_relat_1('#skF_8', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_297, c_193])).
% 8.78/3.13  tff(c_210, plain, (![A_273, B_274]: (r1_xboole_0(A_273, B_274) | ~r1_subset_1(A_273, B_274) | v1_xboole_0(B_274) | v1_xboole_0(A_273))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.78/3.13  tff(c_405, plain, (![A_303, B_304]: (k3_xboole_0(A_303, B_304)=k1_xboole_0 | ~r1_subset_1(A_303, B_304) | v1_xboole_0(B_304) | v1_xboole_0(A_303))), inference(resolution, [status(thm)], [c_210, c_6])).
% 8.78/3.13  tff(c_411, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0 | v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_70, c_405])).
% 8.78/3.13  tff(c_415, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_78, c_74, c_411])).
% 8.78/3.13  tff(c_373, plain, (![A_295, B_296, C_297, D_298]: (k2_partfun1(A_295, B_296, C_297, D_298)=k7_relat_1(C_297, D_298) | ~m1_subset_1(C_297, k1_zfmisc_1(k2_zfmisc_1(A_295, B_296))) | ~v1_funct_1(C_297))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.78/3.13  tff(c_377, plain, (![D_298]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_298)=k7_relat_1('#skF_7', D_298) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_64, c_373])).
% 8.78/3.13  tff(c_383, plain, (![D_298]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_298)=k7_relat_1('#skF_7', D_298))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_377])).
% 8.78/3.13  tff(c_375, plain, (![D_298]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_298)=k7_relat_1('#skF_8', D_298) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_58, c_373])).
% 8.78/3.13  tff(c_380, plain, (![D_298]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_298)=k7_relat_1('#skF_8', D_298))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_375])).
% 8.78/3.13  tff(c_228, plain, (![A_276, B_277, C_278]: (k9_subset_1(A_276, B_277, C_278)=k3_xboole_0(B_277, C_278) | ~m1_subset_1(C_278, k1_zfmisc_1(A_276)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.78/3.13  tff(c_239, plain, (![B_277]: (k9_subset_1('#skF_3', B_277, '#skF_6')=k3_xboole_0(B_277, '#skF_6'))), inference(resolution, [status(thm)], [c_72, c_228])).
% 8.78/3.13  tff(c_56, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')!='#skF_8' | k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')!='#skF_7' | k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_240])).
% 8.78/3.13  tff(c_111, plain, (k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_56])).
% 8.78/3.13  tff(c_241, plain, (k2_partfun1('#skF_5', '#skF_4', '#skF_7', k3_xboole_0('#skF_5', '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k3_xboole_0('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_239, c_239, c_111])).
% 8.78/3.13  tff(c_384, plain, (k2_partfun1('#skF_5', '#skF_4', '#skF_7', k3_xboole_0('#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k3_xboole_0('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_380, c_241])).
% 8.78/3.13  tff(c_404, plain, (k7_relat_1('#skF_7', k3_xboole_0('#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k3_xboole_0('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_383, c_384])).
% 8.78/3.13  tff(c_416, plain, (k7_relat_1('#skF_7', k1_xboole_0)!=k7_relat_1('#skF_8', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_415, c_415, c_404])).
% 8.78/3.13  tff(c_419, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_309, c_308, c_416])).
% 8.78/3.13  tff(c_420, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')!='#skF_7' | k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')!='#skF_8'), inference(splitRight, [status(thm)], [c_56])).
% 8.78/3.13  tff(c_485, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')!='#skF_8'), inference(splitLeft, [status(thm)], [c_420])).
% 8.78/3.13  tff(c_3615, plain, (~v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3604, c_485])).
% 8.78/3.13  tff(c_3629, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_573, c_574, c_1343, c_1297, c_1343, c_1297, c_2096, c_3615])).
% 8.78/3.13  tff(c_3631, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_3629])).
% 8.78/3.13  tff(c_3632, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_420])).
% 8.78/3.13  tff(c_7041, plain, (~v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7032, c_3632])).
% 8.78/3.13  tff(c_7052, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_3725, c_3726, c_4563, c_4517, c_4563, c_4517, c_5316, c_7041])).
% 8.78/3.13  tff(c_7054, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_7052])).
% 8.78/3.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.78/3.13  
% 8.78/3.13  Inference rules
% 8.78/3.13  ----------------------
% 8.78/3.13  #Ref     : 0
% 8.78/3.13  #Sup     : 1418
% 8.78/3.13  #Fact    : 0
% 8.78/3.13  #Define  : 0
% 8.78/3.13  #Split   : 38
% 8.78/3.13  #Chain   : 0
% 8.78/3.13  #Close   : 0
% 8.78/3.13  
% 8.78/3.13  Ordering : KBO
% 8.78/3.13  
% 8.78/3.13  Simplification rules
% 8.78/3.13  ----------------------
% 8.78/3.13  #Subsume      : 235
% 8.78/3.13  #Demod        : 864
% 8.78/3.13  #Tautology    : 626
% 8.78/3.13  #SimpNegUnit  : 309
% 8.78/3.13  #BackRed      : 12
% 8.78/3.13  
% 8.78/3.13  #Partial instantiations: 0
% 8.78/3.13  #Strategies tried      : 1
% 8.78/3.13  
% 8.78/3.13  Timing (in seconds)
% 8.78/3.13  ----------------------
% 8.78/3.13  Preprocessing        : 0.44
% 8.78/3.13  Parsing              : 0.21
% 8.78/3.13  CNF conversion       : 0.06
% 8.78/3.13  Main loop            : 1.88
% 8.78/3.13  Inferencing          : 0.69
% 8.78/3.13  Reduction            : 0.61
% 8.78/3.13  Demodulation         : 0.43
% 8.78/3.13  BG Simplification    : 0.06
% 8.78/3.13  Subsumption          : 0.39
% 8.78/3.13  Abstraction          : 0.07
% 8.78/3.13  MUC search           : 0.00
% 8.78/3.13  Cooper               : 0.00
% 8.78/3.13  Total                : 2.39
% 8.78/3.13  Index Insertion      : 0.00
% 8.78/3.13  Index Deletion       : 0.00
% 8.78/3.13  Index Matching       : 0.00
% 8.78/3.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
