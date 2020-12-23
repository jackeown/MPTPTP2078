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
% DateTime   : Thu Dec  3 10:26:09 EST 2020

% Result     : Theorem 8.08s
% Output     : CNFRefutation 8.37s
% Verified   : 
% Statistics : Number of formulae       :  257 ( 838 expanded)
%              Number of leaves         :   43 ( 312 expanded)
%              Depth                    :   13
%              Number of atoms          :  813 (4324 expanded)
%              Number of equality atoms :  159 ( 770 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal term depth       :    4 (   1 average)

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

tff(f_231,negated_conjecture,(
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

tff(f_59,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
       => r1_subset_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_subset_1)).

tff(f_189,axiom,(
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

tff(f_107,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_155,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_60,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( r1_xboole_0(A_14,B_15)
      | ~ r1_subset_1(A_14,B_15)
      | v1_xboole_0(B_15)
      | v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_125,plain,(
    ! [C_228,A_229,B_230] :
      ( v1_relat_1(C_228)
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1(A_229,B_230))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_133,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_125])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_1154,plain,(
    ! [C_340,A_341,B_342] :
      ( v4_relat_1(C_340,A_341)
      | ~ m1_subset_1(C_340,k1_zfmisc_1(k2_zfmisc_1(A_341,B_342))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1162,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_1154])).

tff(c_3308,plain,(
    ! [B_689,A_690] :
      ( k1_relat_1(B_689) = A_690
      | ~ v1_partfun1(B_689,A_690)
      | ~ v4_relat_1(B_689,A_690)
      | ~ v1_relat_1(B_689) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_3311,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1162,c_3308])).

tff(c_3317,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_3311])).

tff(c_3321,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3317])).

tff(c_52,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_50,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_3721,plain,(
    ! [C_730,A_731,B_732] :
      ( v1_partfun1(C_730,A_731)
      | ~ v1_funct_2(C_730,A_731,B_732)
      | ~ v1_funct_1(C_730)
      | ~ m1_subset_1(C_730,k1_zfmisc_1(k2_zfmisc_1(A_731,B_732)))
      | v1_xboole_0(B_732) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_3727,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_3721])).

tff(c_3734,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_3727])).

tff(c_3736,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_3321,c_3734])).

tff(c_3737,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3317])).

tff(c_8,plain,(
    ! [A_9,B_11] :
      ( k7_relat_1(A_9,B_11) = k1_xboole_0
      | ~ r1_xboole_0(B_11,k1_relat_1(A_9))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3745,plain,(
    ! [B_11] :
      ( k7_relat_1('#skF_6',B_11) = k1_xboole_0
      | ~ r1_xboole_0(B_11,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3737,c_8])).

tff(c_4053,plain,(
    ! [B_759] :
      ( k7_relat_1('#skF_6',B_759) = k1_xboole_0
      | ~ r1_xboole_0(B_759,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_3745])).

tff(c_4057,plain,(
    ! [A_14] :
      ( k7_relat_1('#skF_6',A_14) = k1_xboole_0
      | ~ r1_subset_1(A_14,'#skF_4')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_14) ) ),
    inference(resolution,[status(thm)],[c_14,c_4053])).

tff(c_4208,plain,(
    ! [A_767] :
      ( k7_relat_1('#skF_6',A_767) = k1_xboole_0
      | ~ r1_subset_1(A_767,'#skF_4')
      | v1_xboole_0(A_767) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_4057])).

tff(c_4211,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_4208])).

tff(c_4214,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_4211])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_3753,plain,(
    ! [B_733,A_734] :
      ( k7_relat_1(B_733,k3_xboole_0(k1_relat_1(B_733),A_734)) = k7_relat_1(B_733,A_734)
      | ~ v1_relat_1(B_733) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3762,plain,(
    ! [A_734] :
      ( k7_relat_1('#skF_6',k3_xboole_0('#skF_4',A_734)) = k7_relat_1('#skF_6',A_734)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3737,c_3753])).

tff(c_4087,plain,(
    ! [A_762] : k7_relat_1('#skF_6',k3_xboole_0('#skF_4',A_762)) = k7_relat_1('#skF_6',A_762) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_3762])).

tff(c_4097,plain,(
    ! [B_2] : k7_relat_1('#skF_6',k3_xboole_0(B_2,'#skF_4')) = k7_relat_1('#skF_6',B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4087])).

tff(c_3295,plain,(
    ! [A_686,B_687,C_688] :
      ( k9_subset_1(A_686,B_687,C_688) = k3_xboole_0(B_687,C_688)
      | ~ m1_subset_1(C_688,k1_zfmisc_1(A_686)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3307,plain,(
    ! [B_687] : k9_subset_1('#skF_1',B_687,'#skF_4') = k3_xboole_0(B_687,'#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_3295])).

tff(c_3284,plain,(
    ! [B_684,A_685] :
      ( r1_subset_1(B_684,A_685)
      | ~ r1_subset_1(A_685,B_684)
      | v1_xboole_0(B_684)
      | v1_xboole_0(A_685) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3286,plain,
    ( r1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_3284])).

tff(c_3289,plain,(
    r1_subset_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_64,c_3286])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_132,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_125])).

tff(c_1161,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_1154])).

tff(c_3314,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1161,c_3308])).

tff(c_3320,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_3314])).

tff(c_3776,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_3320])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_56,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_3987,plain,(
    ! [C_753,A_754,B_755] :
      ( v1_partfun1(C_753,A_754)
      | ~ v1_funct_2(C_753,A_754,B_755)
      | ~ v1_funct_1(C_753)
      | ~ m1_subset_1(C_753,k1_zfmisc_1(k2_zfmisc_1(A_754,B_755)))
      | v1_xboole_0(B_755) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_3990,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_3987])).

tff(c_3996,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_3990])).

tff(c_3998,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_3776,c_3996])).

tff(c_3999,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3320])).

tff(c_4010,plain,(
    ! [B_11] :
      ( k7_relat_1('#skF_5',B_11) = k1_xboole_0
      | ~ r1_xboole_0(B_11,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3999,c_8])).

tff(c_4045,plain,(
    ! [B_758] :
      ( k7_relat_1('#skF_5',B_758) = k1_xboole_0
      | ~ r1_xboole_0(B_758,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_4010])).

tff(c_4049,plain,(
    ! [A_14] :
      ( k7_relat_1('#skF_5',A_14) = k1_xboole_0
      | ~ r1_subset_1(A_14,'#skF_3')
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_14) ) ),
    inference(resolution,[status(thm)],[c_14,c_4045])).

tff(c_4197,plain,(
    ! [A_766] :
      ( k7_relat_1('#skF_5',A_766) = k1_xboole_0
      | ~ r1_subset_1(A_766,'#skF_3')
      | v1_xboole_0(A_766) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_4049])).

tff(c_4200,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_3289,c_4197])).

tff(c_4203,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_4200])).

tff(c_10,plain,(
    ! [B_13,A_12] :
      ( k7_relat_1(B_13,k3_xboole_0(k1_relat_1(B_13),A_12)) = k7_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4004,plain,(
    ! [A_12] :
      ( k7_relat_1('#skF_5',k3_xboole_0('#skF_3',A_12)) = k7_relat_1('#skF_5',A_12)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3999,c_10])).

tff(c_4014,plain,(
    ! [A_12] : k7_relat_1('#skF_5',k3_xboole_0('#skF_3',A_12)) = k7_relat_1('#skF_5',A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_4004])).

tff(c_4366,plain,(
    ! [D_782,E_785,F_786,B_781,A_784,C_783] :
      ( v1_funct_1(k1_tmap_1(A_784,B_781,C_783,D_782,E_785,F_786))
      | ~ m1_subset_1(F_786,k1_zfmisc_1(k2_zfmisc_1(D_782,B_781)))
      | ~ v1_funct_2(F_786,D_782,B_781)
      | ~ v1_funct_1(F_786)
      | ~ m1_subset_1(E_785,k1_zfmisc_1(k2_zfmisc_1(C_783,B_781)))
      | ~ v1_funct_2(E_785,C_783,B_781)
      | ~ v1_funct_1(E_785)
      | ~ m1_subset_1(D_782,k1_zfmisc_1(A_784))
      | v1_xboole_0(D_782)
      | ~ m1_subset_1(C_783,k1_zfmisc_1(A_784))
      | v1_xboole_0(C_783)
      | v1_xboole_0(B_781)
      | v1_xboole_0(A_784) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_4370,plain,(
    ! [A_784,C_783,E_785] :
      ( v1_funct_1(k1_tmap_1(A_784,'#skF_2',C_783,'#skF_4',E_785,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_785,k1_zfmisc_1(k2_zfmisc_1(C_783,'#skF_2')))
      | ~ v1_funct_2(E_785,C_783,'#skF_2')
      | ~ v1_funct_1(E_785)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_784))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_783,k1_zfmisc_1(A_784))
      | v1_xboole_0(C_783)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_784) ) ),
    inference(resolution,[status(thm)],[c_48,c_4366])).

tff(c_4377,plain,(
    ! [A_784,C_783,E_785] :
      ( v1_funct_1(k1_tmap_1(A_784,'#skF_2',C_783,'#skF_4',E_785,'#skF_6'))
      | ~ m1_subset_1(E_785,k1_zfmisc_1(k2_zfmisc_1(C_783,'#skF_2')))
      | ~ v1_funct_2(E_785,C_783,'#skF_2')
      | ~ v1_funct_1(E_785)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_784))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_783,k1_zfmisc_1(A_784))
      | v1_xboole_0(C_783)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_784) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_4370])).

tff(c_4408,plain,(
    ! [A_798,C_799,E_800] :
      ( v1_funct_1(k1_tmap_1(A_798,'#skF_2',C_799,'#skF_4',E_800,'#skF_6'))
      | ~ m1_subset_1(E_800,k1_zfmisc_1(k2_zfmisc_1(C_799,'#skF_2')))
      | ~ v1_funct_2(E_800,C_799,'#skF_2')
      | ~ v1_funct_1(E_800)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_798))
      | ~ m1_subset_1(C_799,k1_zfmisc_1(A_798))
      | v1_xboole_0(C_799)
      | v1_xboole_0(A_798) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_4377])).

tff(c_4410,plain,(
    ! [A_798] :
      ( v1_funct_1(k1_tmap_1(A_798,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_798))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_798))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_798) ) ),
    inference(resolution,[status(thm)],[c_54,c_4408])).

tff(c_4415,plain,(
    ! [A_798] :
      ( v1_funct_1(k1_tmap_1(A_798,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_798))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_798))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_798) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_4410])).

tff(c_4428,plain,(
    ! [A_802] :
      ( v1_funct_1(k1_tmap_1(A_802,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_802))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_802))
      | v1_xboole_0(A_802) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_4415])).

tff(c_4431,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_4428])).

tff(c_4434,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_4431])).

tff(c_4435,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_4434])).

tff(c_4297,plain,(
    ! [A_772,B_773,C_774,D_775] :
      ( k2_partfun1(A_772,B_773,C_774,D_775) = k7_relat_1(C_774,D_775)
      | ~ m1_subset_1(C_774,k1_zfmisc_1(k2_zfmisc_1(A_772,B_773)))
      | ~ v1_funct_1(C_774) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_4299,plain,(
    ! [D_775] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_775) = k7_relat_1('#skF_5',D_775)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_4297])).

tff(c_4304,plain,(
    ! [D_775] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_775) = k7_relat_1('#skF_5',D_775) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_4299])).

tff(c_4301,plain,(
    ! [D_775] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_775) = k7_relat_1('#skF_6',D_775)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_48,c_4297])).

tff(c_4307,plain,(
    ! [D_775] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_775) = k7_relat_1('#skF_6',D_775) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_4301])).

tff(c_42,plain,(
    ! [E_165,C_163,F_166,A_161,B_162,D_164] :
      ( v1_funct_2(k1_tmap_1(A_161,B_162,C_163,D_164,E_165,F_166),k4_subset_1(A_161,C_163,D_164),B_162)
      | ~ m1_subset_1(F_166,k1_zfmisc_1(k2_zfmisc_1(D_164,B_162)))
      | ~ v1_funct_2(F_166,D_164,B_162)
      | ~ v1_funct_1(F_166)
      | ~ m1_subset_1(E_165,k1_zfmisc_1(k2_zfmisc_1(C_163,B_162)))
      | ~ v1_funct_2(E_165,C_163,B_162)
      | ~ v1_funct_1(E_165)
      | ~ m1_subset_1(D_164,k1_zfmisc_1(A_161))
      | v1_xboole_0(D_164)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(A_161))
      | v1_xboole_0(C_163)
      | v1_xboole_0(B_162)
      | v1_xboole_0(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_40,plain,(
    ! [E_165,C_163,F_166,A_161,B_162,D_164] :
      ( m1_subset_1(k1_tmap_1(A_161,B_162,C_163,D_164,E_165,F_166),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_161,C_163,D_164),B_162)))
      | ~ m1_subset_1(F_166,k1_zfmisc_1(k2_zfmisc_1(D_164,B_162)))
      | ~ v1_funct_2(F_166,D_164,B_162)
      | ~ v1_funct_1(F_166)
      | ~ m1_subset_1(E_165,k1_zfmisc_1(k2_zfmisc_1(C_163,B_162)))
      | ~ v1_funct_2(E_165,C_163,B_162)
      | ~ v1_funct_1(E_165)
      | ~ m1_subset_1(D_164,k1_zfmisc_1(A_161))
      | v1_xboole_0(D_164)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(A_161))
      | v1_xboole_0(C_163)
      | v1_xboole_0(B_162)
      | v1_xboole_0(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_4558,plain,(
    ! [D_835,B_833,E_834,C_831,F_832,A_830] :
      ( k2_partfun1(k4_subset_1(A_830,C_831,D_835),B_833,k1_tmap_1(A_830,B_833,C_831,D_835,E_834,F_832),C_831) = E_834
      | ~ m1_subset_1(k1_tmap_1(A_830,B_833,C_831,D_835,E_834,F_832),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_830,C_831,D_835),B_833)))
      | ~ v1_funct_2(k1_tmap_1(A_830,B_833,C_831,D_835,E_834,F_832),k4_subset_1(A_830,C_831,D_835),B_833)
      | ~ v1_funct_1(k1_tmap_1(A_830,B_833,C_831,D_835,E_834,F_832))
      | k2_partfun1(D_835,B_833,F_832,k9_subset_1(A_830,C_831,D_835)) != k2_partfun1(C_831,B_833,E_834,k9_subset_1(A_830,C_831,D_835))
      | ~ m1_subset_1(F_832,k1_zfmisc_1(k2_zfmisc_1(D_835,B_833)))
      | ~ v1_funct_2(F_832,D_835,B_833)
      | ~ v1_funct_1(F_832)
      | ~ m1_subset_1(E_834,k1_zfmisc_1(k2_zfmisc_1(C_831,B_833)))
      | ~ v1_funct_2(E_834,C_831,B_833)
      | ~ v1_funct_1(E_834)
      | ~ m1_subset_1(D_835,k1_zfmisc_1(A_830))
      | v1_xboole_0(D_835)
      | ~ m1_subset_1(C_831,k1_zfmisc_1(A_830))
      | v1_xboole_0(C_831)
      | v1_xboole_0(B_833)
      | v1_xboole_0(A_830) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_4993,plain,(
    ! [C_949,F_952,A_950,D_948,B_947,E_951] :
      ( k2_partfun1(k4_subset_1(A_950,C_949,D_948),B_947,k1_tmap_1(A_950,B_947,C_949,D_948,E_951,F_952),C_949) = E_951
      | ~ v1_funct_2(k1_tmap_1(A_950,B_947,C_949,D_948,E_951,F_952),k4_subset_1(A_950,C_949,D_948),B_947)
      | ~ v1_funct_1(k1_tmap_1(A_950,B_947,C_949,D_948,E_951,F_952))
      | k2_partfun1(D_948,B_947,F_952,k9_subset_1(A_950,C_949,D_948)) != k2_partfun1(C_949,B_947,E_951,k9_subset_1(A_950,C_949,D_948))
      | ~ m1_subset_1(F_952,k1_zfmisc_1(k2_zfmisc_1(D_948,B_947)))
      | ~ v1_funct_2(F_952,D_948,B_947)
      | ~ v1_funct_1(F_952)
      | ~ m1_subset_1(E_951,k1_zfmisc_1(k2_zfmisc_1(C_949,B_947)))
      | ~ v1_funct_2(E_951,C_949,B_947)
      | ~ v1_funct_1(E_951)
      | ~ m1_subset_1(D_948,k1_zfmisc_1(A_950))
      | v1_xboole_0(D_948)
      | ~ m1_subset_1(C_949,k1_zfmisc_1(A_950))
      | v1_xboole_0(C_949)
      | v1_xboole_0(B_947)
      | v1_xboole_0(A_950) ) ),
    inference(resolution,[status(thm)],[c_40,c_4558])).

tff(c_5311,plain,(
    ! [D_991,F_995,C_992,A_993,B_990,E_994] :
      ( k2_partfun1(k4_subset_1(A_993,C_992,D_991),B_990,k1_tmap_1(A_993,B_990,C_992,D_991,E_994,F_995),C_992) = E_994
      | ~ v1_funct_1(k1_tmap_1(A_993,B_990,C_992,D_991,E_994,F_995))
      | k2_partfun1(D_991,B_990,F_995,k9_subset_1(A_993,C_992,D_991)) != k2_partfun1(C_992,B_990,E_994,k9_subset_1(A_993,C_992,D_991))
      | ~ m1_subset_1(F_995,k1_zfmisc_1(k2_zfmisc_1(D_991,B_990)))
      | ~ v1_funct_2(F_995,D_991,B_990)
      | ~ v1_funct_1(F_995)
      | ~ m1_subset_1(E_994,k1_zfmisc_1(k2_zfmisc_1(C_992,B_990)))
      | ~ v1_funct_2(E_994,C_992,B_990)
      | ~ v1_funct_1(E_994)
      | ~ m1_subset_1(D_991,k1_zfmisc_1(A_993))
      | v1_xboole_0(D_991)
      | ~ m1_subset_1(C_992,k1_zfmisc_1(A_993))
      | v1_xboole_0(C_992)
      | v1_xboole_0(B_990)
      | v1_xboole_0(A_993) ) ),
    inference(resolution,[status(thm)],[c_42,c_4993])).

tff(c_5317,plain,(
    ! [A_993,C_992,E_994] :
      ( k2_partfun1(k4_subset_1(A_993,C_992,'#skF_4'),'#skF_2',k1_tmap_1(A_993,'#skF_2',C_992,'#skF_4',E_994,'#skF_6'),C_992) = E_994
      | ~ v1_funct_1(k1_tmap_1(A_993,'#skF_2',C_992,'#skF_4',E_994,'#skF_6'))
      | k2_partfun1(C_992,'#skF_2',E_994,k9_subset_1(A_993,C_992,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_993,C_992,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_994,k1_zfmisc_1(k2_zfmisc_1(C_992,'#skF_2')))
      | ~ v1_funct_2(E_994,C_992,'#skF_2')
      | ~ v1_funct_1(E_994)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_993))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_992,k1_zfmisc_1(A_993))
      | v1_xboole_0(C_992)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_993) ) ),
    inference(resolution,[status(thm)],[c_48,c_5311])).

tff(c_5325,plain,(
    ! [A_993,C_992,E_994] :
      ( k2_partfun1(k4_subset_1(A_993,C_992,'#skF_4'),'#skF_2',k1_tmap_1(A_993,'#skF_2',C_992,'#skF_4',E_994,'#skF_6'),C_992) = E_994
      | ~ v1_funct_1(k1_tmap_1(A_993,'#skF_2',C_992,'#skF_4',E_994,'#skF_6'))
      | k2_partfun1(C_992,'#skF_2',E_994,k9_subset_1(A_993,C_992,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_993,C_992,'#skF_4'))
      | ~ m1_subset_1(E_994,k1_zfmisc_1(k2_zfmisc_1(C_992,'#skF_2')))
      | ~ v1_funct_2(E_994,C_992,'#skF_2')
      | ~ v1_funct_1(E_994)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_993))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_992,k1_zfmisc_1(A_993))
      | v1_xboole_0(C_992)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_993) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_4307,c_5317])).

tff(c_5477,plain,(
    ! [A_1016,C_1017,E_1018] :
      ( k2_partfun1(k4_subset_1(A_1016,C_1017,'#skF_4'),'#skF_2',k1_tmap_1(A_1016,'#skF_2',C_1017,'#skF_4',E_1018,'#skF_6'),C_1017) = E_1018
      | ~ v1_funct_1(k1_tmap_1(A_1016,'#skF_2',C_1017,'#skF_4',E_1018,'#skF_6'))
      | k2_partfun1(C_1017,'#skF_2',E_1018,k9_subset_1(A_1016,C_1017,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1016,C_1017,'#skF_4'))
      | ~ m1_subset_1(E_1018,k1_zfmisc_1(k2_zfmisc_1(C_1017,'#skF_2')))
      | ~ v1_funct_2(E_1018,C_1017,'#skF_2')
      | ~ v1_funct_1(E_1018)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1016))
      | ~ m1_subset_1(C_1017,k1_zfmisc_1(A_1016))
      | v1_xboole_0(C_1017)
      | v1_xboole_0(A_1016) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_5325])).

tff(c_5482,plain,(
    ! [A_1016] :
      ( k2_partfun1(k4_subset_1(A_1016,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1016,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1016,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1016,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1016,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1016))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1016))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1016) ) ),
    inference(resolution,[status(thm)],[c_54,c_5477])).

tff(c_5490,plain,(
    ! [A_1016] :
      ( k2_partfun1(k4_subset_1(A_1016,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1016,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1016,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1016,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1016,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1016))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1016))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1016) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_4304,c_5482])).

tff(c_5544,plain,(
    ! [A_1031] :
      ( k2_partfun1(k4_subset_1(A_1031,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1031,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1031,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1031,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1031,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1031))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1031))
      | v1_xboole_0(A_1031) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_5490])).

tff(c_1210,plain,(
    ! [B_358,A_359] :
      ( k1_relat_1(B_358) = A_359
      | ~ v1_partfun1(B_358,A_359)
      | ~ v4_relat_1(B_358,A_359)
      | ~ v1_relat_1(B_358) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1213,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1162,c_1210])).

tff(c_1219,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_1213])).

tff(c_1223,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1219])).

tff(c_1580,plain,(
    ! [C_397,A_398,B_399] :
      ( v1_partfun1(C_397,A_398)
      | ~ v1_funct_2(C_397,A_398,B_399)
      | ~ v1_funct_1(C_397)
      | ~ m1_subset_1(C_397,k1_zfmisc_1(k2_zfmisc_1(A_398,B_399)))
      | v1_xboole_0(B_399) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1586,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_1580])).

tff(c_1593,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1586])).

tff(c_1595,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1223,c_1593])).

tff(c_1596,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1219])).

tff(c_1604,plain,(
    ! [B_11] :
      ( k7_relat_1('#skF_6',B_11) = k1_xboole_0
      | ~ r1_xboole_0(B_11,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1596,c_8])).

tff(c_1909,plain,(
    ! [B_426] :
      ( k7_relat_1('#skF_6',B_426) = k1_xboole_0
      | ~ r1_xboole_0(B_426,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_1604])).

tff(c_1913,plain,(
    ! [A_14] :
      ( k7_relat_1('#skF_6',A_14) = k1_xboole_0
      | ~ r1_subset_1(A_14,'#skF_4')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_14) ) ),
    inference(resolution,[status(thm)],[c_14,c_1909])).

tff(c_2061,plain,(
    ! [A_434] :
      ( k7_relat_1('#skF_6',A_434) = k1_xboole_0
      | ~ r1_subset_1(A_434,'#skF_4')
      | v1_xboole_0(A_434) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1913])).

tff(c_2064,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_2061])).

tff(c_2067,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2064])).

tff(c_1871,plain,(
    ! [B_423,A_424] :
      ( k7_relat_1(B_423,k3_xboole_0(k1_relat_1(B_423),A_424)) = k7_relat_1(B_423,A_424)
      | ~ v1_relat_1(B_423) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1883,plain,(
    ! [A_424] :
      ( k7_relat_1('#skF_6',k3_xboole_0('#skF_4',A_424)) = k7_relat_1('#skF_6',A_424)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1596,c_1871])).

tff(c_1951,plain,(
    ! [A_430] : k7_relat_1('#skF_6',k3_xboole_0('#skF_4',A_430)) = k7_relat_1('#skF_6',A_430) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_1883])).

tff(c_1961,plain,(
    ! [B_2] : k7_relat_1('#skF_6',k3_xboole_0(B_2,'#skF_4')) = k7_relat_1('#skF_6',B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1951])).

tff(c_1197,plain,(
    ! [A_355,B_356,C_357] :
      ( k9_subset_1(A_355,B_356,C_357) = k3_xboole_0(B_356,C_357)
      | ~ m1_subset_1(C_357,k1_zfmisc_1(A_355)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1209,plain,(
    ! [B_356] : k9_subset_1('#skF_1',B_356,'#skF_4') = k3_xboole_0(B_356,'#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_1197])).

tff(c_1186,plain,(
    ! [B_353,A_354] :
      ( r1_subset_1(B_353,A_354)
      | ~ r1_subset_1(A_354,B_353)
      | v1_xboole_0(B_353)
      | v1_xboole_0(A_354) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1188,plain,
    ( r1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_1186])).

tff(c_1191,plain,(
    r1_subset_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_64,c_1188])).

tff(c_1216,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1161,c_1210])).

tff(c_1222,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_1216])).

tff(c_1622,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1222])).

tff(c_1842,plain,(
    ! [C_420,A_421,B_422] :
      ( v1_partfun1(C_420,A_421)
      | ~ v1_funct_2(C_420,A_421,B_422)
      | ~ v1_funct_1(C_420)
      | ~ m1_subset_1(C_420,k1_zfmisc_1(k2_zfmisc_1(A_421,B_422)))
      | v1_xboole_0(B_422) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1845,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_1842])).

tff(c_1851,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1845])).

tff(c_1853,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1622,c_1851])).

tff(c_1854,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1222])).

tff(c_1862,plain,(
    ! [B_11] :
      ( k7_relat_1('#skF_5',B_11) = k1_xboole_0
      | ~ r1_xboole_0(B_11,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1854,c_8])).

tff(c_1917,plain,(
    ! [B_427] :
      ( k7_relat_1('#skF_5',B_427) = k1_xboole_0
      | ~ r1_xboole_0(B_427,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_1862])).

tff(c_1921,plain,(
    ! [A_14] :
      ( k7_relat_1('#skF_5',A_14) = k1_xboole_0
      | ~ r1_subset_1(A_14,'#skF_3')
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_14) ) ),
    inference(resolution,[status(thm)],[c_14,c_1917])).

tff(c_2072,plain,(
    ! [A_435] :
      ( k7_relat_1('#skF_5',A_435) = k1_xboole_0
      | ~ r1_subset_1(A_435,'#skF_3')
      | v1_xboole_0(A_435) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1921])).

tff(c_2075,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1191,c_2072])).

tff(c_2078,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2075])).

tff(c_1880,plain,(
    ! [A_424] :
      ( k7_relat_1('#skF_5',k3_xboole_0('#skF_3',A_424)) = k7_relat_1('#skF_5',A_424)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1854,c_1871])).

tff(c_1895,plain,(
    ! [A_424] : k7_relat_1('#skF_5',k3_xboole_0('#skF_3',A_424)) = k7_relat_1('#skF_5',A_424) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_1880])).

tff(c_2230,plain,(
    ! [B_449,E_453,A_452,F_454,D_450,C_451] :
      ( v1_funct_1(k1_tmap_1(A_452,B_449,C_451,D_450,E_453,F_454))
      | ~ m1_subset_1(F_454,k1_zfmisc_1(k2_zfmisc_1(D_450,B_449)))
      | ~ v1_funct_2(F_454,D_450,B_449)
      | ~ v1_funct_1(F_454)
      | ~ m1_subset_1(E_453,k1_zfmisc_1(k2_zfmisc_1(C_451,B_449)))
      | ~ v1_funct_2(E_453,C_451,B_449)
      | ~ v1_funct_1(E_453)
      | ~ m1_subset_1(D_450,k1_zfmisc_1(A_452))
      | v1_xboole_0(D_450)
      | ~ m1_subset_1(C_451,k1_zfmisc_1(A_452))
      | v1_xboole_0(C_451)
      | v1_xboole_0(B_449)
      | v1_xboole_0(A_452) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_2234,plain,(
    ! [A_452,C_451,E_453] :
      ( v1_funct_1(k1_tmap_1(A_452,'#skF_2',C_451,'#skF_4',E_453,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_453,k1_zfmisc_1(k2_zfmisc_1(C_451,'#skF_2')))
      | ~ v1_funct_2(E_453,C_451,'#skF_2')
      | ~ v1_funct_1(E_453)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_452))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_451,k1_zfmisc_1(A_452))
      | v1_xboole_0(C_451)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_452) ) ),
    inference(resolution,[status(thm)],[c_48,c_2230])).

tff(c_2241,plain,(
    ! [A_452,C_451,E_453] :
      ( v1_funct_1(k1_tmap_1(A_452,'#skF_2',C_451,'#skF_4',E_453,'#skF_6'))
      | ~ m1_subset_1(E_453,k1_zfmisc_1(k2_zfmisc_1(C_451,'#skF_2')))
      | ~ v1_funct_2(E_453,C_451,'#skF_2')
      | ~ v1_funct_1(E_453)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_452))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_451,k1_zfmisc_1(A_452))
      | v1_xboole_0(C_451)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_452) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_2234])).

tff(c_2272,plain,(
    ! [A_466,C_467,E_468] :
      ( v1_funct_1(k1_tmap_1(A_466,'#skF_2',C_467,'#skF_4',E_468,'#skF_6'))
      | ~ m1_subset_1(E_468,k1_zfmisc_1(k2_zfmisc_1(C_467,'#skF_2')))
      | ~ v1_funct_2(E_468,C_467,'#skF_2')
      | ~ v1_funct_1(E_468)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_466))
      | ~ m1_subset_1(C_467,k1_zfmisc_1(A_466))
      | v1_xboole_0(C_467)
      | v1_xboole_0(A_466) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_2241])).

tff(c_2274,plain,(
    ! [A_466] :
      ( v1_funct_1(k1_tmap_1(A_466,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_466))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_466))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_466) ) ),
    inference(resolution,[status(thm)],[c_54,c_2272])).

tff(c_2279,plain,(
    ! [A_466] :
      ( v1_funct_1(k1_tmap_1(A_466,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_466))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_466))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_466) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_2274])).

tff(c_2292,plain,(
    ! [A_470] :
      ( v1_funct_1(k1_tmap_1(A_470,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_470))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_470))
      | v1_xboole_0(A_470) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2279])).

tff(c_2295,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_2292])).

tff(c_2298,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2295])).

tff(c_2299,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2298])).

tff(c_2148,plain,(
    ! [A_438,B_439,C_440,D_441] :
      ( k2_partfun1(A_438,B_439,C_440,D_441) = k7_relat_1(C_440,D_441)
      | ~ m1_subset_1(C_440,k1_zfmisc_1(k2_zfmisc_1(A_438,B_439)))
      | ~ v1_funct_1(C_440) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2150,plain,(
    ! [D_441] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_441) = k7_relat_1('#skF_5',D_441)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_2148])).

tff(c_2155,plain,(
    ! [D_441] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_441) = k7_relat_1('#skF_5',D_441) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2150])).

tff(c_2152,plain,(
    ! [D_441] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_441) = k7_relat_1('#skF_6',D_441)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_48,c_2148])).

tff(c_2158,plain,(
    ! [D_441] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_441) = k7_relat_1('#skF_6',D_441) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2152])).

tff(c_2488,plain,(
    ! [E_519,B_518,A_515,F_517,C_516,D_520] :
      ( k2_partfun1(k4_subset_1(A_515,C_516,D_520),B_518,k1_tmap_1(A_515,B_518,C_516,D_520,E_519,F_517),D_520) = F_517
      | ~ m1_subset_1(k1_tmap_1(A_515,B_518,C_516,D_520,E_519,F_517),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_515,C_516,D_520),B_518)))
      | ~ v1_funct_2(k1_tmap_1(A_515,B_518,C_516,D_520,E_519,F_517),k4_subset_1(A_515,C_516,D_520),B_518)
      | ~ v1_funct_1(k1_tmap_1(A_515,B_518,C_516,D_520,E_519,F_517))
      | k2_partfun1(D_520,B_518,F_517,k9_subset_1(A_515,C_516,D_520)) != k2_partfun1(C_516,B_518,E_519,k9_subset_1(A_515,C_516,D_520))
      | ~ m1_subset_1(F_517,k1_zfmisc_1(k2_zfmisc_1(D_520,B_518)))
      | ~ v1_funct_2(F_517,D_520,B_518)
      | ~ v1_funct_1(F_517)
      | ~ m1_subset_1(E_519,k1_zfmisc_1(k2_zfmisc_1(C_516,B_518)))
      | ~ v1_funct_2(E_519,C_516,B_518)
      | ~ v1_funct_1(E_519)
      | ~ m1_subset_1(D_520,k1_zfmisc_1(A_515))
      | v1_xboole_0(D_520)
      | ~ m1_subset_1(C_516,k1_zfmisc_1(A_515))
      | v1_xboole_0(C_516)
      | v1_xboole_0(B_518)
      | v1_xboole_0(A_515) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_2842,plain,(
    ! [C_623,D_622,E_625,F_626,B_621,A_624] :
      ( k2_partfun1(k4_subset_1(A_624,C_623,D_622),B_621,k1_tmap_1(A_624,B_621,C_623,D_622,E_625,F_626),D_622) = F_626
      | ~ v1_funct_2(k1_tmap_1(A_624,B_621,C_623,D_622,E_625,F_626),k4_subset_1(A_624,C_623,D_622),B_621)
      | ~ v1_funct_1(k1_tmap_1(A_624,B_621,C_623,D_622,E_625,F_626))
      | k2_partfun1(D_622,B_621,F_626,k9_subset_1(A_624,C_623,D_622)) != k2_partfun1(C_623,B_621,E_625,k9_subset_1(A_624,C_623,D_622))
      | ~ m1_subset_1(F_626,k1_zfmisc_1(k2_zfmisc_1(D_622,B_621)))
      | ~ v1_funct_2(F_626,D_622,B_621)
      | ~ v1_funct_1(F_626)
      | ~ m1_subset_1(E_625,k1_zfmisc_1(k2_zfmisc_1(C_623,B_621)))
      | ~ v1_funct_2(E_625,C_623,B_621)
      | ~ v1_funct_1(E_625)
      | ~ m1_subset_1(D_622,k1_zfmisc_1(A_624))
      | v1_xboole_0(D_622)
      | ~ m1_subset_1(C_623,k1_zfmisc_1(A_624))
      | v1_xboole_0(C_623)
      | v1_xboole_0(B_621)
      | v1_xboole_0(A_624) ) ),
    inference(resolution,[status(thm)],[c_40,c_2488])).

tff(c_3111,plain,(
    ! [E_659,D_656,B_655,C_657,F_660,A_658] :
      ( k2_partfun1(k4_subset_1(A_658,C_657,D_656),B_655,k1_tmap_1(A_658,B_655,C_657,D_656,E_659,F_660),D_656) = F_660
      | ~ v1_funct_1(k1_tmap_1(A_658,B_655,C_657,D_656,E_659,F_660))
      | k2_partfun1(D_656,B_655,F_660,k9_subset_1(A_658,C_657,D_656)) != k2_partfun1(C_657,B_655,E_659,k9_subset_1(A_658,C_657,D_656))
      | ~ m1_subset_1(F_660,k1_zfmisc_1(k2_zfmisc_1(D_656,B_655)))
      | ~ v1_funct_2(F_660,D_656,B_655)
      | ~ v1_funct_1(F_660)
      | ~ m1_subset_1(E_659,k1_zfmisc_1(k2_zfmisc_1(C_657,B_655)))
      | ~ v1_funct_2(E_659,C_657,B_655)
      | ~ v1_funct_1(E_659)
      | ~ m1_subset_1(D_656,k1_zfmisc_1(A_658))
      | v1_xboole_0(D_656)
      | ~ m1_subset_1(C_657,k1_zfmisc_1(A_658))
      | v1_xboole_0(C_657)
      | v1_xboole_0(B_655)
      | v1_xboole_0(A_658) ) ),
    inference(resolution,[status(thm)],[c_42,c_2842])).

tff(c_3117,plain,(
    ! [A_658,C_657,E_659] :
      ( k2_partfun1(k4_subset_1(A_658,C_657,'#skF_4'),'#skF_2',k1_tmap_1(A_658,'#skF_2',C_657,'#skF_4',E_659,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_658,'#skF_2',C_657,'#skF_4',E_659,'#skF_6'))
      | k2_partfun1(C_657,'#skF_2',E_659,k9_subset_1(A_658,C_657,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_658,C_657,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_659,k1_zfmisc_1(k2_zfmisc_1(C_657,'#skF_2')))
      | ~ v1_funct_2(E_659,C_657,'#skF_2')
      | ~ v1_funct_1(E_659)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_658))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_657,k1_zfmisc_1(A_658))
      | v1_xboole_0(C_657)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_658) ) ),
    inference(resolution,[status(thm)],[c_48,c_3111])).

tff(c_3125,plain,(
    ! [A_658,C_657,E_659] :
      ( k2_partfun1(k4_subset_1(A_658,C_657,'#skF_4'),'#skF_2',k1_tmap_1(A_658,'#skF_2',C_657,'#skF_4',E_659,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_658,'#skF_2',C_657,'#skF_4',E_659,'#skF_6'))
      | k2_partfun1(C_657,'#skF_2',E_659,k9_subset_1(A_658,C_657,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_658,C_657,'#skF_4'))
      | ~ m1_subset_1(E_659,k1_zfmisc_1(k2_zfmisc_1(C_657,'#skF_2')))
      | ~ v1_funct_2(E_659,C_657,'#skF_2')
      | ~ v1_funct_1(E_659)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_658))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_657,k1_zfmisc_1(A_658))
      | v1_xboole_0(C_657)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_658) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_2158,c_3117])).

tff(c_3130,plain,(
    ! [A_661,C_662,E_663] :
      ( k2_partfun1(k4_subset_1(A_661,C_662,'#skF_4'),'#skF_2',k1_tmap_1(A_661,'#skF_2',C_662,'#skF_4',E_663,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_661,'#skF_2',C_662,'#skF_4',E_663,'#skF_6'))
      | k2_partfun1(C_662,'#skF_2',E_663,k9_subset_1(A_661,C_662,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_661,C_662,'#skF_4'))
      | ~ m1_subset_1(E_663,k1_zfmisc_1(k2_zfmisc_1(C_662,'#skF_2')))
      | ~ v1_funct_2(E_663,C_662,'#skF_2')
      | ~ v1_funct_1(E_663)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_661))
      | ~ m1_subset_1(C_662,k1_zfmisc_1(A_661))
      | v1_xboole_0(C_662)
      | v1_xboole_0(A_661) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_3125])).

tff(c_3135,plain,(
    ! [A_661] :
      ( k2_partfun1(k4_subset_1(A_661,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_661,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_661,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_661,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_661,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_661))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_661))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_661) ) ),
    inference(resolution,[status(thm)],[c_54,c_3130])).

tff(c_3143,plain,(
    ! [A_661] :
      ( k2_partfun1(k4_subset_1(A_661,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_661,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_661,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_661,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_661,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_661))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_661))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_661) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_2155,c_3135])).

tff(c_3247,plain,(
    ! [A_680] :
      ( k2_partfun1(k4_subset_1(A_680,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_680,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_680,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_680,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_680,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_680))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_680))
      | v1_xboole_0(A_680) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3143])).

tff(c_146,plain,(
    ! [C_234,A_235,B_236] :
      ( v4_relat_1(C_234,A_235)
      | ~ m1_subset_1(C_234,k1_zfmisc_1(k2_zfmisc_1(A_235,B_236))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_154,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_146])).

tff(c_196,plain,(
    ! [B_248,A_249] :
      ( k1_relat_1(B_248) = A_249
      | ~ v1_partfun1(B_248,A_249)
      | ~ v4_relat_1(B_248,A_249)
      | ~ v1_relat_1(B_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_199,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_154,c_196])).

tff(c_205,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_199])).

tff(c_209,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_205])).

tff(c_556,plain,(
    ! [C_289,A_290,B_291] :
      ( v1_partfun1(C_289,A_290)
      | ~ v1_funct_2(C_289,A_290,B_291)
      | ~ v1_funct_1(C_289)
      | ~ m1_subset_1(C_289,k1_zfmisc_1(k2_zfmisc_1(A_290,B_291)))
      | v1_xboole_0(B_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_562,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_556])).

tff(c_569,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_562])).

tff(c_571,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_209,c_569])).

tff(c_572,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_205])).

tff(c_580,plain,(
    ! [B_11] :
      ( k7_relat_1('#skF_6',B_11) = k1_xboole_0
      | ~ r1_xboole_0(B_11,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_572,c_8])).

tff(c_841,plain,(
    ! [B_315] :
      ( k7_relat_1('#skF_6',B_315) = k1_xboole_0
      | ~ r1_xboole_0(B_315,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_580])).

tff(c_845,plain,(
    ! [A_14] :
      ( k7_relat_1('#skF_6',A_14) = k1_xboole_0
      | ~ r1_subset_1(A_14,'#skF_4')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_14) ) ),
    inference(resolution,[status(thm)],[c_14,c_841])).

tff(c_1058,plain,(
    ! [A_334] :
      ( k7_relat_1('#skF_6',A_334) = k1_xboole_0
      | ~ r1_subset_1(A_334,'#skF_4')
      | v1_xboole_0(A_334) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_845])).

tff(c_1061,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_1058])).

tff(c_1064,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1061])).

tff(c_156,plain,(
    ! [B_238,A_239] :
      ( r1_subset_1(B_238,A_239)
      | ~ r1_subset_1(A_239,B_238)
      | v1_xboole_0(B_238)
      | v1_xboole_0(A_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_158,plain,
    ( r1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_156])).

tff(c_161,plain,(
    r1_subset_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_64,c_158])).

tff(c_153,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_146])).

tff(c_202,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_153,c_196])).

tff(c_208,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_202])).

tff(c_594,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_208])).

tff(c_799,plain,(
    ! [C_311,A_312,B_313] :
      ( v1_partfun1(C_311,A_312)
      | ~ v1_funct_2(C_311,A_312,B_313)
      | ~ v1_funct_1(C_311)
      | ~ m1_subset_1(C_311,k1_zfmisc_1(k2_zfmisc_1(A_312,B_313)))
      | v1_xboole_0(B_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_802,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_799])).

tff(c_808,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_802])).

tff(c_810,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_594,c_808])).

tff(c_811,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_208])).

tff(c_819,plain,(
    ! [B_11] :
      ( k7_relat_1('#skF_5',B_11) = k1_xboole_0
      | ~ r1_xboole_0(B_11,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_811,c_8])).

tff(c_833,plain,(
    ! [B_314] :
      ( k7_relat_1('#skF_5',B_314) = k1_xboole_0
      | ~ r1_xboole_0(B_314,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_819])).

tff(c_837,plain,(
    ! [A_14] :
      ( k7_relat_1('#skF_5',A_14) = k1_xboole_0
      | ~ r1_subset_1(A_14,'#skF_3')
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_14) ) ),
    inference(resolution,[status(thm)],[c_14,c_833])).

tff(c_1047,plain,(
    ! [A_333] :
      ( k7_relat_1('#skF_5',A_333) = k1_xboole_0
      | ~ r1_subset_1(A_333,'#skF_3')
      | v1_xboole_0(A_333) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_837])).

tff(c_1050,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_161,c_1047])).

tff(c_1053,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1050])).

tff(c_577,plain,(
    ! [A_12] :
      ( k7_relat_1('#skF_6',k3_xboole_0('#skF_4',A_12)) = k7_relat_1('#skF_6',A_12)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_572,c_10])).

tff(c_587,plain,(
    ! [A_12] : k7_relat_1('#skF_6',k3_xboole_0('#skF_4',A_12)) = k7_relat_1('#skF_6',A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_577])).

tff(c_1009,plain,(
    ! [A_326,B_327,C_328,D_329] :
      ( k2_partfun1(A_326,B_327,C_328,D_329) = k7_relat_1(C_328,D_329)
      | ~ m1_subset_1(C_328,k1_zfmisc_1(k2_zfmisc_1(A_326,B_327)))
      | ~ v1_funct_1(C_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1013,plain,(
    ! [D_329] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_329) = k7_relat_1('#skF_6',D_329)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_48,c_1009])).

tff(c_1019,plain,(
    ! [D_329] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_329) = k7_relat_1('#skF_6',D_329) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1013])).

tff(c_816,plain,(
    ! [A_12] :
      ( k7_relat_1('#skF_5',k3_xboole_0('#skF_3',A_12)) = k7_relat_1('#skF_5',A_12)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_811,c_10])).

tff(c_882,plain,(
    ! [A_321] : k7_relat_1('#skF_5',k3_xboole_0('#skF_3',A_321)) = k7_relat_1('#skF_5',A_321) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_816])).

tff(c_896,plain,(
    ! [A_1] : k7_relat_1('#skF_5',k3_xboole_0(A_1,'#skF_3')) = k7_relat_1('#skF_5',A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_882])).

tff(c_1011,plain,(
    ! [D_329] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_329) = k7_relat_1('#skF_5',D_329)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_1009])).

tff(c_1016,plain,(
    ! [D_329] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_329) = k7_relat_1('#skF_5',D_329) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1011])).

tff(c_849,plain,(
    ! [A_316,B_317,C_318] :
      ( k9_subset_1(A_316,B_317,C_318) = k3_xboole_0(B_317,C_318)
      | ~ m1_subset_1(C_318,k1_zfmisc_1(A_316)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_861,plain,(
    ! [B_317] : k9_subset_1('#skF_1',B_317,'#skF_4') = k3_xboole_0(B_317,'#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_849])).

tff(c_46,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_135,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_871,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_861,c_861,c_135])).

tff(c_872,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_4','#skF_3')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_871])).

tff(c_1146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1064,c_1053,c_587,c_1019,c_896,c_1016,c_872])).

tff(c_1147,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1178,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1147])).

tff(c_3258,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3247,c_1178])).

tff(c_3272,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_2067,c_1961,c_1209,c_2078,c_1895,c_1209,c_2299,c_3258])).

tff(c_3274,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3272])).

tff(c_3275,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1147])).

tff(c_5553,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5544,c_3275])).

tff(c_5564,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_4214,c_4097,c_3307,c_4203,c_4014,c_3307,c_4435,c_5553])).

tff(c_5566,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_5564])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:34:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.08/2.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.08/2.70  
% 8.08/2.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.08/2.70  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.08/2.70  
% 8.08/2.70  %Foreground sorts:
% 8.08/2.70  
% 8.08/2.70  
% 8.08/2.70  %Background operators:
% 8.08/2.70  
% 8.08/2.70  
% 8.08/2.70  %Foreground operators:
% 8.08/2.70  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 8.08/2.70  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.08/2.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.08/2.70  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.08/2.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.08/2.70  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 8.08/2.70  tff('#skF_5', type, '#skF_5': $i).
% 8.08/2.70  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.08/2.70  tff('#skF_6', type, '#skF_6': $i).
% 8.08/2.70  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.08/2.70  tff('#skF_2', type, '#skF_2': $i).
% 8.08/2.70  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 8.08/2.70  tff('#skF_3', type, '#skF_3': $i).
% 8.08/2.70  tff('#skF_1', type, '#skF_1': $i).
% 8.08/2.70  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.08/2.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.08/2.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.08/2.70  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.08/2.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.08/2.70  tff('#skF_4', type, '#skF_4': $i).
% 8.08/2.70  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.08/2.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.08/2.70  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 8.08/2.70  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.08/2.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.08/2.70  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.08/2.70  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.08/2.70  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 8.08/2.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.08/2.70  
% 8.37/2.74  tff(f_231, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 8.37/2.74  tff(f_59, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 8.37/2.74  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.37/2.74  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.37/2.74  tff(f_101, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 8.37/2.74  tff(f_93, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 8.37/2.74  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 8.37/2.74  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.37/2.74  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 8.37/2.74  tff(f_31, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 8.37/2.74  tff(f_69, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) => r1_subset_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_subset_1)).
% 8.37/2.74  tff(f_189, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 8.37/2.74  tff(f_107, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 8.37/2.74  tff(f_155, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 8.37/2.74  tff(c_72, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.37/2.74  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.37/2.74  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.37/2.74  tff(c_68, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.37/2.74  tff(c_60, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.37/2.74  tff(c_64, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.37/2.74  tff(c_14, plain, (![A_14, B_15]: (r1_xboole_0(A_14, B_15) | ~r1_subset_1(A_14, B_15) | v1_xboole_0(B_15) | v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.37/2.74  tff(c_48, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.37/2.74  tff(c_125, plain, (![C_228, A_229, B_230]: (v1_relat_1(C_228) | ~m1_subset_1(C_228, k1_zfmisc_1(k2_zfmisc_1(A_229, B_230))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.37/2.74  tff(c_133, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_48, c_125])).
% 8.37/2.74  tff(c_70, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.37/2.74  tff(c_1154, plain, (![C_340, A_341, B_342]: (v4_relat_1(C_340, A_341) | ~m1_subset_1(C_340, k1_zfmisc_1(k2_zfmisc_1(A_341, B_342))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.37/2.74  tff(c_1162, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_48, c_1154])).
% 8.37/2.74  tff(c_3308, plain, (![B_689, A_690]: (k1_relat_1(B_689)=A_690 | ~v1_partfun1(B_689, A_690) | ~v4_relat_1(B_689, A_690) | ~v1_relat_1(B_689))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.37/2.74  tff(c_3311, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1162, c_3308])).
% 8.37/2.74  tff(c_3317, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_3311])).
% 8.37/2.74  tff(c_3321, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_3317])).
% 8.37/2.74  tff(c_52, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.37/2.74  tff(c_50, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.37/2.74  tff(c_3721, plain, (![C_730, A_731, B_732]: (v1_partfun1(C_730, A_731) | ~v1_funct_2(C_730, A_731, B_732) | ~v1_funct_1(C_730) | ~m1_subset_1(C_730, k1_zfmisc_1(k2_zfmisc_1(A_731, B_732))) | v1_xboole_0(B_732))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.37/2.74  tff(c_3727, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_3721])).
% 8.37/2.74  tff(c_3734, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_3727])).
% 8.37/2.74  tff(c_3736, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_3321, c_3734])).
% 8.37/2.74  tff(c_3737, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_3317])).
% 8.37/2.74  tff(c_8, plain, (![A_9, B_11]: (k7_relat_1(A_9, B_11)=k1_xboole_0 | ~r1_xboole_0(B_11, k1_relat_1(A_9)) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.37/2.74  tff(c_3745, plain, (![B_11]: (k7_relat_1('#skF_6', B_11)=k1_xboole_0 | ~r1_xboole_0(B_11, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3737, c_8])).
% 8.37/2.74  tff(c_4053, plain, (![B_759]: (k7_relat_1('#skF_6', B_759)=k1_xboole_0 | ~r1_xboole_0(B_759, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_3745])).
% 8.37/2.74  tff(c_4057, plain, (![A_14]: (k7_relat_1('#skF_6', A_14)=k1_xboole_0 | ~r1_subset_1(A_14, '#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(A_14))), inference(resolution, [status(thm)], [c_14, c_4053])).
% 8.37/2.74  tff(c_4208, plain, (![A_767]: (k7_relat_1('#skF_6', A_767)=k1_xboole_0 | ~r1_subset_1(A_767, '#skF_4') | v1_xboole_0(A_767))), inference(negUnitSimplification, [status(thm)], [c_64, c_4057])).
% 8.37/2.74  tff(c_4211, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_4208])).
% 8.37/2.74  tff(c_4214, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_68, c_4211])).
% 8.37/2.74  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.37/2.74  tff(c_3753, plain, (![B_733, A_734]: (k7_relat_1(B_733, k3_xboole_0(k1_relat_1(B_733), A_734))=k7_relat_1(B_733, A_734) | ~v1_relat_1(B_733))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.37/2.74  tff(c_3762, plain, (![A_734]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_4', A_734))=k7_relat_1('#skF_6', A_734) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3737, c_3753])).
% 8.37/2.74  tff(c_4087, plain, (![A_762]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_4', A_762))=k7_relat_1('#skF_6', A_762))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_3762])).
% 8.37/2.74  tff(c_4097, plain, (![B_2]: (k7_relat_1('#skF_6', k3_xboole_0(B_2, '#skF_4'))=k7_relat_1('#skF_6', B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_4087])).
% 8.37/2.74  tff(c_3295, plain, (![A_686, B_687, C_688]: (k9_subset_1(A_686, B_687, C_688)=k3_xboole_0(B_687, C_688) | ~m1_subset_1(C_688, k1_zfmisc_1(A_686)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.37/2.74  tff(c_3307, plain, (![B_687]: (k9_subset_1('#skF_1', B_687, '#skF_4')=k3_xboole_0(B_687, '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_3295])).
% 8.37/2.74  tff(c_3284, plain, (![B_684, A_685]: (r1_subset_1(B_684, A_685) | ~r1_subset_1(A_685, B_684) | v1_xboole_0(B_684) | v1_xboole_0(A_685))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.37/2.74  tff(c_3286, plain, (r1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_3284])).
% 8.37/2.74  tff(c_3289, plain, (r1_subset_1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_68, c_64, c_3286])).
% 8.37/2.74  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.37/2.74  tff(c_132, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_125])).
% 8.37/2.74  tff(c_1161, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_1154])).
% 8.37/2.74  tff(c_3314, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1161, c_3308])).
% 8.37/2.74  tff(c_3320, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_3314])).
% 8.37/2.74  tff(c_3776, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_3320])).
% 8.37/2.74  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.37/2.74  tff(c_56, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.37/2.74  tff(c_3987, plain, (![C_753, A_754, B_755]: (v1_partfun1(C_753, A_754) | ~v1_funct_2(C_753, A_754, B_755) | ~v1_funct_1(C_753) | ~m1_subset_1(C_753, k1_zfmisc_1(k2_zfmisc_1(A_754, B_755))) | v1_xboole_0(B_755))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.37/2.74  tff(c_3990, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_3987])).
% 8.37/2.74  tff(c_3996, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_3990])).
% 8.37/2.74  tff(c_3998, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_3776, c_3996])).
% 8.37/2.74  tff(c_3999, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_3320])).
% 8.37/2.74  tff(c_4010, plain, (![B_11]: (k7_relat_1('#skF_5', B_11)=k1_xboole_0 | ~r1_xboole_0(B_11, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3999, c_8])).
% 8.37/2.74  tff(c_4045, plain, (![B_758]: (k7_relat_1('#skF_5', B_758)=k1_xboole_0 | ~r1_xboole_0(B_758, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_4010])).
% 8.37/2.74  tff(c_4049, plain, (![A_14]: (k7_relat_1('#skF_5', A_14)=k1_xboole_0 | ~r1_subset_1(A_14, '#skF_3') | v1_xboole_0('#skF_3') | v1_xboole_0(A_14))), inference(resolution, [status(thm)], [c_14, c_4045])).
% 8.37/2.74  tff(c_4197, plain, (![A_766]: (k7_relat_1('#skF_5', A_766)=k1_xboole_0 | ~r1_subset_1(A_766, '#skF_3') | v1_xboole_0(A_766))), inference(negUnitSimplification, [status(thm)], [c_68, c_4049])).
% 8.37/2.74  tff(c_4200, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_3289, c_4197])).
% 8.37/2.74  tff(c_4203, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_64, c_4200])).
% 8.37/2.74  tff(c_10, plain, (![B_13, A_12]: (k7_relat_1(B_13, k3_xboole_0(k1_relat_1(B_13), A_12))=k7_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.37/2.74  tff(c_4004, plain, (![A_12]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', A_12))=k7_relat_1('#skF_5', A_12) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3999, c_10])).
% 8.37/2.74  tff(c_4014, plain, (![A_12]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', A_12))=k7_relat_1('#skF_5', A_12))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_4004])).
% 8.37/2.74  tff(c_4366, plain, (![D_782, E_785, F_786, B_781, A_784, C_783]: (v1_funct_1(k1_tmap_1(A_784, B_781, C_783, D_782, E_785, F_786)) | ~m1_subset_1(F_786, k1_zfmisc_1(k2_zfmisc_1(D_782, B_781))) | ~v1_funct_2(F_786, D_782, B_781) | ~v1_funct_1(F_786) | ~m1_subset_1(E_785, k1_zfmisc_1(k2_zfmisc_1(C_783, B_781))) | ~v1_funct_2(E_785, C_783, B_781) | ~v1_funct_1(E_785) | ~m1_subset_1(D_782, k1_zfmisc_1(A_784)) | v1_xboole_0(D_782) | ~m1_subset_1(C_783, k1_zfmisc_1(A_784)) | v1_xboole_0(C_783) | v1_xboole_0(B_781) | v1_xboole_0(A_784))), inference(cnfTransformation, [status(thm)], [f_189])).
% 8.37/2.74  tff(c_4370, plain, (![A_784, C_783, E_785]: (v1_funct_1(k1_tmap_1(A_784, '#skF_2', C_783, '#skF_4', E_785, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_785, k1_zfmisc_1(k2_zfmisc_1(C_783, '#skF_2'))) | ~v1_funct_2(E_785, C_783, '#skF_2') | ~v1_funct_1(E_785) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_784)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_783, k1_zfmisc_1(A_784)) | v1_xboole_0(C_783) | v1_xboole_0('#skF_2') | v1_xboole_0(A_784))), inference(resolution, [status(thm)], [c_48, c_4366])).
% 8.37/2.74  tff(c_4377, plain, (![A_784, C_783, E_785]: (v1_funct_1(k1_tmap_1(A_784, '#skF_2', C_783, '#skF_4', E_785, '#skF_6')) | ~m1_subset_1(E_785, k1_zfmisc_1(k2_zfmisc_1(C_783, '#skF_2'))) | ~v1_funct_2(E_785, C_783, '#skF_2') | ~v1_funct_1(E_785) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_784)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_783, k1_zfmisc_1(A_784)) | v1_xboole_0(C_783) | v1_xboole_0('#skF_2') | v1_xboole_0(A_784))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_4370])).
% 8.37/2.74  tff(c_4408, plain, (![A_798, C_799, E_800]: (v1_funct_1(k1_tmap_1(A_798, '#skF_2', C_799, '#skF_4', E_800, '#skF_6')) | ~m1_subset_1(E_800, k1_zfmisc_1(k2_zfmisc_1(C_799, '#skF_2'))) | ~v1_funct_2(E_800, C_799, '#skF_2') | ~v1_funct_1(E_800) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_798)) | ~m1_subset_1(C_799, k1_zfmisc_1(A_798)) | v1_xboole_0(C_799) | v1_xboole_0(A_798))), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_4377])).
% 8.37/2.74  tff(c_4410, plain, (![A_798]: (v1_funct_1(k1_tmap_1(A_798, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_798)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_798)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_798))), inference(resolution, [status(thm)], [c_54, c_4408])).
% 8.37/2.74  tff(c_4415, plain, (![A_798]: (v1_funct_1(k1_tmap_1(A_798, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_798)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_798)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_798))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_4410])).
% 8.37/2.74  tff(c_4428, plain, (![A_802]: (v1_funct_1(k1_tmap_1(A_802, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_802)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_802)) | v1_xboole_0(A_802))), inference(negUnitSimplification, [status(thm)], [c_68, c_4415])).
% 8.37/2.74  tff(c_4431, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_66, c_4428])).
% 8.37/2.74  tff(c_4434, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_4431])).
% 8.37/2.74  tff(c_4435, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_72, c_4434])).
% 8.37/2.74  tff(c_4297, plain, (![A_772, B_773, C_774, D_775]: (k2_partfun1(A_772, B_773, C_774, D_775)=k7_relat_1(C_774, D_775) | ~m1_subset_1(C_774, k1_zfmisc_1(k2_zfmisc_1(A_772, B_773))) | ~v1_funct_1(C_774))), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.37/2.74  tff(c_4299, plain, (![D_775]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_775)=k7_relat_1('#skF_5', D_775) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_4297])).
% 8.37/2.74  tff(c_4304, plain, (![D_775]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_775)=k7_relat_1('#skF_5', D_775))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_4299])).
% 8.37/2.74  tff(c_4301, plain, (![D_775]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_775)=k7_relat_1('#skF_6', D_775) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_48, c_4297])).
% 8.37/2.74  tff(c_4307, plain, (![D_775]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_775)=k7_relat_1('#skF_6', D_775))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_4301])).
% 8.37/2.74  tff(c_42, plain, (![E_165, C_163, F_166, A_161, B_162, D_164]: (v1_funct_2(k1_tmap_1(A_161, B_162, C_163, D_164, E_165, F_166), k4_subset_1(A_161, C_163, D_164), B_162) | ~m1_subset_1(F_166, k1_zfmisc_1(k2_zfmisc_1(D_164, B_162))) | ~v1_funct_2(F_166, D_164, B_162) | ~v1_funct_1(F_166) | ~m1_subset_1(E_165, k1_zfmisc_1(k2_zfmisc_1(C_163, B_162))) | ~v1_funct_2(E_165, C_163, B_162) | ~v1_funct_1(E_165) | ~m1_subset_1(D_164, k1_zfmisc_1(A_161)) | v1_xboole_0(D_164) | ~m1_subset_1(C_163, k1_zfmisc_1(A_161)) | v1_xboole_0(C_163) | v1_xboole_0(B_162) | v1_xboole_0(A_161))), inference(cnfTransformation, [status(thm)], [f_189])).
% 8.37/2.74  tff(c_40, plain, (![E_165, C_163, F_166, A_161, B_162, D_164]: (m1_subset_1(k1_tmap_1(A_161, B_162, C_163, D_164, E_165, F_166), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_161, C_163, D_164), B_162))) | ~m1_subset_1(F_166, k1_zfmisc_1(k2_zfmisc_1(D_164, B_162))) | ~v1_funct_2(F_166, D_164, B_162) | ~v1_funct_1(F_166) | ~m1_subset_1(E_165, k1_zfmisc_1(k2_zfmisc_1(C_163, B_162))) | ~v1_funct_2(E_165, C_163, B_162) | ~v1_funct_1(E_165) | ~m1_subset_1(D_164, k1_zfmisc_1(A_161)) | v1_xboole_0(D_164) | ~m1_subset_1(C_163, k1_zfmisc_1(A_161)) | v1_xboole_0(C_163) | v1_xboole_0(B_162) | v1_xboole_0(A_161))), inference(cnfTransformation, [status(thm)], [f_189])).
% 8.37/2.74  tff(c_4558, plain, (![D_835, B_833, E_834, C_831, F_832, A_830]: (k2_partfun1(k4_subset_1(A_830, C_831, D_835), B_833, k1_tmap_1(A_830, B_833, C_831, D_835, E_834, F_832), C_831)=E_834 | ~m1_subset_1(k1_tmap_1(A_830, B_833, C_831, D_835, E_834, F_832), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_830, C_831, D_835), B_833))) | ~v1_funct_2(k1_tmap_1(A_830, B_833, C_831, D_835, E_834, F_832), k4_subset_1(A_830, C_831, D_835), B_833) | ~v1_funct_1(k1_tmap_1(A_830, B_833, C_831, D_835, E_834, F_832)) | k2_partfun1(D_835, B_833, F_832, k9_subset_1(A_830, C_831, D_835))!=k2_partfun1(C_831, B_833, E_834, k9_subset_1(A_830, C_831, D_835)) | ~m1_subset_1(F_832, k1_zfmisc_1(k2_zfmisc_1(D_835, B_833))) | ~v1_funct_2(F_832, D_835, B_833) | ~v1_funct_1(F_832) | ~m1_subset_1(E_834, k1_zfmisc_1(k2_zfmisc_1(C_831, B_833))) | ~v1_funct_2(E_834, C_831, B_833) | ~v1_funct_1(E_834) | ~m1_subset_1(D_835, k1_zfmisc_1(A_830)) | v1_xboole_0(D_835) | ~m1_subset_1(C_831, k1_zfmisc_1(A_830)) | v1_xboole_0(C_831) | v1_xboole_0(B_833) | v1_xboole_0(A_830))), inference(cnfTransformation, [status(thm)], [f_155])).
% 8.37/2.74  tff(c_4993, plain, (![C_949, F_952, A_950, D_948, B_947, E_951]: (k2_partfun1(k4_subset_1(A_950, C_949, D_948), B_947, k1_tmap_1(A_950, B_947, C_949, D_948, E_951, F_952), C_949)=E_951 | ~v1_funct_2(k1_tmap_1(A_950, B_947, C_949, D_948, E_951, F_952), k4_subset_1(A_950, C_949, D_948), B_947) | ~v1_funct_1(k1_tmap_1(A_950, B_947, C_949, D_948, E_951, F_952)) | k2_partfun1(D_948, B_947, F_952, k9_subset_1(A_950, C_949, D_948))!=k2_partfun1(C_949, B_947, E_951, k9_subset_1(A_950, C_949, D_948)) | ~m1_subset_1(F_952, k1_zfmisc_1(k2_zfmisc_1(D_948, B_947))) | ~v1_funct_2(F_952, D_948, B_947) | ~v1_funct_1(F_952) | ~m1_subset_1(E_951, k1_zfmisc_1(k2_zfmisc_1(C_949, B_947))) | ~v1_funct_2(E_951, C_949, B_947) | ~v1_funct_1(E_951) | ~m1_subset_1(D_948, k1_zfmisc_1(A_950)) | v1_xboole_0(D_948) | ~m1_subset_1(C_949, k1_zfmisc_1(A_950)) | v1_xboole_0(C_949) | v1_xboole_0(B_947) | v1_xboole_0(A_950))), inference(resolution, [status(thm)], [c_40, c_4558])).
% 8.37/2.74  tff(c_5311, plain, (![D_991, F_995, C_992, A_993, B_990, E_994]: (k2_partfun1(k4_subset_1(A_993, C_992, D_991), B_990, k1_tmap_1(A_993, B_990, C_992, D_991, E_994, F_995), C_992)=E_994 | ~v1_funct_1(k1_tmap_1(A_993, B_990, C_992, D_991, E_994, F_995)) | k2_partfun1(D_991, B_990, F_995, k9_subset_1(A_993, C_992, D_991))!=k2_partfun1(C_992, B_990, E_994, k9_subset_1(A_993, C_992, D_991)) | ~m1_subset_1(F_995, k1_zfmisc_1(k2_zfmisc_1(D_991, B_990))) | ~v1_funct_2(F_995, D_991, B_990) | ~v1_funct_1(F_995) | ~m1_subset_1(E_994, k1_zfmisc_1(k2_zfmisc_1(C_992, B_990))) | ~v1_funct_2(E_994, C_992, B_990) | ~v1_funct_1(E_994) | ~m1_subset_1(D_991, k1_zfmisc_1(A_993)) | v1_xboole_0(D_991) | ~m1_subset_1(C_992, k1_zfmisc_1(A_993)) | v1_xboole_0(C_992) | v1_xboole_0(B_990) | v1_xboole_0(A_993))), inference(resolution, [status(thm)], [c_42, c_4993])).
% 8.37/2.74  tff(c_5317, plain, (![A_993, C_992, E_994]: (k2_partfun1(k4_subset_1(A_993, C_992, '#skF_4'), '#skF_2', k1_tmap_1(A_993, '#skF_2', C_992, '#skF_4', E_994, '#skF_6'), C_992)=E_994 | ~v1_funct_1(k1_tmap_1(A_993, '#skF_2', C_992, '#skF_4', E_994, '#skF_6')) | k2_partfun1(C_992, '#skF_2', E_994, k9_subset_1(A_993, C_992, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_993, C_992, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_994, k1_zfmisc_1(k2_zfmisc_1(C_992, '#skF_2'))) | ~v1_funct_2(E_994, C_992, '#skF_2') | ~v1_funct_1(E_994) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_993)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_992, k1_zfmisc_1(A_993)) | v1_xboole_0(C_992) | v1_xboole_0('#skF_2') | v1_xboole_0(A_993))), inference(resolution, [status(thm)], [c_48, c_5311])).
% 8.37/2.74  tff(c_5325, plain, (![A_993, C_992, E_994]: (k2_partfun1(k4_subset_1(A_993, C_992, '#skF_4'), '#skF_2', k1_tmap_1(A_993, '#skF_2', C_992, '#skF_4', E_994, '#skF_6'), C_992)=E_994 | ~v1_funct_1(k1_tmap_1(A_993, '#skF_2', C_992, '#skF_4', E_994, '#skF_6')) | k2_partfun1(C_992, '#skF_2', E_994, k9_subset_1(A_993, C_992, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_993, C_992, '#skF_4')) | ~m1_subset_1(E_994, k1_zfmisc_1(k2_zfmisc_1(C_992, '#skF_2'))) | ~v1_funct_2(E_994, C_992, '#skF_2') | ~v1_funct_1(E_994) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_993)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_992, k1_zfmisc_1(A_993)) | v1_xboole_0(C_992) | v1_xboole_0('#skF_2') | v1_xboole_0(A_993))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_4307, c_5317])).
% 8.37/2.74  tff(c_5477, plain, (![A_1016, C_1017, E_1018]: (k2_partfun1(k4_subset_1(A_1016, C_1017, '#skF_4'), '#skF_2', k1_tmap_1(A_1016, '#skF_2', C_1017, '#skF_4', E_1018, '#skF_6'), C_1017)=E_1018 | ~v1_funct_1(k1_tmap_1(A_1016, '#skF_2', C_1017, '#skF_4', E_1018, '#skF_6')) | k2_partfun1(C_1017, '#skF_2', E_1018, k9_subset_1(A_1016, C_1017, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1016, C_1017, '#skF_4')) | ~m1_subset_1(E_1018, k1_zfmisc_1(k2_zfmisc_1(C_1017, '#skF_2'))) | ~v1_funct_2(E_1018, C_1017, '#skF_2') | ~v1_funct_1(E_1018) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1016)) | ~m1_subset_1(C_1017, k1_zfmisc_1(A_1016)) | v1_xboole_0(C_1017) | v1_xboole_0(A_1016))), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_5325])).
% 8.37/2.74  tff(c_5482, plain, (![A_1016]: (k2_partfun1(k4_subset_1(A_1016, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1016, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1016, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_1016, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1016, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1016)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1016)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1016))), inference(resolution, [status(thm)], [c_54, c_5477])).
% 8.37/2.74  tff(c_5490, plain, (![A_1016]: (k2_partfun1(k4_subset_1(A_1016, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1016, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1016, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1016, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1016, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1016)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1016)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1016))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_4304, c_5482])).
% 8.37/2.74  tff(c_5544, plain, (![A_1031]: (k2_partfun1(k4_subset_1(A_1031, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1031, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1031, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1031, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1031, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1031)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1031)) | v1_xboole_0(A_1031))), inference(negUnitSimplification, [status(thm)], [c_68, c_5490])).
% 8.37/2.74  tff(c_1210, plain, (![B_358, A_359]: (k1_relat_1(B_358)=A_359 | ~v1_partfun1(B_358, A_359) | ~v4_relat_1(B_358, A_359) | ~v1_relat_1(B_358))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.37/2.74  tff(c_1213, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1162, c_1210])).
% 8.37/2.74  tff(c_1219, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_1213])).
% 8.37/2.74  tff(c_1223, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_1219])).
% 8.37/2.74  tff(c_1580, plain, (![C_397, A_398, B_399]: (v1_partfun1(C_397, A_398) | ~v1_funct_2(C_397, A_398, B_399) | ~v1_funct_1(C_397) | ~m1_subset_1(C_397, k1_zfmisc_1(k2_zfmisc_1(A_398, B_399))) | v1_xboole_0(B_399))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.37/2.74  tff(c_1586, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_1580])).
% 8.37/2.74  tff(c_1593, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1586])).
% 8.37/2.74  tff(c_1595, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_1223, c_1593])).
% 8.37/2.74  tff(c_1596, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_1219])).
% 8.37/2.74  tff(c_1604, plain, (![B_11]: (k7_relat_1('#skF_6', B_11)=k1_xboole_0 | ~r1_xboole_0(B_11, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1596, c_8])).
% 8.37/2.74  tff(c_1909, plain, (![B_426]: (k7_relat_1('#skF_6', B_426)=k1_xboole_0 | ~r1_xboole_0(B_426, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_1604])).
% 8.37/2.74  tff(c_1913, plain, (![A_14]: (k7_relat_1('#skF_6', A_14)=k1_xboole_0 | ~r1_subset_1(A_14, '#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(A_14))), inference(resolution, [status(thm)], [c_14, c_1909])).
% 8.37/2.74  tff(c_2061, plain, (![A_434]: (k7_relat_1('#skF_6', A_434)=k1_xboole_0 | ~r1_subset_1(A_434, '#skF_4') | v1_xboole_0(A_434))), inference(negUnitSimplification, [status(thm)], [c_64, c_1913])).
% 8.37/2.74  tff(c_2064, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_2061])).
% 8.37/2.74  tff(c_2067, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_68, c_2064])).
% 8.37/2.74  tff(c_1871, plain, (![B_423, A_424]: (k7_relat_1(B_423, k3_xboole_0(k1_relat_1(B_423), A_424))=k7_relat_1(B_423, A_424) | ~v1_relat_1(B_423))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.37/2.74  tff(c_1883, plain, (![A_424]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_4', A_424))=k7_relat_1('#skF_6', A_424) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1596, c_1871])).
% 8.37/2.74  tff(c_1951, plain, (![A_430]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_4', A_430))=k7_relat_1('#skF_6', A_430))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_1883])).
% 8.37/2.74  tff(c_1961, plain, (![B_2]: (k7_relat_1('#skF_6', k3_xboole_0(B_2, '#skF_4'))=k7_relat_1('#skF_6', B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1951])).
% 8.37/2.74  tff(c_1197, plain, (![A_355, B_356, C_357]: (k9_subset_1(A_355, B_356, C_357)=k3_xboole_0(B_356, C_357) | ~m1_subset_1(C_357, k1_zfmisc_1(A_355)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.37/2.74  tff(c_1209, plain, (![B_356]: (k9_subset_1('#skF_1', B_356, '#skF_4')=k3_xboole_0(B_356, '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_1197])).
% 8.37/2.74  tff(c_1186, plain, (![B_353, A_354]: (r1_subset_1(B_353, A_354) | ~r1_subset_1(A_354, B_353) | v1_xboole_0(B_353) | v1_xboole_0(A_354))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.37/2.74  tff(c_1188, plain, (r1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_1186])).
% 8.37/2.74  tff(c_1191, plain, (r1_subset_1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_68, c_64, c_1188])).
% 8.37/2.74  tff(c_1216, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1161, c_1210])).
% 8.37/2.74  tff(c_1222, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_1216])).
% 8.37/2.74  tff(c_1622, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_1222])).
% 8.37/2.74  tff(c_1842, plain, (![C_420, A_421, B_422]: (v1_partfun1(C_420, A_421) | ~v1_funct_2(C_420, A_421, B_422) | ~v1_funct_1(C_420) | ~m1_subset_1(C_420, k1_zfmisc_1(k2_zfmisc_1(A_421, B_422))) | v1_xboole_0(B_422))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.37/2.74  tff(c_1845, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_1842])).
% 8.37/2.74  tff(c_1851, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_1845])).
% 8.37/2.74  tff(c_1853, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_1622, c_1851])).
% 8.37/2.74  tff(c_1854, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_1222])).
% 8.37/2.74  tff(c_1862, plain, (![B_11]: (k7_relat_1('#skF_5', B_11)=k1_xboole_0 | ~r1_xboole_0(B_11, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1854, c_8])).
% 8.37/2.74  tff(c_1917, plain, (![B_427]: (k7_relat_1('#skF_5', B_427)=k1_xboole_0 | ~r1_xboole_0(B_427, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_1862])).
% 8.37/2.74  tff(c_1921, plain, (![A_14]: (k7_relat_1('#skF_5', A_14)=k1_xboole_0 | ~r1_subset_1(A_14, '#skF_3') | v1_xboole_0('#skF_3') | v1_xboole_0(A_14))), inference(resolution, [status(thm)], [c_14, c_1917])).
% 8.37/2.74  tff(c_2072, plain, (![A_435]: (k7_relat_1('#skF_5', A_435)=k1_xboole_0 | ~r1_subset_1(A_435, '#skF_3') | v1_xboole_0(A_435))), inference(negUnitSimplification, [status(thm)], [c_68, c_1921])).
% 8.37/2.74  tff(c_2075, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1191, c_2072])).
% 8.37/2.74  tff(c_2078, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_64, c_2075])).
% 8.37/2.74  tff(c_1880, plain, (![A_424]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', A_424))=k7_relat_1('#skF_5', A_424) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1854, c_1871])).
% 8.37/2.74  tff(c_1895, plain, (![A_424]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', A_424))=k7_relat_1('#skF_5', A_424))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_1880])).
% 8.37/2.74  tff(c_2230, plain, (![B_449, E_453, A_452, F_454, D_450, C_451]: (v1_funct_1(k1_tmap_1(A_452, B_449, C_451, D_450, E_453, F_454)) | ~m1_subset_1(F_454, k1_zfmisc_1(k2_zfmisc_1(D_450, B_449))) | ~v1_funct_2(F_454, D_450, B_449) | ~v1_funct_1(F_454) | ~m1_subset_1(E_453, k1_zfmisc_1(k2_zfmisc_1(C_451, B_449))) | ~v1_funct_2(E_453, C_451, B_449) | ~v1_funct_1(E_453) | ~m1_subset_1(D_450, k1_zfmisc_1(A_452)) | v1_xboole_0(D_450) | ~m1_subset_1(C_451, k1_zfmisc_1(A_452)) | v1_xboole_0(C_451) | v1_xboole_0(B_449) | v1_xboole_0(A_452))), inference(cnfTransformation, [status(thm)], [f_189])).
% 8.37/2.74  tff(c_2234, plain, (![A_452, C_451, E_453]: (v1_funct_1(k1_tmap_1(A_452, '#skF_2', C_451, '#skF_4', E_453, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_453, k1_zfmisc_1(k2_zfmisc_1(C_451, '#skF_2'))) | ~v1_funct_2(E_453, C_451, '#skF_2') | ~v1_funct_1(E_453) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_452)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_451, k1_zfmisc_1(A_452)) | v1_xboole_0(C_451) | v1_xboole_0('#skF_2') | v1_xboole_0(A_452))), inference(resolution, [status(thm)], [c_48, c_2230])).
% 8.37/2.74  tff(c_2241, plain, (![A_452, C_451, E_453]: (v1_funct_1(k1_tmap_1(A_452, '#skF_2', C_451, '#skF_4', E_453, '#skF_6')) | ~m1_subset_1(E_453, k1_zfmisc_1(k2_zfmisc_1(C_451, '#skF_2'))) | ~v1_funct_2(E_453, C_451, '#skF_2') | ~v1_funct_1(E_453) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_452)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_451, k1_zfmisc_1(A_452)) | v1_xboole_0(C_451) | v1_xboole_0('#skF_2') | v1_xboole_0(A_452))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_2234])).
% 8.37/2.74  tff(c_2272, plain, (![A_466, C_467, E_468]: (v1_funct_1(k1_tmap_1(A_466, '#skF_2', C_467, '#skF_4', E_468, '#skF_6')) | ~m1_subset_1(E_468, k1_zfmisc_1(k2_zfmisc_1(C_467, '#skF_2'))) | ~v1_funct_2(E_468, C_467, '#skF_2') | ~v1_funct_1(E_468) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_466)) | ~m1_subset_1(C_467, k1_zfmisc_1(A_466)) | v1_xboole_0(C_467) | v1_xboole_0(A_466))), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_2241])).
% 8.37/2.74  tff(c_2274, plain, (![A_466]: (v1_funct_1(k1_tmap_1(A_466, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_466)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_466)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_466))), inference(resolution, [status(thm)], [c_54, c_2272])).
% 8.37/2.74  tff(c_2279, plain, (![A_466]: (v1_funct_1(k1_tmap_1(A_466, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_466)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_466)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_466))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_2274])).
% 8.37/2.74  tff(c_2292, plain, (![A_470]: (v1_funct_1(k1_tmap_1(A_470, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_470)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_470)) | v1_xboole_0(A_470))), inference(negUnitSimplification, [status(thm)], [c_68, c_2279])).
% 8.37/2.74  tff(c_2295, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_66, c_2292])).
% 8.37/2.74  tff(c_2298, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2295])).
% 8.37/2.74  tff(c_2299, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_72, c_2298])).
% 8.37/2.74  tff(c_2148, plain, (![A_438, B_439, C_440, D_441]: (k2_partfun1(A_438, B_439, C_440, D_441)=k7_relat_1(C_440, D_441) | ~m1_subset_1(C_440, k1_zfmisc_1(k2_zfmisc_1(A_438, B_439))) | ~v1_funct_1(C_440))), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.37/2.74  tff(c_2150, plain, (![D_441]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_441)=k7_relat_1('#skF_5', D_441) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_2148])).
% 8.37/2.74  tff(c_2155, plain, (![D_441]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_441)=k7_relat_1('#skF_5', D_441))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2150])).
% 8.37/2.74  tff(c_2152, plain, (![D_441]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_441)=k7_relat_1('#skF_6', D_441) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_48, c_2148])).
% 8.37/2.74  tff(c_2158, plain, (![D_441]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_441)=k7_relat_1('#skF_6', D_441))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2152])).
% 8.37/2.74  tff(c_2488, plain, (![E_519, B_518, A_515, F_517, C_516, D_520]: (k2_partfun1(k4_subset_1(A_515, C_516, D_520), B_518, k1_tmap_1(A_515, B_518, C_516, D_520, E_519, F_517), D_520)=F_517 | ~m1_subset_1(k1_tmap_1(A_515, B_518, C_516, D_520, E_519, F_517), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_515, C_516, D_520), B_518))) | ~v1_funct_2(k1_tmap_1(A_515, B_518, C_516, D_520, E_519, F_517), k4_subset_1(A_515, C_516, D_520), B_518) | ~v1_funct_1(k1_tmap_1(A_515, B_518, C_516, D_520, E_519, F_517)) | k2_partfun1(D_520, B_518, F_517, k9_subset_1(A_515, C_516, D_520))!=k2_partfun1(C_516, B_518, E_519, k9_subset_1(A_515, C_516, D_520)) | ~m1_subset_1(F_517, k1_zfmisc_1(k2_zfmisc_1(D_520, B_518))) | ~v1_funct_2(F_517, D_520, B_518) | ~v1_funct_1(F_517) | ~m1_subset_1(E_519, k1_zfmisc_1(k2_zfmisc_1(C_516, B_518))) | ~v1_funct_2(E_519, C_516, B_518) | ~v1_funct_1(E_519) | ~m1_subset_1(D_520, k1_zfmisc_1(A_515)) | v1_xboole_0(D_520) | ~m1_subset_1(C_516, k1_zfmisc_1(A_515)) | v1_xboole_0(C_516) | v1_xboole_0(B_518) | v1_xboole_0(A_515))), inference(cnfTransformation, [status(thm)], [f_155])).
% 8.37/2.74  tff(c_2842, plain, (![C_623, D_622, E_625, F_626, B_621, A_624]: (k2_partfun1(k4_subset_1(A_624, C_623, D_622), B_621, k1_tmap_1(A_624, B_621, C_623, D_622, E_625, F_626), D_622)=F_626 | ~v1_funct_2(k1_tmap_1(A_624, B_621, C_623, D_622, E_625, F_626), k4_subset_1(A_624, C_623, D_622), B_621) | ~v1_funct_1(k1_tmap_1(A_624, B_621, C_623, D_622, E_625, F_626)) | k2_partfun1(D_622, B_621, F_626, k9_subset_1(A_624, C_623, D_622))!=k2_partfun1(C_623, B_621, E_625, k9_subset_1(A_624, C_623, D_622)) | ~m1_subset_1(F_626, k1_zfmisc_1(k2_zfmisc_1(D_622, B_621))) | ~v1_funct_2(F_626, D_622, B_621) | ~v1_funct_1(F_626) | ~m1_subset_1(E_625, k1_zfmisc_1(k2_zfmisc_1(C_623, B_621))) | ~v1_funct_2(E_625, C_623, B_621) | ~v1_funct_1(E_625) | ~m1_subset_1(D_622, k1_zfmisc_1(A_624)) | v1_xboole_0(D_622) | ~m1_subset_1(C_623, k1_zfmisc_1(A_624)) | v1_xboole_0(C_623) | v1_xboole_0(B_621) | v1_xboole_0(A_624))), inference(resolution, [status(thm)], [c_40, c_2488])).
% 8.37/2.74  tff(c_3111, plain, (![E_659, D_656, B_655, C_657, F_660, A_658]: (k2_partfun1(k4_subset_1(A_658, C_657, D_656), B_655, k1_tmap_1(A_658, B_655, C_657, D_656, E_659, F_660), D_656)=F_660 | ~v1_funct_1(k1_tmap_1(A_658, B_655, C_657, D_656, E_659, F_660)) | k2_partfun1(D_656, B_655, F_660, k9_subset_1(A_658, C_657, D_656))!=k2_partfun1(C_657, B_655, E_659, k9_subset_1(A_658, C_657, D_656)) | ~m1_subset_1(F_660, k1_zfmisc_1(k2_zfmisc_1(D_656, B_655))) | ~v1_funct_2(F_660, D_656, B_655) | ~v1_funct_1(F_660) | ~m1_subset_1(E_659, k1_zfmisc_1(k2_zfmisc_1(C_657, B_655))) | ~v1_funct_2(E_659, C_657, B_655) | ~v1_funct_1(E_659) | ~m1_subset_1(D_656, k1_zfmisc_1(A_658)) | v1_xboole_0(D_656) | ~m1_subset_1(C_657, k1_zfmisc_1(A_658)) | v1_xboole_0(C_657) | v1_xboole_0(B_655) | v1_xboole_0(A_658))), inference(resolution, [status(thm)], [c_42, c_2842])).
% 8.37/2.74  tff(c_3117, plain, (![A_658, C_657, E_659]: (k2_partfun1(k4_subset_1(A_658, C_657, '#skF_4'), '#skF_2', k1_tmap_1(A_658, '#skF_2', C_657, '#skF_4', E_659, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_658, '#skF_2', C_657, '#skF_4', E_659, '#skF_6')) | k2_partfun1(C_657, '#skF_2', E_659, k9_subset_1(A_658, C_657, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_658, C_657, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_659, k1_zfmisc_1(k2_zfmisc_1(C_657, '#skF_2'))) | ~v1_funct_2(E_659, C_657, '#skF_2') | ~v1_funct_1(E_659) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_658)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_657, k1_zfmisc_1(A_658)) | v1_xboole_0(C_657) | v1_xboole_0('#skF_2') | v1_xboole_0(A_658))), inference(resolution, [status(thm)], [c_48, c_3111])).
% 8.37/2.74  tff(c_3125, plain, (![A_658, C_657, E_659]: (k2_partfun1(k4_subset_1(A_658, C_657, '#skF_4'), '#skF_2', k1_tmap_1(A_658, '#skF_2', C_657, '#skF_4', E_659, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_658, '#skF_2', C_657, '#skF_4', E_659, '#skF_6')) | k2_partfun1(C_657, '#skF_2', E_659, k9_subset_1(A_658, C_657, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_658, C_657, '#skF_4')) | ~m1_subset_1(E_659, k1_zfmisc_1(k2_zfmisc_1(C_657, '#skF_2'))) | ~v1_funct_2(E_659, C_657, '#skF_2') | ~v1_funct_1(E_659) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_658)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_657, k1_zfmisc_1(A_658)) | v1_xboole_0(C_657) | v1_xboole_0('#skF_2') | v1_xboole_0(A_658))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_2158, c_3117])).
% 8.37/2.74  tff(c_3130, plain, (![A_661, C_662, E_663]: (k2_partfun1(k4_subset_1(A_661, C_662, '#skF_4'), '#skF_2', k1_tmap_1(A_661, '#skF_2', C_662, '#skF_4', E_663, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_661, '#skF_2', C_662, '#skF_4', E_663, '#skF_6')) | k2_partfun1(C_662, '#skF_2', E_663, k9_subset_1(A_661, C_662, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_661, C_662, '#skF_4')) | ~m1_subset_1(E_663, k1_zfmisc_1(k2_zfmisc_1(C_662, '#skF_2'))) | ~v1_funct_2(E_663, C_662, '#skF_2') | ~v1_funct_1(E_663) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_661)) | ~m1_subset_1(C_662, k1_zfmisc_1(A_661)) | v1_xboole_0(C_662) | v1_xboole_0(A_661))), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_3125])).
% 8.37/2.74  tff(c_3135, plain, (![A_661]: (k2_partfun1(k4_subset_1(A_661, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_661, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_661, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_661, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_661, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_661)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_661)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_661))), inference(resolution, [status(thm)], [c_54, c_3130])).
% 8.37/2.74  tff(c_3143, plain, (![A_661]: (k2_partfun1(k4_subset_1(A_661, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_661, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_661, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_661, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_661, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_661)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_661)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_661))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_2155, c_3135])).
% 8.37/2.74  tff(c_3247, plain, (![A_680]: (k2_partfun1(k4_subset_1(A_680, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_680, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_680, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_680, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_680, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_680)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_680)) | v1_xboole_0(A_680))), inference(negUnitSimplification, [status(thm)], [c_68, c_3143])).
% 8.37/2.74  tff(c_146, plain, (![C_234, A_235, B_236]: (v4_relat_1(C_234, A_235) | ~m1_subset_1(C_234, k1_zfmisc_1(k2_zfmisc_1(A_235, B_236))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.37/2.74  tff(c_154, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_48, c_146])).
% 8.37/2.74  tff(c_196, plain, (![B_248, A_249]: (k1_relat_1(B_248)=A_249 | ~v1_partfun1(B_248, A_249) | ~v4_relat_1(B_248, A_249) | ~v1_relat_1(B_248))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.37/2.74  tff(c_199, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_154, c_196])).
% 8.37/2.74  tff(c_205, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_199])).
% 8.37/2.74  tff(c_209, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_205])).
% 8.37/2.74  tff(c_556, plain, (![C_289, A_290, B_291]: (v1_partfun1(C_289, A_290) | ~v1_funct_2(C_289, A_290, B_291) | ~v1_funct_1(C_289) | ~m1_subset_1(C_289, k1_zfmisc_1(k2_zfmisc_1(A_290, B_291))) | v1_xboole_0(B_291))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.37/2.74  tff(c_562, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_556])).
% 8.37/2.74  tff(c_569, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_562])).
% 8.37/2.74  tff(c_571, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_209, c_569])).
% 8.37/2.74  tff(c_572, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_205])).
% 8.37/2.74  tff(c_580, plain, (![B_11]: (k7_relat_1('#skF_6', B_11)=k1_xboole_0 | ~r1_xboole_0(B_11, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_572, c_8])).
% 8.37/2.74  tff(c_841, plain, (![B_315]: (k7_relat_1('#skF_6', B_315)=k1_xboole_0 | ~r1_xboole_0(B_315, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_580])).
% 8.37/2.74  tff(c_845, plain, (![A_14]: (k7_relat_1('#skF_6', A_14)=k1_xboole_0 | ~r1_subset_1(A_14, '#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(A_14))), inference(resolution, [status(thm)], [c_14, c_841])).
% 8.37/2.74  tff(c_1058, plain, (![A_334]: (k7_relat_1('#skF_6', A_334)=k1_xboole_0 | ~r1_subset_1(A_334, '#skF_4') | v1_xboole_0(A_334))), inference(negUnitSimplification, [status(thm)], [c_64, c_845])).
% 8.37/2.74  tff(c_1061, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_1058])).
% 8.37/2.74  tff(c_1064, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_68, c_1061])).
% 8.37/2.74  tff(c_156, plain, (![B_238, A_239]: (r1_subset_1(B_238, A_239) | ~r1_subset_1(A_239, B_238) | v1_xboole_0(B_238) | v1_xboole_0(A_239))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.37/2.74  tff(c_158, plain, (r1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_156])).
% 8.37/2.74  tff(c_161, plain, (r1_subset_1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_68, c_64, c_158])).
% 8.37/2.74  tff(c_153, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_146])).
% 8.37/2.74  tff(c_202, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_153, c_196])).
% 8.37/2.74  tff(c_208, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_202])).
% 8.37/2.74  tff(c_594, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_208])).
% 8.37/2.74  tff(c_799, plain, (![C_311, A_312, B_313]: (v1_partfun1(C_311, A_312) | ~v1_funct_2(C_311, A_312, B_313) | ~v1_funct_1(C_311) | ~m1_subset_1(C_311, k1_zfmisc_1(k2_zfmisc_1(A_312, B_313))) | v1_xboole_0(B_313))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.37/2.74  tff(c_802, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_799])).
% 8.37/2.74  tff(c_808, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_802])).
% 8.37/2.74  tff(c_810, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_594, c_808])).
% 8.37/2.74  tff(c_811, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_208])).
% 8.37/2.74  tff(c_819, plain, (![B_11]: (k7_relat_1('#skF_5', B_11)=k1_xboole_0 | ~r1_xboole_0(B_11, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_811, c_8])).
% 8.37/2.74  tff(c_833, plain, (![B_314]: (k7_relat_1('#skF_5', B_314)=k1_xboole_0 | ~r1_xboole_0(B_314, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_819])).
% 8.37/2.74  tff(c_837, plain, (![A_14]: (k7_relat_1('#skF_5', A_14)=k1_xboole_0 | ~r1_subset_1(A_14, '#skF_3') | v1_xboole_0('#skF_3') | v1_xboole_0(A_14))), inference(resolution, [status(thm)], [c_14, c_833])).
% 8.37/2.74  tff(c_1047, plain, (![A_333]: (k7_relat_1('#skF_5', A_333)=k1_xboole_0 | ~r1_subset_1(A_333, '#skF_3') | v1_xboole_0(A_333))), inference(negUnitSimplification, [status(thm)], [c_68, c_837])).
% 8.37/2.74  tff(c_1050, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_161, c_1047])).
% 8.37/2.74  tff(c_1053, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_64, c_1050])).
% 8.37/2.74  tff(c_577, plain, (![A_12]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_4', A_12))=k7_relat_1('#skF_6', A_12) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_572, c_10])).
% 8.37/2.74  tff(c_587, plain, (![A_12]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_4', A_12))=k7_relat_1('#skF_6', A_12))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_577])).
% 8.37/2.74  tff(c_1009, plain, (![A_326, B_327, C_328, D_329]: (k2_partfun1(A_326, B_327, C_328, D_329)=k7_relat_1(C_328, D_329) | ~m1_subset_1(C_328, k1_zfmisc_1(k2_zfmisc_1(A_326, B_327))) | ~v1_funct_1(C_328))), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.37/2.74  tff(c_1013, plain, (![D_329]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_329)=k7_relat_1('#skF_6', D_329) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_48, c_1009])).
% 8.37/2.74  tff(c_1019, plain, (![D_329]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_329)=k7_relat_1('#skF_6', D_329))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1013])).
% 8.37/2.74  tff(c_816, plain, (![A_12]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', A_12))=k7_relat_1('#skF_5', A_12) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_811, c_10])).
% 8.37/2.74  tff(c_882, plain, (![A_321]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', A_321))=k7_relat_1('#skF_5', A_321))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_816])).
% 8.37/2.74  tff(c_896, plain, (![A_1]: (k7_relat_1('#skF_5', k3_xboole_0(A_1, '#skF_3'))=k7_relat_1('#skF_5', A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_882])).
% 8.37/2.74  tff(c_1011, plain, (![D_329]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_329)=k7_relat_1('#skF_5', D_329) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_1009])).
% 8.37/2.74  tff(c_1016, plain, (![D_329]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_329)=k7_relat_1('#skF_5', D_329))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1011])).
% 8.37/2.74  tff(c_849, plain, (![A_316, B_317, C_318]: (k9_subset_1(A_316, B_317, C_318)=k3_xboole_0(B_317, C_318) | ~m1_subset_1(C_318, k1_zfmisc_1(A_316)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.37/2.74  tff(c_861, plain, (![B_317]: (k9_subset_1('#skF_1', B_317, '#skF_4')=k3_xboole_0(B_317, '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_849])).
% 8.37/2.74  tff(c_46, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.37/2.74  tff(c_135, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_46])).
% 8.37/2.74  tff(c_871, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_861, c_861, c_135])).
% 8.37/2.74  tff(c_872, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_4', '#skF_3'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_871])).
% 8.37/2.74  tff(c_1146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1064, c_1053, c_587, c_1019, c_896, c_1016, c_872])).
% 8.37/2.74  tff(c_1147, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_46])).
% 8.37/2.74  tff(c_1178, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_1147])).
% 8.37/2.74  tff(c_3258, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3247, c_1178])).
% 8.37/2.74  tff(c_3272, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_2067, c_1961, c_1209, c_2078, c_1895, c_1209, c_2299, c_3258])).
% 8.37/2.74  tff(c_3274, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_3272])).
% 8.37/2.74  tff(c_3275, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_1147])).
% 8.37/2.74  tff(c_5553, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5544, c_3275])).
% 8.37/2.74  tff(c_5564, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_4214, c_4097, c_3307, c_4203, c_4014, c_3307, c_4435, c_5553])).
% 8.37/2.74  tff(c_5566, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_5564])).
% 8.37/2.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.37/2.74  
% 8.37/2.74  Inference rules
% 8.37/2.74  ----------------------
% 8.37/2.74  #Ref     : 0
% 8.37/2.74  #Sup     : 1110
% 8.37/2.74  #Fact    : 0
% 8.37/2.74  #Define  : 0
% 8.37/2.74  #Split   : 28
% 8.37/2.74  #Chain   : 0
% 8.37/2.74  #Close   : 0
% 8.37/2.74  
% 8.37/2.74  Ordering : KBO
% 8.37/2.74  
% 8.37/2.74  Simplification rules
% 8.37/2.74  ----------------------
% 8.37/2.74  #Subsume      : 58
% 8.37/2.74  #Demod        : 934
% 8.37/2.74  #Tautology    : 682
% 8.37/2.74  #SimpNegUnit  : 201
% 8.37/2.74  #BackRed      : 20
% 8.37/2.74  
% 8.37/2.74  #Partial instantiations: 0
% 8.37/2.74  #Strategies tried      : 1
% 8.37/2.74  
% 8.37/2.74  Timing (in seconds)
% 8.37/2.74  ----------------------
% 8.37/2.74  Preprocessing        : 0.44
% 8.37/2.74  Parsing              : 0.21
% 8.37/2.74  CNF conversion       : 0.06
% 8.37/2.74  Main loop            : 1.49
% 8.37/2.74  Inferencing          : 0.54
% 8.37/2.74  Reduction            : 0.52
% 8.37/2.75  Demodulation         : 0.39
% 8.37/2.75  BG Simplification    : 0.06
% 8.37/2.75  Subsumption          : 0.29
% 8.37/2.75  Abstraction          : 0.07
% 8.37/2.75  MUC search           : 0.00
% 8.37/2.75  Cooper               : 0.00
% 8.37/2.75  Total                : 2.00
% 8.37/2.75  Index Insertion      : 0.00
% 8.37/2.75  Index Deletion       : 0.00
% 8.37/2.75  Index Matching       : 0.00
% 8.37/2.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
