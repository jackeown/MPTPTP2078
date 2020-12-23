%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:13 EST 2020

% Result     : Theorem 11.59s
% Output     : CNFRefutation 11.86s
% Verified   : 
% Statistics : Number of formulae       :  245 ( 982 expanded)
%              Number of leaves         :   51 ( 369 expanded)
%              Depth                    :   14
%              Number of atoms          :  767 (4718 expanded)
%              Number of equality atoms :  155 ( 861 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_248,negated_conjecture,(
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

tff(f_27,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_118,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_110,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_50,axiom,(
    ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
       => r1_subset_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_206,axiom,(
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

tff(f_124,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_172,axiom,(
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

tff(c_82,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_76,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_2,plain,(
    ! [A_1] : r1_xboole_0(A_1,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_58,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_100,plain,(
    ! [C_236,A_237,B_238] :
      ( v1_relat_1(C_236)
      | ~ m1_subset_1(C_236,k1_zfmisc_1(k2_zfmisc_1(A_237,B_238))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_107,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_100])).

tff(c_1486,plain,(
    ! [C_359,A_360,B_361] :
      ( v4_relat_1(C_359,A_360)
      | ~ m1_subset_1(C_359,k1_zfmisc_1(k2_zfmisc_1(A_360,B_361))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1493,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_1486])).

tff(c_1504,plain,(
    ! [B_365,A_366] :
      ( k7_relat_1(B_365,A_366) = B_365
      | ~ v4_relat_1(B_365,A_366)
      | ~ v1_relat_1(B_365) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1510,plain,
    ( k7_relat_1('#skF_6','#skF_4') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1493,c_1504])).

tff(c_1516,plain,(
    k7_relat_1('#skF_6','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_1510])).

tff(c_8564,plain,(
    ! [C_1065,A_1066,B_1067] :
      ( k7_relat_1(k7_relat_1(C_1065,A_1066),B_1067) = k1_xboole_0
      | ~ r1_xboole_0(A_1066,B_1067)
      | ~ v1_relat_1(C_1065) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8582,plain,(
    ! [B_1067] :
      ( k7_relat_1('#skF_6',B_1067) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_1067)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1516,c_8564])).

tff(c_8607,plain,(
    ! [B_1071] :
      ( k7_relat_1('#skF_6',B_1071) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_1071) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_8582])).

tff(c_8619,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_8607])).

tff(c_80,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_7291,plain,(
    ! [B_964,A_965] :
      ( k1_relat_1(B_964) = A_965
      | ~ v1_partfun1(B_964,A_965)
      | ~ v4_relat_1(B_964,A_965)
      | ~ v1_relat_1(B_964) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_7297,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1493,c_7291])).

tff(c_7303,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_7297])).

tff(c_8106,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_7303])).

tff(c_62,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_60,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_8490,plain,(
    ! [C_1055,A_1056,B_1057] :
      ( v1_partfun1(C_1055,A_1056)
      | ~ v1_funct_2(C_1055,A_1056,B_1057)
      | ~ v1_funct_1(C_1055)
      | ~ m1_subset_1(C_1055,k1_zfmisc_1(k2_zfmisc_1(A_1056,B_1057)))
      | v1_xboole_0(B_1057) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_8493,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_8490])).

tff(c_8499,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_8493])).

tff(c_8501,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_8106,c_8499])).

tff(c_8502,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_7303])).

tff(c_14,plain,(
    ! [A_13] : k10_relat_1(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_78,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_70,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_7268,plain,(
    ! [B_957,A_958] :
      ( r1_subset_1(B_957,A_958)
      | ~ r1_subset_1(A_958,B_957)
      | v1_xboole_0(B_957)
      | v1_xboole_0(A_958) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_7270,plain,
    ( r1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_7268])).

tff(c_7273,plain,(
    r1_subset_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_74,c_7270])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( r1_xboole_0(A_19,B_20)
      | ~ r1_subset_1(A_19,B_20)
      | v1_xboole_0(B_20)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_8611,plain,(
    ! [B_20] :
      ( k7_relat_1('#skF_6',B_20) = k1_xboole_0
      | ~ r1_subset_1('#skF_4',B_20)
      | v1_xboole_0(B_20)
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22,c_8607])).

tff(c_8638,plain,(
    ! [B_1072] :
      ( k7_relat_1('#skF_6',B_1072) = k1_xboole_0
      | ~ r1_subset_1('#skF_4',B_1072)
      | v1_xboole_0(B_1072) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_8611])).

tff(c_8641,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_7273,c_8638])).

tff(c_8644,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_8641])).

tff(c_12,plain,(
    ! [A_12] :
      ( k10_relat_1(A_12,k2_relat_1(A_12)) = k1_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8592,plain,(
    ! [A_1068,C_1069,B_1070] :
      ( k3_xboole_0(A_1068,k10_relat_1(C_1069,B_1070)) = k10_relat_1(k7_relat_1(C_1069,A_1068),B_1070)
      | ~ v1_relat_1(C_1069) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_8945,plain,(
    ! [A_1096,A_1097] :
      ( k10_relat_1(k7_relat_1(A_1096,A_1097),k2_relat_1(A_1096)) = k3_xboole_0(A_1097,k1_relat_1(A_1096))
      | ~ v1_relat_1(A_1096)
      | ~ v1_relat_1(A_1096) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_8592])).

tff(c_8981,plain,
    ( k3_xboole_0('#skF_3',k1_relat_1('#skF_6')) = k10_relat_1(k1_xboole_0,k2_relat_1('#skF_6'))
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_8644,c_8945])).

tff(c_9010,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_107,c_8502,c_14,c_8981])).

tff(c_64,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_108,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_100])).

tff(c_1494,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_1486])).

tff(c_1507,plain,
    ( k7_relat_1('#skF_5','#skF_3') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1494,c_1504])).

tff(c_1513,plain,(
    k7_relat_1('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_1507])).

tff(c_8585,plain,(
    ! [B_1067] :
      ( k7_relat_1('#skF_5',B_1067) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_1067)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1513,c_8564])).

tff(c_8663,plain,(
    ! [B_1073] :
      ( k7_relat_1('#skF_5',B_1073) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_1073) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_8585])).

tff(c_8675,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_8663])).

tff(c_8514,plain,(
    ! [A_1058,B_1059,C_1060] :
      ( k9_subset_1(A_1058,B_1059,C_1060) = k3_xboole_0(B_1059,C_1060)
      | ~ m1_subset_1(C_1060,k1_zfmisc_1(A_1058)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8525,plain,(
    ! [B_1059] : k9_subset_1('#skF_1',B_1059,'#skF_4') = k3_xboole_0(B_1059,'#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_8514])).

tff(c_68,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_66,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_8885,plain,(
    ! [E_1094,F_1091,D_1090,A_1089,C_1093,B_1092] :
      ( v1_funct_1(k1_tmap_1(A_1089,B_1092,C_1093,D_1090,E_1094,F_1091))
      | ~ m1_subset_1(F_1091,k1_zfmisc_1(k2_zfmisc_1(D_1090,B_1092)))
      | ~ v1_funct_2(F_1091,D_1090,B_1092)
      | ~ v1_funct_1(F_1091)
      | ~ m1_subset_1(E_1094,k1_zfmisc_1(k2_zfmisc_1(C_1093,B_1092)))
      | ~ v1_funct_2(E_1094,C_1093,B_1092)
      | ~ v1_funct_1(E_1094)
      | ~ m1_subset_1(D_1090,k1_zfmisc_1(A_1089))
      | v1_xboole_0(D_1090)
      | ~ m1_subset_1(C_1093,k1_zfmisc_1(A_1089))
      | v1_xboole_0(C_1093)
      | v1_xboole_0(B_1092)
      | v1_xboole_0(A_1089) ) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_8887,plain,(
    ! [A_1089,C_1093,E_1094] :
      ( v1_funct_1(k1_tmap_1(A_1089,'#skF_2',C_1093,'#skF_4',E_1094,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1094,k1_zfmisc_1(k2_zfmisc_1(C_1093,'#skF_2')))
      | ~ v1_funct_2(E_1094,C_1093,'#skF_2')
      | ~ v1_funct_1(E_1094)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1089))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1093,k1_zfmisc_1(A_1089))
      | v1_xboole_0(C_1093)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1089) ) ),
    inference(resolution,[status(thm)],[c_58,c_8885])).

tff(c_8892,plain,(
    ! [A_1089,C_1093,E_1094] :
      ( v1_funct_1(k1_tmap_1(A_1089,'#skF_2',C_1093,'#skF_4',E_1094,'#skF_6'))
      | ~ m1_subset_1(E_1094,k1_zfmisc_1(k2_zfmisc_1(C_1093,'#skF_2')))
      | ~ v1_funct_2(E_1094,C_1093,'#skF_2')
      | ~ v1_funct_1(E_1094)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1089))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1093,k1_zfmisc_1(A_1089))
      | v1_xboole_0(C_1093)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1089) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_8887])).

tff(c_9018,plain,(
    ! [A_1098,C_1099,E_1100] :
      ( v1_funct_1(k1_tmap_1(A_1098,'#skF_2',C_1099,'#skF_4',E_1100,'#skF_6'))
      | ~ m1_subset_1(E_1100,k1_zfmisc_1(k2_zfmisc_1(C_1099,'#skF_2')))
      | ~ v1_funct_2(E_1100,C_1099,'#skF_2')
      | ~ v1_funct_1(E_1100)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1098))
      | ~ m1_subset_1(C_1099,k1_zfmisc_1(A_1098))
      | v1_xboole_0(C_1099)
      | v1_xboole_0(A_1098) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_8892])).

tff(c_9022,plain,(
    ! [A_1098] :
      ( v1_funct_1(k1_tmap_1(A_1098,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1098))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1098))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1098) ) ),
    inference(resolution,[status(thm)],[c_64,c_9018])).

tff(c_9029,plain,(
    ! [A_1098] :
      ( v1_funct_1(k1_tmap_1(A_1098,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1098))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1098))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1098) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_9022])).

tff(c_9258,plain,(
    ! [A_1116] :
      ( v1_funct_1(k1_tmap_1(A_1116,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1116))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1116))
      | v1_xboole_0(A_1116) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_9029])).

tff(c_9261,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_9258])).

tff(c_9264,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_9261])).

tff(c_9265,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_9264])).

tff(c_8694,plain,(
    ! [A_1074,B_1075,C_1076,D_1077] :
      ( k2_partfun1(A_1074,B_1075,C_1076,D_1077) = k7_relat_1(C_1076,D_1077)
      | ~ m1_subset_1(C_1076,k1_zfmisc_1(k2_zfmisc_1(A_1074,B_1075)))
      | ~ v1_funct_1(C_1076) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_8698,plain,(
    ! [D_1077] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_1077) = k7_relat_1('#skF_5',D_1077)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_64,c_8694])).

tff(c_8704,plain,(
    ! [D_1077] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_1077) = k7_relat_1('#skF_5',D_1077) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_8698])).

tff(c_8696,plain,(
    ! [D_1077] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_1077) = k7_relat_1('#skF_6',D_1077)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_58,c_8694])).

tff(c_8701,plain,(
    ! [D_1077] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_1077) = k7_relat_1('#skF_6',D_1077) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_8696])).

tff(c_52,plain,(
    ! [C_171,E_173,F_174,D_172,A_169,B_170] :
      ( v1_funct_2(k1_tmap_1(A_169,B_170,C_171,D_172,E_173,F_174),k4_subset_1(A_169,C_171,D_172),B_170)
      | ~ m1_subset_1(F_174,k1_zfmisc_1(k2_zfmisc_1(D_172,B_170)))
      | ~ v1_funct_2(F_174,D_172,B_170)
      | ~ v1_funct_1(F_174)
      | ~ m1_subset_1(E_173,k1_zfmisc_1(k2_zfmisc_1(C_171,B_170)))
      | ~ v1_funct_2(E_173,C_171,B_170)
      | ~ v1_funct_1(E_173)
      | ~ m1_subset_1(D_172,k1_zfmisc_1(A_169))
      | v1_xboole_0(D_172)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(A_169))
      | v1_xboole_0(C_171)
      | v1_xboole_0(B_170)
      | v1_xboole_0(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_50,plain,(
    ! [C_171,E_173,F_174,D_172,A_169,B_170] :
      ( m1_subset_1(k1_tmap_1(A_169,B_170,C_171,D_172,E_173,F_174),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_169,C_171,D_172),B_170)))
      | ~ m1_subset_1(F_174,k1_zfmisc_1(k2_zfmisc_1(D_172,B_170)))
      | ~ v1_funct_2(F_174,D_172,B_170)
      | ~ v1_funct_1(F_174)
      | ~ m1_subset_1(E_173,k1_zfmisc_1(k2_zfmisc_1(C_171,B_170)))
      | ~ v1_funct_2(E_173,C_171,B_170)
      | ~ v1_funct_1(E_173)
      | ~ m1_subset_1(D_172,k1_zfmisc_1(A_169))
      | v1_xboole_0(D_172)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(A_169))
      | v1_xboole_0(C_171)
      | v1_xboole_0(B_170)
      | v1_xboole_0(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_9318,plain,(
    ! [F_1126,B_1124,C_1121,A_1122,E_1123,D_1125] :
      ( k2_partfun1(k4_subset_1(A_1122,C_1121,D_1125),B_1124,k1_tmap_1(A_1122,B_1124,C_1121,D_1125,E_1123,F_1126),C_1121) = E_1123
      | ~ m1_subset_1(k1_tmap_1(A_1122,B_1124,C_1121,D_1125,E_1123,F_1126),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1122,C_1121,D_1125),B_1124)))
      | ~ v1_funct_2(k1_tmap_1(A_1122,B_1124,C_1121,D_1125,E_1123,F_1126),k4_subset_1(A_1122,C_1121,D_1125),B_1124)
      | ~ v1_funct_1(k1_tmap_1(A_1122,B_1124,C_1121,D_1125,E_1123,F_1126))
      | k2_partfun1(D_1125,B_1124,F_1126,k9_subset_1(A_1122,C_1121,D_1125)) != k2_partfun1(C_1121,B_1124,E_1123,k9_subset_1(A_1122,C_1121,D_1125))
      | ~ m1_subset_1(F_1126,k1_zfmisc_1(k2_zfmisc_1(D_1125,B_1124)))
      | ~ v1_funct_2(F_1126,D_1125,B_1124)
      | ~ v1_funct_1(F_1126)
      | ~ m1_subset_1(E_1123,k1_zfmisc_1(k2_zfmisc_1(C_1121,B_1124)))
      | ~ v1_funct_2(E_1123,C_1121,B_1124)
      | ~ v1_funct_1(E_1123)
      | ~ m1_subset_1(D_1125,k1_zfmisc_1(A_1122))
      | v1_xboole_0(D_1125)
      | ~ m1_subset_1(C_1121,k1_zfmisc_1(A_1122))
      | v1_xboole_0(C_1121)
      | v1_xboole_0(B_1124)
      | v1_xboole_0(A_1122) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_10952,plain,(
    ! [B_1344,A_1341,C_1345,F_1343,D_1342,E_1346] :
      ( k2_partfun1(k4_subset_1(A_1341,C_1345,D_1342),B_1344,k1_tmap_1(A_1341,B_1344,C_1345,D_1342,E_1346,F_1343),C_1345) = E_1346
      | ~ v1_funct_2(k1_tmap_1(A_1341,B_1344,C_1345,D_1342,E_1346,F_1343),k4_subset_1(A_1341,C_1345,D_1342),B_1344)
      | ~ v1_funct_1(k1_tmap_1(A_1341,B_1344,C_1345,D_1342,E_1346,F_1343))
      | k2_partfun1(D_1342,B_1344,F_1343,k9_subset_1(A_1341,C_1345,D_1342)) != k2_partfun1(C_1345,B_1344,E_1346,k9_subset_1(A_1341,C_1345,D_1342))
      | ~ m1_subset_1(F_1343,k1_zfmisc_1(k2_zfmisc_1(D_1342,B_1344)))
      | ~ v1_funct_2(F_1343,D_1342,B_1344)
      | ~ v1_funct_1(F_1343)
      | ~ m1_subset_1(E_1346,k1_zfmisc_1(k2_zfmisc_1(C_1345,B_1344)))
      | ~ v1_funct_2(E_1346,C_1345,B_1344)
      | ~ v1_funct_1(E_1346)
      | ~ m1_subset_1(D_1342,k1_zfmisc_1(A_1341))
      | v1_xboole_0(D_1342)
      | ~ m1_subset_1(C_1345,k1_zfmisc_1(A_1341))
      | v1_xboole_0(C_1345)
      | v1_xboole_0(B_1344)
      | v1_xboole_0(A_1341) ) ),
    inference(resolution,[status(thm)],[c_50,c_9318])).

tff(c_12401,plain,(
    ! [C_1468,F_1466,B_1467,A_1464,E_1469,D_1465] :
      ( k2_partfun1(k4_subset_1(A_1464,C_1468,D_1465),B_1467,k1_tmap_1(A_1464,B_1467,C_1468,D_1465,E_1469,F_1466),C_1468) = E_1469
      | ~ v1_funct_1(k1_tmap_1(A_1464,B_1467,C_1468,D_1465,E_1469,F_1466))
      | k2_partfun1(D_1465,B_1467,F_1466,k9_subset_1(A_1464,C_1468,D_1465)) != k2_partfun1(C_1468,B_1467,E_1469,k9_subset_1(A_1464,C_1468,D_1465))
      | ~ m1_subset_1(F_1466,k1_zfmisc_1(k2_zfmisc_1(D_1465,B_1467)))
      | ~ v1_funct_2(F_1466,D_1465,B_1467)
      | ~ v1_funct_1(F_1466)
      | ~ m1_subset_1(E_1469,k1_zfmisc_1(k2_zfmisc_1(C_1468,B_1467)))
      | ~ v1_funct_2(E_1469,C_1468,B_1467)
      | ~ v1_funct_1(E_1469)
      | ~ m1_subset_1(D_1465,k1_zfmisc_1(A_1464))
      | v1_xboole_0(D_1465)
      | ~ m1_subset_1(C_1468,k1_zfmisc_1(A_1464))
      | v1_xboole_0(C_1468)
      | v1_xboole_0(B_1467)
      | v1_xboole_0(A_1464) ) ),
    inference(resolution,[status(thm)],[c_52,c_10952])).

tff(c_12405,plain,(
    ! [A_1464,C_1468,E_1469] :
      ( k2_partfun1(k4_subset_1(A_1464,C_1468,'#skF_4'),'#skF_2',k1_tmap_1(A_1464,'#skF_2',C_1468,'#skF_4',E_1469,'#skF_6'),C_1468) = E_1469
      | ~ v1_funct_1(k1_tmap_1(A_1464,'#skF_2',C_1468,'#skF_4',E_1469,'#skF_6'))
      | k2_partfun1(C_1468,'#skF_2',E_1469,k9_subset_1(A_1464,C_1468,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_1464,C_1468,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1469,k1_zfmisc_1(k2_zfmisc_1(C_1468,'#skF_2')))
      | ~ v1_funct_2(E_1469,C_1468,'#skF_2')
      | ~ v1_funct_1(E_1469)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1464))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1468,k1_zfmisc_1(A_1464))
      | v1_xboole_0(C_1468)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1464) ) ),
    inference(resolution,[status(thm)],[c_58,c_12401])).

tff(c_12411,plain,(
    ! [A_1464,C_1468,E_1469] :
      ( k2_partfun1(k4_subset_1(A_1464,C_1468,'#skF_4'),'#skF_2',k1_tmap_1(A_1464,'#skF_2',C_1468,'#skF_4',E_1469,'#skF_6'),C_1468) = E_1469
      | ~ v1_funct_1(k1_tmap_1(A_1464,'#skF_2',C_1468,'#skF_4',E_1469,'#skF_6'))
      | k2_partfun1(C_1468,'#skF_2',E_1469,k9_subset_1(A_1464,C_1468,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1464,C_1468,'#skF_4'))
      | ~ m1_subset_1(E_1469,k1_zfmisc_1(k2_zfmisc_1(C_1468,'#skF_2')))
      | ~ v1_funct_2(E_1469,C_1468,'#skF_2')
      | ~ v1_funct_1(E_1469)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1464))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1468,k1_zfmisc_1(A_1464))
      | v1_xboole_0(C_1468)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1464) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_8701,c_12405])).

tff(c_12939,plain,(
    ! [A_1525,C_1526,E_1527] :
      ( k2_partfun1(k4_subset_1(A_1525,C_1526,'#skF_4'),'#skF_2',k1_tmap_1(A_1525,'#skF_2',C_1526,'#skF_4',E_1527,'#skF_6'),C_1526) = E_1527
      | ~ v1_funct_1(k1_tmap_1(A_1525,'#skF_2',C_1526,'#skF_4',E_1527,'#skF_6'))
      | k2_partfun1(C_1526,'#skF_2',E_1527,k9_subset_1(A_1525,C_1526,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1525,C_1526,'#skF_4'))
      | ~ m1_subset_1(E_1527,k1_zfmisc_1(k2_zfmisc_1(C_1526,'#skF_2')))
      | ~ v1_funct_2(E_1527,C_1526,'#skF_2')
      | ~ v1_funct_1(E_1527)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1525))
      | ~ m1_subset_1(C_1526,k1_zfmisc_1(A_1525))
      | v1_xboole_0(C_1526)
      | v1_xboole_0(A_1525) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_12411])).

tff(c_12946,plain,(
    ! [A_1525] :
      ( k2_partfun1(k4_subset_1(A_1525,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1525,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1525,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1525,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1525,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1525))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1525))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1525) ) ),
    inference(resolution,[status(thm)],[c_64,c_12939])).

tff(c_12956,plain,(
    ! [A_1525] :
      ( k2_partfun1(k4_subset_1(A_1525,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1525,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1525,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1525,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1525,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1525))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1525))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1525) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_8704,c_12946])).

tff(c_13072,plain,(
    ! [A_1547] :
      ( k2_partfun1(k4_subset_1(A_1547,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1547,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1547,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1547,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1547,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1547))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1547))
      | v1_xboole_0(A_1547) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_12956])).

tff(c_2492,plain,(
    ! [C_458,A_459,B_460] :
      ( k7_relat_1(k7_relat_1(C_458,A_459),B_460) = k1_xboole_0
      | ~ r1_xboole_0(A_459,B_460)
      | ~ v1_relat_1(C_458) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2510,plain,(
    ! [B_460] :
      ( k7_relat_1('#skF_6',B_460) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_460)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1516,c_2492])).

tff(c_2520,plain,(
    ! [B_461] :
      ( k7_relat_1('#skF_6',B_461) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_461) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_2510])).

tff(c_2532,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_2520])).

tff(c_1611,plain,(
    ! [B_381,A_382] :
      ( k1_relat_1(B_381) = A_382
      | ~ v1_partfun1(B_381,A_382)
      | ~ v4_relat_1(B_381,A_382)
      | ~ v1_relat_1(B_381) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1617,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1493,c_1611])).

tff(c_1623,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_1617])).

tff(c_2215,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1623])).

tff(c_2459,plain,(
    ! [C_454,A_455,B_456] :
      ( v1_partfun1(C_454,A_455)
      | ~ v1_funct_2(C_454,A_455,B_456)
      | ~ v1_funct_1(C_454)
      | ~ m1_subset_1(C_454,k1_zfmisc_1(k2_zfmisc_1(A_455,B_456)))
      | v1_xboole_0(B_456) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2462,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_2459])).

tff(c_2468,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_2462])).

tff(c_2470,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2215,c_2468])).

tff(c_2471,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1623])).

tff(c_1557,plain,(
    ! [B_371,A_372] :
      ( r1_subset_1(B_371,A_372)
      | ~ r1_subset_1(A_372,B_371)
      | v1_xboole_0(B_371)
      | v1_xboole_0(A_372) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1559,plain,
    ( r1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_1557])).

tff(c_1562,plain,(
    r1_subset_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_74,c_1559])).

tff(c_2524,plain,(
    ! [B_20] :
      ( k7_relat_1('#skF_6',B_20) = k1_xboole_0
      | ~ r1_subset_1('#skF_4',B_20)
      | v1_xboole_0(B_20)
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22,c_2520])).

tff(c_2609,plain,(
    ! [B_467] :
      ( k7_relat_1('#skF_6',B_467) = k1_xboole_0
      | ~ r1_subset_1('#skF_4',B_467)
      | v1_xboole_0(B_467) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2524])).

tff(c_2612,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1562,c_2609])).

tff(c_2615,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2612])).

tff(c_2564,plain,(
    ! [A_463,C_464,B_465] :
      ( k3_xboole_0(A_463,k10_relat_1(C_464,B_465)) = k10_relat_1(k7_relat_1(C_464,A_463),B_465)
      | ~ v1_relat_1(C_464) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2860,plain,(
    ! [A_483,A_484] :
      ( k10_relat_1(k7_relat_1(A_483,A_484),k2_relat_1(A_483)) = k3_xboole_0(A_484,k1_relat_1(A_483))
      | ~ v1_relat_1(A_483)
      | ~ v1_relat_1(A_483) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2564])).

tff(c_2893,plain,
    ( k3_xboole_0('#skF_3',k1_relat_1('#skF_6')) = k10_relat_1(k1_xboole_0,k2_relat_1('#skF_6'))
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2615,c_2860])).

tff(c_2923,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_107,c_2471,c_14,c_2893])).

tff(c_2513,plain,(
    ! [B_460] :
      ( k7_relat_1('#skF_5',B_460) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_460)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1513,c_2492])).

tff(c_2551,plain,(
    ! [B_462] :
      ( k7_relat_1('#skF_5',B_462) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_462) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_2513])).

tff(c_2563,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_2551])).

tff(c_1579,plain,(
    ! [A_376,B_377,C_378] :
      ( k9_subset_1(A_376,B_377,C_378) = k3_xboole_0(B_377,C_378)
      | ~ m1_subset_1(C_378,k1_zfmisc_1(A_376)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1590,plain,(
    ! [B_377] : k9_subset_1('#skF_1',B_377,'#skF_4') = k3_xboole_0(B_377,'#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_1579])).

tff(c_2937,plain,(
    ! [D_486,E_490,A_485,B_488,C_489,F_487] :
      ( v1_funct_1(k1_tmap_1(A_485,B_488,C_489,D_486,E_490,F_487))
      | ~ m1_subset_1(F_487,k1_zfmisc_1(k2_zfmisc_1(D_486,B_488)))
      | ~ v1_funct_2(F_487,D_486,B_488)
      | ~ v1_funct_1(F_487)
      | ~ m1_subset_1(E_490,k1_zfmisc_1(k2_zfmisc_1(C_489,B_488)))
      | ~ v1_funct_2(E_490,C_489,B_488)
      | ~ v1_funct_1(E_490)
      | ~ m1_subset_1(D_486,k1_zfmisc_1(A_485))
      | v1_xboole_0(D_486)
      | ~ m1_subset_1(C_489,k1_zfmisc_1(A_485))
      | v1_xboole_0(C_489)
      | v1_xboole_0(B_488)
      | v1_xboole_0(A_485) ) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_2939,plain,(
    ! [A_485,C_489,E_490] :
      ( v1_funct_1(k1_tmap_1(A_485,'#skF_2',C_489,'#skF_4',E_490,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_490,k1_zfmisc_1(k2_zfmisc_1(C_489,'#skF_2')))
      | ~ v1_funct_2(E_490,C_489,'#skF_2')
      | ~ v1_funct_1(E_490)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_485))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_489,k1_zfmisc_1(A_485))
      | v1_xboole_0(C_489)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_485) ) ),
    inference(resolution,[status(thm)],[c_58,c_2937])).

tff(c_2944,plain,(
    ! [A_485,C_489,E_490] :
      ( v1_funct_1(k1_tmap_1(A_485,'#skF_2',C_489,'#skF_4',E_490,'#skF_6'))
      | ~ m1_subset_1(E_490,k1_zfmisc_1(k2_zfmisc_1(C_489,'#skF_2')))
      | ~ v1_funct_2(E_490,C_489,'#skF_2')
      | ~ v1_funct_1(E_490)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_485))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_489,k1_zfmisc_1(A_485))
      | v1_xboole_0(C_489)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_485) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_2939])).

tff(c_2970,plain,(
    ! [A_491,C_492,E_493] :
      ( v1_funct_1(k1_tmap_1(A_491,'#skF_2',C_492,'#skF_4',E_493,'#skF_6'))
      | ~ m1_subset_1(E_493,k1_zfmisc_1(k2_zfmisc_1(C_492,'#skF_2')))
      | ~ v1_funct_2(E_493,C_492,'#skF_2')
      | ~ v1_funct_1(E_493)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_491))
      | ~ m1_subset_1(C_492,k1_zfmisc_1(A_491))
      | v1_xboole_0(C_492)
      | v1_xboole_0(A_491) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_2944])).

tff(c_2974,plain,(
    ! [A_491] :
      ( v1_funct_1(k1_tmap_1(A_491,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_491))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_491))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_491) ) ),
    inference(resolution,[status(thm)],[c_64,c_2970])).

tff(c_2981,plain,(
    ! [A_491] :
      ( v1_funct_1(k1_tmap_1(A_491,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_491))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_491))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_491) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_2974])).

tff(c_3196,plain,(
    ! [A_513] :
      ( v1_funct_1(k1_tmap_1(A_513,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_513))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_513))
      | v1_xboole_0(A_513) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2981])).

tff(c_3199,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_3196])).

tff(c_3202,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3199])).

tff(c_3203,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_3202])).

tff(c_2658,plain,(
    ! [A_469,B_470,C_471,D_472] :
      ( k2_partfun1(A_469,B_470,C_471,D_472) = k7_relat_1(C_471,D_472)
      | ~ m1_subset_1(C_471,k1_zfmisc_1(k2_zfmisc_1(A_469,B_470)))
      | ~ v1_funct_1(C_471) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2662,plain,(
    ! [D_472] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_472) = k7_relat_1('#skF_5',D_472)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_64,c_2658])).

tff(c_2668,plain,(
    ! [D_472] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_472) = k7_relat_1('#skF_5',D_472) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2662])).

tff(c_2660,plain,(
    ! [D_472] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_472) = k7_relat_1('#skF_6',D_472)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_58,c_2658])).

tff(c_2665,plain,(
    ! [D_472] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_472) = k7_relat_1('#skF_6',D_472) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2660])).

tff(c_3463,plain,(
    ! [C_539,D_543,A_540,E_541,F_544,B_542] :
      ( k2_partfun1(k4_subset_1(A_540,C_539,D_543),B_542,k1_tmap_1(A_540,B_542,C_539,D_543,E_541,F_544),D_543) = F_544
      | ~ m1_subset_1(k1_tmap_1(A_540,B_542,C_539,D_543,E_541,F_544),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_540,C_539,D_543),B_542)))
      | ~ v1_funct_2(k1_tmap_1(A_540,B_542,C_539,D_543,E_541,F_544),k4_subset_1(A_540,C_539,D_543),B_542)
      | ~ v1_funct_1(k1_tmap_1(A_540,B_542,C_539,D_543,E_541,F_544))
      | k2_partfun1(D_543,B_542,F_544,k9_subset_1(A_540,C_539,D_543)) != k2_partfun1(C_539,B_542,E_541,k9_subset_1(A_540,C_539,D_543))
      | ~ m1_subset_1(F_544,k1_zfmisc_1(k2_zfmisc_1(D_543,B_542)))
      | ~ v1_funct_2(F_544,D_543,B_542)
      | ~ v1_funct_1(F_544)
      | ~ m1_subset_1(E_541,k1_zfmisc_1(k2_zfmisc_1(C_539,B_542)))
      | ~ v1_funct_2(E_541,C_539,B_542)
      | ~ v1_funct_1(E_541)
      | ~ m1_subset_1(D_543,k1_zfmisc_1(A_540))
      | v1_xboole_0(D_543)
      | ~ m1_subset_1(C_539,k1_zfmisc_1(A_540))
      | v1_xboole_0(C_539)
      | v1_xboole_0(B_542)
      | v1_xboole_0(A_540) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_5310,plain,(
    ! [E_767,F_764,B_765,A_762,D_763,C_766] :
      ( k2_partfun1(k4_subset_1(A_762,C_766,D_763),B_765,k1_tmap_1(A_762,B_765,C_766,D_763,E_767,F_764),D_763) = F_764
      | ~ v1_funct_2(k1_tmap_1(A_762,B_765,C_766,D_763,E_767,F_764),k4_subset_1(A_762,C_766,D_763),B_765)
      | ~ v1_funct_1(k1_tmap_1(A_762,B_765,C_766,D_763,E_767,F_764))
      | k2_partfun1(D_763,B_765,F_764,k9_subset_1(A_762,C_766,D_763)) != k2_partfun1(C_766,B_765,E_767,k9_subset_1(A_762,C_766,D_763))
      | ~ m1_subset_1(F_764,k1_zfmisc_1(k2_zfmisc_1(D_763,B_765)))
      | ~ v1_funct_2(F_764,D_763,B_765)
      | ~ v1_funct_1(F_764)
      | ~ m1_subset_1(E_767,k1_zfmisc_1(k2_zfmisc_1(C_766,B_765)))
      | ~ v1_funct_2(E_767,C_766,B_765)
      | ~ v1_funct_1(E_767)
      | ~ m1_subset_1(D_763,k1_zfmisc_1(A_762))
      | v1_xboole_0(D_763)
      | ~ m1_subset_1(C_766,k1_zfmisc_1(A_762))
      | v1_xboole_0(C_766)
      | v1_xboole_0(B_765)
      | v1_xboole_0(A_762) ) ),
    inference(resolution,[status(thm)],[c_50,c_3463])).

tff(c_6160,plain,(
    ! [A_849,D_850,B_852,F_851,C_853,E_854] :
      ( k2_partfun1(k4_subset_1(A_849,C_853,D_850),B_852,k1_tmap_1(A_849,B_852,C_853,D_850,E_854,F_851),D_850) = F_851
      | ~ v1_funct_1(k1_tmap_1(A_849,B_852,C_853,D_850,E_854,F_851))
      | k2_partfun1(D_850,B_852,F_851,k9_subset_1(A_849,C_853,D_850)) != k2_partfun1(C_853,B_852,E_854,k9_subset_1(A_849,C_853,D_850))
      | ~ m1_subset_1(F_851,k1_zfmisc_1(k2_zfmisc_1(D_850,B_852)))
      | ~ v1_funct_2(F_851,D_850,B_852)
      | ~ v1_funct_1(F_851)
      | ~ m1_subset_1(E_854,k1_zfmisc_1(k2_zfmisc_1(C_853,B_852)))
      | ~ v1_funct_2(E_854,C_853,B_852)
      | ~ v1_funct_1(E_854)
      | ~ m1_subset_1(D_850,k1_zfmisc_1(A_849))
      | v1_xboole_0(D_850)
      | ~ m1_subset_1(C_853,k1_zfmisc_1(A_849))
      | v1_xboole_0(C_853)
      | v1_xboole_0(B_852)
      | v1_xboole_0(A_849) ) ),
    inference(resolution,[status(thm)],[c_52,c_5310])).

tff(c_6164,plain,(
    ! [A_849,C_853,E_854] :
      ( k2_partfun1(k4_subset_1(A_849,C_853,'#skF_4'),'#skF_2',k1_tmap_1(A_849,'#skF_2',C_853,'#skF_4',E_854,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_849,'#skF_2',C_853,'#skF_4',E_854,'#skF_6'))
      | k2_partfun1(C_853,'#skF_2',E_854,k9_subset_1(A_849,C_853,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_849,C_853,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_854,k1_zfmisc_1(k2_zfmisc_1(C_853,'#skF_2')))
      | ~ v1_funct_2(E_854,C_853,'#skF_2')
      | ~ v1_funct_1(E_854)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_849))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_853,k1_zfmisc_1(A_849))
      | v1_xboole_0(C_853)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_849) ) ),
    inference(resolution,[status(thm)],[c_58,c_6160])).

tff(c_6170,plain,(
    ! [A_849,C_853,E_854] :
      ( k2_partfun1(k4_subset_1(A_849,C_853,'#skF_4'),'#skF_2',k1_tmap_1(A_849,'#skF_2',C_853,'#skF_4',E_854,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_849,'#skF_2',C_853,'#skF_4',E_854,'#skF_6'))
      | k2_partfun1(C_853,'#skF_2',E_854,k9_subset_1(A_849,C_853,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_849,C_853,'#skF_4'))
      | ~ m1_subset_1(E_854,k1_zfmisc_1(k2_zfmisc_1(C_853,'#skF_2')))
      | ~ v1_funct_2(E_854,C_853,'#skF_2')
      | ~ v1_funct_1(E_854)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_849))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_853,k1_zfmisc_1(A_849))
      | v1_xboole_0(C_853)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_849) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_2665,c_6164])).

tff(c_7021,plain,(
    ! [A_932,C_933,E_934] :
      ( k2_partfun1(k4_subset_1(A_932,C_933,'#skF_4'),'#skF_2',k1_tmap_1(A_932,'#skF_2',C_933,'#skF_4',E_934,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_932,'#skF_2',C_933,'#skF_4',E_934,'#skF_6'))
      | k2_partfun1(C_933,'#skF_2',E_934,k9_subset_1(A_932,C_933,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_932,C_933,'#skF_4'))
      | ~ m1_subset_1(E_934,k1_zfmisc_1(k2_zfmisc_1(C_933,'#skF_2')))
      | ~ v1_funct_2(E_934,C_933,'#skF_2')
      | ~ v1_funct_1(E_934)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_932))
      | ~ m1_subset_1(C_933,k1_zfmisc_1(A_932))
      | v1_xboole_0(C_933)
      | v1_xboole_0(A_932) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_6170])).

tff(c_7028,plain,(
    ! [A_932] :
      ( k2_partfun1(k4_subset_1(A_932,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_932,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_932,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_932,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_932,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_932))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_932))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_932) ) ),
    inference(resolution,[status(thm)],[c_64,c_7021])).

tff(c_7038,plain,(
    ! [A_932] :
      ( k2_partfun1(k4_subset_1(A_932,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_932,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_932,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_932,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_932,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_932))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_932))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_932) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_2668,c_7028])).

tff(c_7204,plain,(
    ! [A_954] :
      ( k2_partfun1(k4_subset_1(A_954,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_954,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_954,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_954,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_954,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_954))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_954))
      | v1_xboole_0(A_954) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_7038])).

tff(c_150,plain,(
    ! [C_244,A_245,B_246] :
      ( v4_relat_1(C_244,A_245)
      | ~ m1_subset_1(C_244,k1_zfmisc_1(k2_zfmisc_1(A_245,B_246))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_157,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_150])).

tff(c_18,plain,(
    ! [B_18,A_17] :
      ( k7_relat_1(B_18,A_17) = B_18
      | ~ v4_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_161,plain,
    ( k7_relat_1('#skF_6','#skF_4') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_157,c_18])).

tff(c_164,plain,(
    k7_relat_1('#skF_6','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_161])).

tff(c_304,plain,(
    ! [C_268,A_269,B_270] :
      ( k7_relat_1(k7_relat_1(C_268,A_269),B_270) = k1_xboole_0
      | ~ r1_xboole_0(A_269,B_270)
      | ~ v1_relat_1(C_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_325,plain,(
    ! [B_270] :
      ( k7_relat_1('#skF_6',B_270) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_270)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_304])).

tff(c_1138,plain,(
    ! [B_334] :
      ( k7_relat_1('#skF_6',B_334) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_334) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_325])).

tff(c_1150,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_1138])).

tff(c_158,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_150])).

tff(c_167,plain,
    ( k7_relat_1('#skF_5','#skF_3') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_158,c_18])).

tff(c_170,plain,(
    k7_relat_1('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_167])).

tff(c_322,plain,(
    ! [B_270] :
      ( k7_relat_1('#skF_5',B_270) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_270)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_304])).

tff(c_1107,plain,(
    ! [B_333] :
      ( k7_relat_1('#skF_5',B_333) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_333) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_322])).

tff(c_1119,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_1107])).

tff(c_291,plain,(
    ! [B_266,A_267] :
      ( k1_relat_1(B_266) = A_267
      | ~ v1_partfun1(B_266,A_267)
      | ~ v4_relat_1(B_266,A_267)
      | ~ v1_relat_1(B_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_297,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_157,c_291])).

tff(c_303,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_297])).

tff(c_858,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_303])).

tff(c_1083,plain,(
    ! [C_330,A_331,B_332] :
      ( v1_partfun1(C_330,A_331)
      | ~ v1_funct_2(C_330,A_331,B_332)
      | ~ v1_funct_1(C_330)
      | ~ m1_subset_1(C_330,k1_zfmisc_1(k2_zfmisc_1(A_331,B_332)))
      | v1_xboole_0(B_332) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1086,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_1083])).

tff(c_1092,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1086])).

tff(c_1094,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_858,c_1092])).

tff(c_1095,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_303])).

tff(c_230,plain,(
    ! [B_257,A_258] :
      ( r1_subset_1(B_257,A_258)
      | ~ r1_subset_1(A_258,B_257)
      | v1_xboole_0(B_257)
      | v1_xboole_0(A_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_232,plain,
    ( r1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_230])).

tff(c_235,plain,(
    r1_subset_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_74,c_232])).

tff(c_1142,plain,(
    ! [B_20] :
      ( k7_relat_1('#skF_6',B_20) = k1_xboole_0
      | ~ r1_subset_1('#skF_4',B_20)
      | v1_xboole_0(B_20)
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22,c_1138])).

tff(c_1206,plain,(
    ! [B_339] :
      ( k7_relat_1('#skF_6',B_339) = k1_xboole_0
      | ~ r1_subset_1('#skF_4',B_339)
      | v1_xboole_0(B_339) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1142])).

tff(c_1209,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_235,c_1206])).

tff(c_1212,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1209])).

tff(c_1169,plain,(
    ! [A_335,C_336,B_337] :
      ( k3_xboole_0(A_335,k10_relat_1(C_336,B_337)) = k10_relat_1(k7_relat_1(C_336,A_335),B_337)
      | ~ v1_relat_1(C_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1364,plain,(
    ! [A_354,A_355] :
      ( k10_relat_1(k7_relat_1(A_354,A_355),k2_relat_1(A_354)) = k3_xboole_0(A_355,k1_relat_1(A_354))
      | ~ v1_relat_1(A_354)
      | ~ v1_relat_1(A_354) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1169])).

tff(c_1385,plain,
    ( k3_xboole_0('#skF_3',k1_relat_1('#skF_6')) = k10_relat_1(k1_xboole_0,k2_relat_1('#skF_6'))
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1212,c_1364])).

tff(c_1414,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_107,c_1095,c_14,c_1385])).

tff(c_1266,plain,(
    ! [A_342,B_343,C_344,D_345] :
      ( k2_partfun1(A_342,B_343,C_344,D_345) = k7_relat_1(C_344,D_345)
      | ~ m1_subset_1(C_344,k1_zfmisc_1(k2_zfmisc_1(A_342,B_343)))
      | ~ v1_funct_1(C_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1270,plain,(
    ! [D_345] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_345) = k7_relat_1('#skF_5',D_345)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_64,c_1266])).

tff(c_1276,plain,(
    ! [D_345] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_345) = k7_relat_1('#skF_5',D_345) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1270])).

tff(c_1268,plain,(
    ! [D_345] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_345) = k7_relat_1('#skF_6',D_345)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_58,c_1266])).

tff(c_1273,plain,(
    ! [D_345] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_345) = k7_relat_1('#skF_6',D_345) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1268])).

tff(c_241,plain,(
    ! [A_259,B_260,C_261] :
      ( k9_subset_1(A_259,B_260,C_261) = k3_xboole_0(B_260,C_261)
      | ~ m1_subset_1(C_261,k1_zfmisc_1(A_259)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_252,plain,(
    ! [B_260] : k9_subset_1('#skF_1',B_260,'#skF_4') = k3_xboole_0(B_260,'#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_241])).

tff(c_56,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_109,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_254,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_252,c_109])).

tff(c_1295,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k7_relat_1('#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1273,c_254])).

tff(c_1348,plain,(
    k7_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k7_relat_1('#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1276,c_1295])).

tff(c_1437,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) != k7_relat_1('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1414,c_1414,c_1348])).

tff(c_1440,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1150,c_1119,c_1437])).

tff(c_1441,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1521,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1441])).

tff(c_7215,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_7204,c_1521])).

tff(c_7229,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_2532,c_2923,c_2563,c_2923,c_1590,c_1590,c_3203,c_7215])).

tff(c_7231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_7229])).

tff(c_7232,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1441])).

tff(c_13081,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_13072,c_7232])).

tff(c_13092,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_8619,c_9010,c_8675,c_9010,c_8525,c_8525,c_9265,c_13081])).

tff(c_13094,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_13092])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:04:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.59/4.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.59/4.21  
% 11.59/4.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.59/4.21  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 11.59/4.21  
% 11.59/4.21  %Foreground sorts:
% 11.59/4.21  
% 11.59/4.21  
% 11.59/4.21  %Background operators:
% 11.59/4.21  
% 11.59/4.21  
% 11.59/4.21  %Foreground operators:
% 11.59/4.21  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 11.59/4.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.59/4.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.59/4.21  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 11.59/4.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.59/4.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.59/4.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.59/4.21  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 11.59/4.21  tff('#skF_5', type, '#skF_5': $i).
% 11.59/4.21  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.59/4.21  tff('#skF_6', type, '#skF_6': $i).
% 11.59/4.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.59/4.21  tff('#skF_2', type, '#skF_2': $i).
% 11.59/4.21  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 11.59/4.21  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 11.59/4.21  tff('#skF_3', type, '#skF_3': $i).
% 11.59/4.21  tff('#skF_1', type, '#skF_1': $i).
% 11.59/4.21  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 11.59/4.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.59/4.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.59/4.21  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 11.59/4.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.59/4.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.59/4.21  tff('#skF_4', type, '#skF_4': $i).
% 11.59/4.21  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.59/4.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.59/4.21  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 11.59/4.21  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 11.59/4.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.59/4.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.59/4.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.59/4.21  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 11.59/4.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.59/4.21  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 11.59/4.21  
% 11.86/4.25  tff(f_248, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 11.86/4.25  tff(f_27, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 11.86/4.25  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 11.86/4.25  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 11.86/4.25  tff(f_62, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 11.86/4.25  tff(f_56, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 11.86/4.25  tff(f_118, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 11.86/4.25  tff(f_110, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 11.86/4.25  tff(f_50, axiom, (![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 11.86/4.25  tff(f_82, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) => r1_subset_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_subset_1)).
% 11.86/4.25  tff(f_72, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 11.86/4.25  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 11.86/4.25  tff(f_86, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 11.86/4.25  tff(f_31, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 11.86/4.25  tff(f_206, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 11.86/4.25  tff(f_124, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 11.86/4.25  tff(f_172, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 11.86/4.25  tff(c_82, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_248])).
% 11.86/4.25  tff(c_76, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_248])).
% 11.86/4.25  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_248])).
% 11.86/4.25  tff(c_2, plain, (![A_1]: (r1_xboole_0(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.86/4.25  tff(c_58, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_248])).
% 11.86/4.25  tff(c_100, plain, (![C_236, A_237, B_238]: (v1_relat_1(C_236) | ~m1_subset_1(C_236, k1_zfmisc_1(k2_zfmisc_1(A_237, B_238))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.86/4.25  tff(c_107, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_58, c_100])).
% 11.86/4.25  tff(c_1486, plain, (![C_359, A_360, B_361]: (v4_relat_1(C_359, A_360) | ~m1_subset_1(C_359, k1_zfmisc_1(k2_zfmisc_1(A_360, B_361))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.86/4.25  tff(c_1493, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_1486])).
% 11.86/4.25  tff(c_1504, plain, (![B_365, A_366]: (k7_relat_1(B_365, A_366)=B_365 | ~v4_relat_1(B_365, A_366) | ~v1_relat_1(B_365))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.86/4.25  tff(c_1510, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1493, c_1504])).
% 11.86/4.25  tff(c_1516, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_107, c_1510])).
% 11.86/4.25  tff(c_8564, plain, (![C_1065, A_1066, B_1067]: (k7_relat_1(k7_relat_1(C_1065, A_1066), B_1067)=k1_xboole_0 | ~r1_xboole_0(A_1066, B_1067) | ~v1_relat_1(C_1065))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.86/4.25  tff(c_8582, plain, (![B_1067]: (k7_relat_1('#skF_6', B_1067)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_1067) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1516, c_8564])).
% 11.86/4.25  tff(c_8607, plain, (![B_1071]: (k7_relat_1('#skF_6', B_1071)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_1071))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_8582])).
% 11.86/4.25  tff(c_8619, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_8607])).
% 11.86/4.25  tff(c_80, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_248])).
% 11.86/4.25  tff(c_7291, plain, (![B_964, A_965]: (k1_relat_1(B_964)=A_965 | ~v1_partfun1(B_964, A_965) | ~v4_relat_1(B_964, A_965) | ~v1_relat_1(B_964))), inference(cnfTransformation, [status(thm)], [f_118])).
% 11.86/4.25  tff(c_7297, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1493, c_7291])).
% 11.86/4.25  tff(c_7303, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_7297])).
% 11.86/4.25  tff(c_8106, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_7303])).
% 11.86/4.25  tff(c_62, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_248])).
% 11.86/4.25  tff(c_60, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_248])).
% 11.86/4.25  tff(c_8490, plain, (![C_1055, A_1056, B_1057]: (v1_partfun1(C_1055, A_1056) | ~v1_funct_2(C_1055, A_1056, B_1057) | ~v1_funct_1(C_1055) | ~m1_subset_1(C_1055, k1_zfmisc_1(k2_zfmisc_1(A_1056, B_1057))) | v1_xboole_0(B_1057))), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.86/4.25  tff(c_8493, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_8490])).
% 11.86/4.25  tff(c_8499, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_8493])).
% 11.86/4.25  tff(c_8501, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_8106, c_8499])).
% 11.86/4.25  tff(c_8502, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_7303])).
% 11.86/4.25  tff(c_14, plain, (![A_13]: (k10_relat_1(k1_xboole_0, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.86/4.25  tff(c_78, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_248])).
% 11.86/4.25  tff(c_74, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_248])).
% 11.86/4.25  tff(c_70, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_248])).
% 11.86/4.25  tff(c_7268, plain, (![B_957, A_958]: (r1_subset_1(B_957, A_958) | ~r1_subset_1(A_958, B_957) | v1_xboole_0(B_957) | v1_xboole_0(A_958))), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.86/4.25  tff(c_7270, plain, (r1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_70, c_7268])).
% 11.86/4.25  tff(c_7273, plain, (r1_subset_1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_78, c_74, c_7270])).
% 11.86/4.25  tff(c_22, plain, (![A_19, B_20]: (r1_xboole_0(A_19, B_20) | ~r1_subset_1(A_19, B_20) | v1_xboole_0(B_20) | v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.86/4.25  tff(c_8611, plain, (![B_20]: (k7_relat_1('#skF_6', B_20)=k1_xboole_0 | ~r1_subset_1('#skF_4', B_20) | v1_xboole_0(B_20) | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_22, c_8607])).
% 11.86/4.25  tff(c_8638, plain, (![B_1072]: (k7_relat_1('#skF_6', B_1072)=k1_xboole_0 | ~r1_subset_1('#skF_4', B_1072) | v1_xboole_0(B_1072))), inference(negUnitSimplification, [status(thm)], [c_74, c_8611])).
% 11.86/4.25  tff(c_8641, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_7273, c_8638])).
% 11.86/4.25  tff(c_8644, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_78, c_8641])).
% 11.86/4.25  tff(c_12, plain, (![A_12]: (k10_relat_1(A_12, k2_relat_1(A_12))=k1_relat_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.86/4.25  tff(c_8592, plain, (![A_1068, C_1069, B_1070]: (k3_xboole_0(A_1068, k10_relat_1(C_1069, B_1070))=k10_relat_1(k7_relat_1(C_1069, A_1068), B_1070) | ~v1_relat_1(C_1069))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.86/4.25  tff(c_8945, plain, (![A_1096, A_1097]: (k10_relat_1(k7_relat_1(A_1096, A_1097), k2_relat_1(A_1096))=k3_xboole_0(A_1097, k1_relat_1(A_1096)) | ~v1_relat_1(A_1096) | ~v1_relat_1(A_1096))), inference(superposition, [status(thm), theory('equality')], [c_12, c_8592])).
% 11.86/4.25  tff(c_8981, plain, (k3_xboole_0('#skF_3', k1_relat_1('#skF_6'))=k10_relat_1(k1_xboole_0, k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_8644, c_8945])).
% 11.86/4.25  tff(c_9010, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_107, c_107, c_8502, c_14, c_8981])).
% 11.86/4.25  tff(c_64, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_248])).
% 11.86/4.25  tff(c_108, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_100])).
% 11.86/4.25  tff(c_1494, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_64, c_1486])).
% 11.86/4.25  tff(c_1507, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1494, c_1504])).
% 11.86/4.25  tff(c_1513, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_1507])).
% 11.86/4.25  tff(c_8585, plain, (![B_1067]: (k7_relat_1('#skF_5', B_1067)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_1067) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1513, c_8564])).
% 11.86/4.25  tff(c_8663, plain, (![B_1073]: (k7_relat_1('#skF_5', B_1073)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_1073))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_8585])).
% 11.86/4.25  tff(c_8675, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_8663])).
% 11.86/4.25  tff(c_8514, plain, (![A_1058, B_1059, C_1060]: (k9_subset_1(A_1058, B_1059, C_1060)=k3_xboole_0(B_1059, C_1060) | ~m1_subset_1(C_1060, k1_zfmisc_1(A_1058)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.86/4.25  tff(c_8525, plain, (![B_1059]: (k9_subset_1('#skF_1', B_1059, '#skF_4')=k3_xboole_0(B_1059, '#skF_4'))), inference(resolution, [status(thm)], [c_72, c_8514])).
% 11.86/4.25  tff(c_68, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_248])).
% 11.86/4.25  tff(c_66, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_248])).
% 11.86/4.25  tff(c_8885, plain, (![E_1094, F_1091, D_1090, A_1089, C_1093, B_1092]: (v1_funct_1(k1_tmap_1(A_1089, B_1092, C_1093, D_1090, E_1094, F_1091)) | ~m1_subset_1(F_1091, k1_zfmisc_1(k2_zfmisc_1(D_1090, B_1092))) | ~v1_funct_2(F_1091, D_1090, B_1092) | ~v1_funct_1(F_1091) | ~m1_subset_1(E_1094, k1_zfmisc_1(k2_zfmisc_1(C_1093, B_1092))) | ~v1_funct_2(E_1094, C_1093, B_1092) | ~v1_funct_1(E_1094) | ~m1_subset_1(D_1090, k1_zfmisc_1(A_1089)) | v1_xboole_0(D_1090) | ~m1_subset_1(C_1093, k1_zfmisc_1(A_1089)) | v1_xboole_0(C_1093) | v1_xboole_0(B_1092) | v1_xboole_0(A_1089))), inference(cnfTransformation, [status(thm)], [f_206])).
% 11.86/4.25  tff(c_8887, plain, (![A_1089, C_1093, E_1094]: (v1_funct_1(k1_tmap_1(A_1089, '#skF_2', C_1093, '#skF_4', E_1094, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1094, k1_zfmisc_1(k2_zfmisc_1(C_1093, '#skF_2'))) | ~v1_funct_2(E_1094, C_1093, '#skF_2') | ~v1_funct_1(E_1094) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1089)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1093, k1_zfmisc_1(A_1089)) | v1_xboole_0(C_1093) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1089))), inference(resolution, [status(thm)], [c_58, c_8885])).
% 11.86/4.25  tff(c_8892, plain, (![A_1089, C_1093, E_1094]: (v1_funct_1(k1_tmap_1(A_1089, '#skF_2', C_1093, '#skF_4', E_1094, '#skF_6')) | ~m1_subset_1(E_1094, k1_zfmisc_1(k2_zfmisc_1(C_1093, '#skF_2'))) | ~v1_funct_2(E_1094, C_1093, '#skF_2') | ~v1_funct_1(E_1094) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1089)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1093, k1_zfmisc_1(A_1089)) | v1_xboole_0(C_1093) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1089))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_8887])).
% 11.86/4.25  tff(c_9018, plain, (![A_1098, C_1099, E_1100]: (v1_funct_1(k1_tmap_1(A_1098, '#skF_2', C_1099, '#skF_4', E_1100, '#skF_6')) | ~m1_subset_1(E_1100, k1_zfmisc_1(k2_zfmisc_1(C_1099, '#skF_2'))) | ~v1_funct_2(E_1100, C_1099, '#skF_2') | ~v1_funct_1(E_1100) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1098)) | ~m1_subset_1(C_1099, k1_zfmisc_1(A_1098)) | v1_xboole_0(C_1099) | v1_xboole_0(A_1098))), inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_8892])).
% 11.86/4.25  tff(c_9022, plain, (![A_1098]: (v1_funct_1(k1_tmap_1(A_1098, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1098)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1098)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1098))), inference(resolution, [status(thm)], [c_64, c_9018])).
% 11.86/4.25  tff(c_9029, plain, (![A_1098]: (v1_funct_1(k1_tmap_1(A_1098, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1098)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1098)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1098))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_9022])).
% 11.86/4.25  tff(c_9258, plain, (![A_1116]: (v1_funct_1(k1_tmap_1(A_1116, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1116)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1116)) | v1_xboole_0(A_1116))), inference(negUnitSimplification, [status(thm)], [c_78, c_9029])).
% 11.86/4.25  tff(c_9261, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_76, c_9258])).
% 11.86/4.25  tff(c_9264, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_9261])).
% 11.86/4.25  tff(c_9265, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_82, c_9264])).
% 11.86/4.25  tff(c_8694, plain, (![A_1074, B_1075, C_1076, D_1077]: (k2_partfun1(A_1074, B_1075, C_1076, D_1077)=k7_relat_1(C_1076, D_1077) | ~m1_subset_1(C_1076, k1_zfmisc_1(k2_zfmisc_1(A_1074, B_1075))) | ~v1_funct_1(C_1076))), inference(cnfTransformation, [status(thm)], [f_124])).
% 11.86/4.25  tff(c_8698, plain, (![D_1077]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_1077)=k7_relat_1('#skF_5', D_1077) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_64, c_8694])).
% 11.86/4.25  tff(c_8704, plain, (![D_1077]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_1077)=k7_relat_1('#skF_5', D_1077))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_8698])).
% 11.86/4.25  tff(c_8696, plain, (![D_1077]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_1077)=k7_relat_1('#skF_6', D_1077) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_58, c_8694])).
% 11.86/4.25  tff(c_8701, plain, (![D_1077]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_1077)=k7_relat_1('#skF_6', D_1077))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_8696])).
% 11.86/4.25  tff(c_52, plain, (![C_171, E_173, F_174, D_172, A_169, B_170]: (v1_funct_2(k1_tmap_1(A_169, B_170, C_171, D_172, E_173, F_174), k4_subset_1(A_169, C_171, D_172), B_170) | ~m1_subset_1(F_174, k1_zfmisc_1(k2_zfmisc_1(D_172, B_170))) | ~v1_funct_2(F_174, D_172, B_170) | ~v1_funct_1(F_174) | ~m1_subset_1(E_173, k1_zfmisc_1(k2_zfmisc_1(C_171, B_170))) | ~v1_funct_2(E_173, C_171, B_170) | ~v1_funct_1(E_173) | ~m1_subset_1(D_172, k1_zfmisc_1(A_169)) | v1_xboole_0(D_172) | ~m1_subset_1(C_171, k1_zfmisc_1(A_169)) | v1_xboole_0(C_171) | v1_xboole_0(B_170) | v1_xboole_0(A_169))), inference(cnfTransformation, [status(thm)], [f_206])).
% 11.86/4.25  tff(c_50, plain, (![C_171, E_173, F_174, D_172, A_169, B_170]: (m1_subset_1(k1_tmap_1(A_169, B_170, C_171, D_172, E_173, F_174), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_169, C_171, D_172), B_170))) | ~m1_subset_1(F_174, k1_zfmisc_1(k2_zfmisc_1(D_172, B_170))) | ~v1_funct_2(F_174, D_172, B_170) | ~v1_funct_1(F_174) | ~m1_subset_1(E_173, k1_zfmisc_1(k2_zfmisc_1(C_171, B_170))) | ~v1_funct_2(E_173, C_171, B_170) | ~v1_funct_1(E_173) | ~m1_subset_1(D_172, k1_zfmisc_1(A_169)) | v1_xboole_0(D_172) | ~m1_subset_1(C_171, k1_zfmisc_1(A_169)) | v1_xboole_0(C_171) | v1_xboole_0(B_170) | v1_xboole_0(A_169))), inference(cnfTransformation, [status(thm)], [f_206])).
% 11.86/4.25  tff(c_9318, plain, (![F_1126, B_1124, C_1121, A_1122, E_1123, D_1125]: (k2_partfun1(k4_subset_1(A_1122, C_1121, D_1125), B_1124, k1_tmap_1(A_1122, B_1124, C_1121, D_1125, E_1123, F_1126), C_1121)=E_1123 | ~m1_subset_1(k1_tmap_1(A_1122, B_1124, C_1121, D_1125, E_1123, F_1126), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1122, C_1121, D_1125), B_1124))) | ~v1_funct_2(k1_tmap_1(A_1122, B_1124, C_1121, D_1125, E_1123, F_1126), k4_subset_1(A_1122, C_1121, D_1125), B_1124) | ~v1_funct_1(k1_tmap_1(A_1122, B_1124, C_1121, D_1125, E_1123, F_1126)) | k2_partfun1(D_1125, B_1124, F_1126, k9_subset_1(A_1122, C_1121, D_1125))!=k2_partfun1(C_1121, B_1124, E_1123, k9_subset_1(A_1122, C_1121, D_1125)) | ~m1_subset_1(F_1126, k1_zfmisc_1(k2_zfmisc_1(D_1125, B_1124))) | ~v1_funct_2(F_1126, D_1125, B_1124) | ~v1_funct_1(F_1126) | ~m1_subset_1(E_1123, k1_zfmisc_1(k2_zfmisc_1(C_1121, B_1124))) | ~v1_funct_2(E_1123, C_1121, B_1124) | ~v1_funct_1(E_1123) | ~m1_subset_1(D_1125, k1_zfmisc_1(A_1122)) | v1_xboole_0(D_1125) | ~m1_subset_1(C_1121, k1_zfmisc_1(A_1122)) | v1_xboole_0(C_1121) | v1_xboole_0(B_1124) | v1_xboole_0(A_1122))), inference(cnfTransformation, [status(thm)], [f_172])).
% 11.86/4.25  tff(c_10952, plain, (![B_1344, A_1341, C_1345, F_1343, D_1342, E_1346]: (k2_partfun1(k4_subset_1(A_1341, C_1345, D_1342), B_1344, k1_tmap_1(A_1341, B_1344, C_1345, D_1342, E_1346, F_1343), C_1345)=E_1346 | ~v1_funct_2(k1_tmap_1(A_1341, B_1344, C_1345, D_1342, E_1346, F_1343), k4_subset_1(A_1341, C_1345, D_1342), B_1344) | ~v1_funct_1(k1_tmap_1(A_1341, B_1344, C_1345, D_1342, E_1346, F_1343)) | k2_partfun1(D_1342, B_1344, F_1343, k9_subset_1(A_1341, C_1345, D_1342))!=k2_partfun1(C_1345, B_1344, E_1346, k9_subset_1(A_1341, C_1345, D_1342)) | ~m1_subset_1(F_1343, k1_zfmisc_1(k2_zfmisc_1(D_1342, B_1344))) | ~v1_funct_2(F_1343, D_1342, B_1344) | ~v1_funct_1(F_1343) | ~m1_subset_1(E_1346, k1_zfmisc_1(k2_zfmisc_1(C_1345, B_1344))) | ~v1_funct_2(E_1346, C_1345, B_1344) | ~v1_funct_1(E_1346) | ~m1_subset_1(D_1342, k1_zfmisc_1(A_1341)) | v1_xboole_0(D_1342) | ~m1_subset_1(C_1345, k1_zfmisc_1(A_1341)) | v1_xboole_0(C_1345) | v1_xboole_0(B_1344) | v1_xboole_0(A_1341))), inference(resolution, [status(thm)], [c_50, c_9318])).
% 11.86/4.25  tff(c_12401, plain, (![C_1468, F_1466, B_1467, A_1464, E_1469, D_1465]: (k2_partfun1(k4_subset_1(A_1464, C_1468, D_1465), B_1467, k1_tmap_1(A_1464, B_1467, C_1468, D_1465, E_1469, F_1466), C_1468)=E_1469 | ~v1_funct_1(k1_tmap_1(A_1464, B_1467, C_1468, D_1465, E_1469, F_1466)) | k2_partfun1(D_1465, B_1467, F_1466, k9_subset_1(A_1464, C_1468, D_1465))!=k2_partfun1(C_1468, B_1467, E_1469, k9_subset_1(A_1464, C_1468, D_1465)) | ~m1_subset_1(F_1466, k1_zfmisc_1(k2_zfmisc_1(D_1465, B_1467))) | ~v1_funct_2(F_1466, D_1465, B_1467) | ~v1_funct_1(F_1466) | ~m1_subset_1(E_1469, k1_zfmisc_1(k2_zfmisc_1(C_1468, B_1467))) | ~v1_funct_2(E_1469, C_1468, B_1467) | ~v1_funct_1(E_1469) | ~m1_subset_1(D_1465, k1_zfmisc_1(A_1464)) | v1_xboole_0(D_1465) | ~m1_subset_1(C_1468, k1_zfmisc_1(A_1464)) | v1_xboole_0(C_1468) | v1_xboole_0(B_1467) | v1_xboole_0(A_1464))), inference(resolution, [status(thm)], [c_52, c_10952])).
% 11.86/4.25  tff(c_12405, plain, (![A_1464, C_1468, E_1469]: (k2_partfun1(k4_subset_1(A_1464, C_1468, '#skF_4'), '#skF_2', k1_tmap_1(A_1464, '#skF_2', C_1468, '#skF_4', E_1469, '#skF_6'), C_1468)=E_1469 | ~v1_funct_1(k1_tmap_1(A_1464, '#skF_2', C_1468, '#skF_4', E_1469, '#skF_6')) | k2_partfun1(C_1468, '#skF_2', E_1469, k9_subset_1(A_1464, C_1468, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_1464, C_1468, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1469, k1_zfmisc_1(k2_zfmisc_1(C_1468, '#skF_2'))) | ~v1_funct_2(E_1469, C_1468, '#skF_2') | ~v1_funct_1(E_1469) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1464)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1468, k1_zfmisc_1(A_1464)) | v1_xboole_0(C_1468) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1464))), inference(resolution, [status(thm)], [c_58, c_12401])).
% 11.86/4.25  tff(c_12411, plain, (![A_1464, C_1468, E_1469]: (k2_partfun1(k4_subset_1(A_1464, C_1468, '#skF_4'), '#skF_2', k1_tmap_1(A_1464, '#skF_2', C_1468, '#skF_4', E_1469, '#skF_6'), C_1468)=E_1469 | ~v1_funct_1(k1_tmap_1(A_1464, '#skF_2', C_1468, '#skF_4', E_1469, '#skF_6')) | k2_partfun1(C_1468, '#skF_2', E_1469, k9_subset_1(A_1464, C_1468, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1464, C_1468, '#skF_4')) | ~m1_subset_1(E_1469, k1_zfmisc_1(k2_zfmisc_1(C_1468, '#skF_2'))) | ~v1_funct_2(E_1469, C_1468, '#skF_2') | ~v1_funct_1(E_1469) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1464)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1468, k1_zfmisc_1(A_1464)) | v1_xboole_0(C_1468) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1464))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_8701, c_12405])).
% 11.86/4.25  tff(c_12939, plain, (![A_1525, C_1526, E_1527]: (k2_partfun1(k4_subset_1(A_1525, C_1526, '#skF_4'), '#skF_2', k1_tmap_1(A_1525, '#skF_2', C_1526, '#skF_4', E_1527, '#skF_6'), C_1526)=E_1527 | ~v1_funct_1(k1_tmap_1(A_1525, '#skF_2', C_1526, '#skF_4', E_1527, '#skF_6')) | k2_partfun1(C_1526, '#skF_2', E_1527, k9_subset_1(A_1525, C_1526, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1525, C_1526, '#skF_4')) | ~m1_subset_1(E_1527, k1_zfmisc_1(k2_zfmisc_1(C_1526, '#skF_2'))) | ~v1_funct_2(E_1527, C_1526, '#skF_2') | ~v1_funct_1(E_1527) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1525)) | ~m1_subset_1(C_1526, k1_zfmisc_1(A_1525)) | v1_xboole_0(C_1526) | v1_xboole_0(A_1525))), inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_12411])).
% 11.86/4.25  tff(c_12946, plain, (![A_1525]: (k2_partfun1(k4_subset_1(A_1525, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1525, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1525, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_1525, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1525, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1525)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1525)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1525))), inference(resolution, [status(thm)], [c_64, c_12939])).
% 11.86/4.25  tff(c_12956, plain, (![A_1525]: (k2_partfun1(k4_subset_1(A_1525, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1525, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1525, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1525, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1525, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1525)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1525)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1525))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_8704, c_12946])).
% 11.86/4.25  tff(c_13072, plain, (![A_1547]: (k2_partfun1(k4_subset_1(A_1547, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1547, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1547, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1547, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1547, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1547)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1547)) | v1_xboole_0(A_1547))), inference(negUnitSimplification, [status(thm)], [c_78, c_12956])).
% 11.86/4.25  tff(c_2492, plain, (![C_458, A_459, B_460]: (k7_relat_1(k7_relat_1(C_458, A_459), B_460)=k1_xboole_0 | ~r1_xboole_0(A_459, B_460) | ~v1_relat_1(C_458))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.86/4.25  tff(c_2510, plain, (![B_460]: (k7_relat_1('#skF_6', B_460)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_460) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1516, c_2492])).
% 11.86/4.25  tff(c_2520, plain, (![B_461]: (k7_relat_1('#skF_6', B_461)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_461))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_2510])).
% 11.86/4.25  tff(c_2532, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_2520])).
% 11.86/4.25  tff(c_1611, plain, (![B_381, A_382]: (k1_relat_1(B_381)=A_382 | ~v1_partfun1(B_381, A_382) | ~v4_relat_1(B_381, A_382) | ~v1_relat_1(B_381))), inference(cnfTransformation, [status(thm)], [f_118])).
% 11.86/4.25  tff(c_1617, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1493, c_1611])).
% 11.86/4.25  tff(c_1623, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_1617])).
% 11.86/4.25  tff(c_2215, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_1623])).
% 11.86/4.25  tff(c_2459, plain, (![C_454, A_455, B_456]: (v1_partfun1(C_454, A_455) | ~v1_funct_2(C_454, A_455, B_456) | ~v1_funct_1(C_454) | ~m1_subset_1(C_454, k1_zfmisc_1(k2_zfmisc_1(A_455, B_456))) | v1_xboole_0(B_456))), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.86/4.25  tff(c_2462, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_2459])).
% 11.86/4.25  tff(c_2468, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_2462])).
% 11.86/4.25  tff(c_2470, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_2215, c_2468])).
% 11.86/4.25  tff(c_2471, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_1623])).
% 11.86/4.25  tff(c_1557, plain, (![B_371, A_372]: (r1_subset_1(B_371, A_372) | ~r1_subset_1(A_372, B_371) | v1_xboole_0(B_371) | v1_xboole_0(A_372))), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.86/4.25  tff(c_1559, plain, (r1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_70, c_1557])).
% 11.86/4.25  tff(c_1562, plain, (r1_subset_1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_78, c_74, c_1559])).
% 11.86/4.25  tff(c_2524, plain, (![B_20]: (k7_relat_1('#skF_6', B_20)=k1_xboole_0 | ~r1_subset_1('#skF_4', B_20) | v1_xboole_0(B_20) | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_22, c_2520])).
% 11.86/4.25  tff(c_2609, plain, (![B_467]: (k7_relat_1('#skF_6', B_467)=k1_xboole_0 | ~r1_subset_1('#skF_4', B_467) | v1_xboole_0(B_467))), inference(negUnitSimplification, [status(thm)], [c_74, c_2524])).
% 11.86/4.25  tff(c_2612, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_1562, c_2609])).
% 11.86/4.25  tff(c_2615, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_78, c_2612])).
% 11.86/4.25  tff(c_2564, plain, (![A_463, C_464, B_465]: (k3_xboole_0(A_463, k10_relat_1(C_464, B_465))=k10_relat_1(k7_relat_1(C_464, A_463), B_465) | ~v1_relat_1(C_464))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.86/4.25  tff(c_2860, plain, (![A_483, A_484]: (k10_relat_1(k7_relat_1(A_483, A_484), k2_relat_1(A_483))=k3_xboole_0(A_484, k1_relat_1(A_483)) | ~v1_relat_1(A_483) | ~v1_relat_1(A_483))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2564])).
% 11.86/4.25  tff(c_2893, plain, (k3_xboole_0('#skF_3', k1_relat_1('#skF_6'))=k10_relat_1(k1_xboole_0, k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2615, c_2860])).
% 11.86/4.25  tff(c_2923, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_107, c_107, c_2471, c_14, c_2893])).
% 11.86/4.25  tff(c_2513, plain, (![B_460]: (k7_relat_1('#skF_5', B_460)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_460) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1513, c_2492])).
% 11.86/4.25  tff(c_2551, plain, (![B_462]: (k7_relat_1('#skF_5', B_462)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_462))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_2513])).
% 11.86/4.25  tff(c_2563, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_2551])).
% 11.86/4.25  tff(c_1579, plain, (![A_376, B_377, C_378]: (k9_subset_1(A_376, B_377, C_378)=k3_xboole_0(B_377, C_378) | ~m1_subset_1(C_378, k1_zfmisc_1(A_376)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.86/4.25  tff(c_1590, plain, (![B_377]: (k9_subset_1('#skF_1', B_377, '#skF_4')=k3_xboole_0(B_377, '#skF_4'))), inference(resolution, [status(thm)], [c_72, c_1579])).
% 11.86/4.25  tff(c_2937, plain, (![D_486, E_490, A_485, B_488, C_489, F_487]: (v1_funct_1(k1_tmap_1(A_485, B_488, C_489, D_486, E_490, F_487)) | ~m1_subset_1(F_487, k1_zfmisc_1(k2_zfmisc_1(D_486, B_488))) | ~v1_funct_2(F_487, D_486, B_488) | ~v1_funct_1(F_487) | ~m1_subset_1(E_490, k1_zfmisc_1(k2_zfmisc_1(C_489, B_488))) | ~v1_funct_2(E_490, C_489, B_488) | ~v1_funct_1(E_490) | ~m1_subset_1(D_486, k1_zfmisc_1(A_485)) | v1_xboole_0(D_486) | ~m1_subset_1(C_489, k1_zfmisc_1(A_485)) | v1_xboole_0(C_489) | v1_xboole_0(B_488) | v1_xboole_0(A_485))), inference(cnfTransformation, [status(thm)], [f_206])).
% 11.86/4.25  tff(c_2939, plain, (![A_485, C_489, E_490]: (v1_funct_1(k1_tmap_1(A_485, '#skF_2', C_489, '#skF_4', E_490, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_490, k1_zfmisc_1(k2_zfmisc_1(C_489, '#skF_2'))) | ~v1_funct_2(E_490, C_489, '#skF_2') | ~v1_funct_1(E_490) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_485)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_489, k1_zfmisc_1(A_485)) | v1_xboole_0(C_489) | v1_xboole_0('#skF_2') | v1_xboole_0(A_485))), inference(resolution, [status(thm)], [c_58, c_2937])).
% 11.86/4.25  tff(c_2944, plain, (![A_485, C_489, E_490]: (v1_funct_1(k1_tmap_1(A_485, '#skF_2', C_489, '#skF_4', E_490, '#skF_6')) | ~m1_subset_1(E_490, k1_zfmisc_1(k2_zfmisc_1(C_489, '#skF_2'))) | ~v1_funct_2(E_490, C_489, '#skF_2') | ~v1_funct_1(E_490) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_485)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_489, k1_zfmisc_1(A_485)) | v1_xboole_0(C_489) | v1_xboole_0('#skF_2') | v1_xboole_0(A_485))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_2939])).
% 11.86/4.25  tff(c_2970, plain, (![A_491, C_492, E_493]: (v1_funct_1(k1_tmap_1(A_491, '#skF_2', C_492, '#skF_4', E_493, '#skF_6')) | ~m1_subset_1(E_493, k1_zfmisc_1(k2_zfmisc_1(C_492, '#skF_2'))) | ~v1_funct_2(E_493, C_492, '#skF_2') | ~v1_funct_1(E_493) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_491)) | ~m1_subset_1(C_492, k1_zfmisc_1(A_491)) | v1_xboole_0(C_492) | v1_xboole_0(A_491))), inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_2944])).
% 11.86/4.25  tff(c_2974, plain, (![A_491]: (v1_funct_1(k1_tmap_1(A_491, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_491)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_491)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_491))), inference(resolution, [status(thm)], [c_64, c_2970])).
% 11.86/4.25  tff(c_2981, plain, (![A_491]: (v1_funct_1(k1_tmap_1(A_491, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_491)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_491)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_491))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_2974])).
% 11.86/4.25  tff(c_3196, plain, (![A_513]: (v1_funct_1(k1_tmap_1(A_513, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_513)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_513)) | v1_xboole_0(A_513))), inference(negUnitSimplification, [status(thm)], [c_78, c_2981])).
% 11.86/4.25  tff(c_3199, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_76, c_3196])).
% 11.86/4.25  tff(c_3202, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_3199])).
% 11.86/4.25  tff(c_3203, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_82, c_3202])).
% 11.86/4.25  tff(c_2658, plain, (![A_469, B_470, C_471, D_472]: (k2_partfun1(A_469, B_470, C_471, D_472)=k7_relat_1(C_471, D_472) | ~m1_subset_1(C_471, k1_zfmisc_1(k2_zfmisc_1(A_469, B_470))) | ~v1_funct_1(C_471))), inference(cnfTransformation, [status(thm)], [f_124])).
% 11.86/4.25  tff(c_2662, plain, (![D_472]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_472)=k7_relat_1('#skF_5', D_472) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_64, c_2658])).
% 11.86/4.25  tff(c_2668, plain, (![D_472]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_472)=k7_relat_1('#skF_5', D_472))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2662])).
% 11.86/4.25  tff(c_2660, plain, (![D_472]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_472)=k7_relat_1('#skF_6', D_472) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_58, c_2658])).
% 11.86/4.25  tff(c_2665, plain, (![D_472]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_472)=k7_relat_1('#skF_6', D_472))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2660])).
% 11.86/4.25  tff(c_3463, plain, (![C_539, D_543, A_540, E_541, F_544, B_542]: (k2_partfun1(k4_subset_1(A_540, C_539, D_543), B_542, k1_tmap_1(A_540, B_542, C_539, D_543, E_541, F_544), D_543)=F_544 | ~m1_subset_1(k1_tmap_1(A_540, B_542, C_539, D_543, E_541, F_544), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_540, C_539, D_543), B_542))) | ~v1_funct_2(k1_tmap_1(A_540, B_542, C_539, D_543, E_541, F_544), k4_subset_1(A_540, C_539, D_543), B_542) | ~v1_funct_1(k1_tmap_1(A_540, B_542, C_539, D_543, E_541, F_544)) | k2_partfun1(D_543, B_542, F_544, k9_subset_1(A_540, C_539, D_543))!=k2_partfun1(C_539, B_542, E_541, k9_subset_1(A_540, C_539, D_543)) | ~m1_subset_1(F_544, k1_zfmisc_1(k2_zfmisc_1(D_543, B_542))) | ~v1_funct_2(F_544, D_543, B_542) | ~v1_funct_1(F_544) | ~m1_subset_1(E_541, k1_zfmisc_1(k2_zfmisc_1(C_539, B_542))) | ~v1_funct_2(E_541, C_539, B_542) | ~v1_funct_1(E_541) | ~m1_subset_1(D_543, k1_zfmisc_1(A_540)) | v1_xboole_0(D_543) | ~m1_subset_1(C_539, k1_zfmisc_1(A_540)) | v1_xboole_0(C_539) | v1_xboole_0(B_542) | v1_xboole_0(A_540))), inference(cnfTransformation, [status(thm)], [f_172])).
% 11.86/4.25  tff(c_5310, plain, (![E_767, F_764, B_765, A_762, D_763, C_766]: (k2_partfun1(k4_subset_1(A_762, C_766, D_763), B_765, k1_tmap_1(A_762, B_765, C_766, D_763, E_767, F_764), D_763)=F_764 | ~v1_funct_2(k1_tmap_1(A_762, B_765, C_766, D_763, E_767, F_764), k4_subset_1(A_762, C_766, D_763), B_765) | ~v1_funct_1(k1_tmap_1(A_762, B_765, C_766, D_763, E_767, F_764)) | k2_partfun1(D_763, B_765, F_764, k9_subset_1(A_762, C_766, D_763))!=k2_partfun1(C_766, B_765, E_767, k9_subset_1(A_762, C_766, D_763)) | ~m1_subset_1(F_764, k1_zfmisc_1(k2_zfmisc_1(D_763, B_765))) | ~v1_funct_2(F_764, D_763, B_765) | ~v1_funct_1(F_764) | ~m1_subset_1(E_767, k1_zfmisc_1(k2_zfmisc_1(C_766, B_765))) | ~v1_funct_2(E_767, C_766, B_765) | ~v1_funct_1(E_767) | ~m1_subset_1(D_763, k1_zfmisc_1(A_762)) | v1_xboole_0(D_763) | ~m1_subset_1(C_766, k1_zfmisc_1(A_762)) | v1_xboole_0(C_766) | v1_xboole_0(B_765) | v1_xboole_0(A_762))), inference(resolution, [status(thm)], [c_50, c_3463])).
% 11.86/4.25  tff(c_6160, plain, (![A_849, D_850, B_852, F_851, C_853, E_854]: (k2_partfun1(k4_subset_1(A_849, C_853, D_850), B_852, k1_tmap_1(A_849, B_852, C_853, D_850, E_854, F_851), D_850)=F_851 | ~v1_funct_1(k1_tmap_1(A_849, B_852, C_853, D_850, E_854, F_851)) | k2_partfun1(D_850, B_852, F_851, k9_subset_1(A_849, C_853, D_850))!=k2_partfun1(C_853, B_852, E_854, k9_subset_1(A_849, C_853, D_850)) | ~m1_subset_1(F_851, k1_zfmisc_1(k2_zfmisc_1(D_850, B_852))) | ~v1_funct_2(F_851, D_850, B_852) | ~v1_funct_1(F_851) | ~m1_subset_1(E_854, k1_zfmisc_1(k2_zfmisc_1(C_853, B_852))) | ~v1_funct_2(E_854, C_853, B_852) | ~v1_funct_1(E_854) | ~m1_subset_1(D_850, k1_zfmisc_1(A_849)) | v1_xboole_0(D_850) | ~m1_subset_1(C_853, k1_zfmisc_1(A_849)) | v1_xboole_0(C_853) | v1_xboole_0(B_852) | v1_xboole_0(A_849))), inference(resolution, [status(thm)], [c_52, c_5310])).
% 11.86/4.25  tff(c_6164, plain, (![A_849, C_853, E_854]: (k2_partfun1(k4_subset_1(A_849, C_853, '#skF_4'), '#skF_2', k1_tmap_1(A_849, '#skF_2', C_853, '#skF_4', E_854, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_849, '#skF_2', C_853, '#skF_4', E_854, '#skF_6')) | k2_partfun1(C_853, '#skF_2', E_854, k9_subset_1(A_849, C_853, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_849, C_853, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_854, k1_zfmisc_1(k2_zfmisc_1(C_853, '#skF_2'))) | ~v1_funct_2(E_854, C_853, '#skF_2') | ~v1_funct_1(E_854) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_849)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_853, k1_zfmisc_1(A_849)) | v1_xboole_0(C_853) | v1_xboole_0('#skF_2') | v1_xboole_0(A_849))), inference(resolution, [status(thm)], [c_58, c_6160])).
% 11.86/4.25  tff(c_6170, plain, (![A_849, C_853, E_854]: (k2_partfun1(k4_subset_1(A_849, C_853, '#skF_4'), '#skF_2', k1_tmap_1(A_849, '#skF_2', C_853, '#skF_4', E_854, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_849, '#skF_2', C_853, '#skF_4', E_854, '#skF_6')) | k2_partfun1(C_853, '#skF_2', E_854, k9_subset_1(A_849, C_853, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_849, C_853, '#skF_4')) | ~m1_subset_1(E_854, k1_zfmisc_1(k2_zfmisc_1(C_853, '#skF_2'))) | ~v1_funct_2(E_854, C_853, '#skF_2') | ~v1_funct_1(E_854) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_849)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_853, k1_zfmisc_1(A_849)) | v1_xboole_0(C_853) | v1_xboole_0('#skF_2') | v1_xboole_0(A_849))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_2665, c_6164])).
% 11.86/4.25  tff(c_7021, plain, (![A_932, C_933, E_934]: (k2_partfun1(k4_subset_1(A_932, C_933, '#skF_4'), '#skF_2', k1_tmap_1(A_932, '#skF_2', C_933, '#skF_4', E_934, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_932, '#skF_2', C_933, '#skF_4', E_934, '#skF_6')) | k2_partfun1(C_933, '#skF_2', E_934, k9_subset_1(A_932, C_933, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_932, C_933, '#skF_4')) | ~m1_subset_1(E_934, k1_zfmisc_1(k2_zfmisc_1(C_933, '#skF_2'))) | ~v1_funct_2(E_934, C_933, '#skF_2') | ~v1_funct_1(E_934) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_932)) | ~m1_subset_1(C_933, k1_zfmisc_1(A_932)) | v1_xboole_0(C_933) | v1_xboole_0(A_932))), inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_6170])).
% 11.86/4.25  tff(c_7028, plain, (![A_932]: (k2_partfun1(k4_subset_1(A_932, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_932, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_932, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_932, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_932, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_932)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_932)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_932))), inference(resolution, [status(thm)], [c_64, c_7021])).
% 11.86/4.25  tff(c_7038, plain, (![A_932]: (k2_partfun1(k4_subset_1(A_932, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_932, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_932, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_932, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_932, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_932)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_932)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_932))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_2668, c_7028])).
% 11.86/4.25  tff(c_7204, plain, (![A_954]: (k2_partfun1(k4_subset_1(A_954, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_954, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_954, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_954, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_954, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_954)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_954)) | v1_xboole_0(A_954))), inference(negUnitSimplification, [status(thm)], [c_78, c_7038])).
% 11.86/4.25  tff(c_150, plain, (![C_244, A_245, B_246]: (v4_relat_1(C_244, A_245) | ~m1_subset_1(C_244, k1_zfmisc_1(k2_zfmisc_1(A_245, B_246))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.86/4.25  tff(c_157, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_150])).
% 11.86/4.25  tff(c_18, plain, (![B_18, A_17]: (k7_relat_1(B_18, A_17)=B_18 | ~v4_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.86/4.25  tff(c_161, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_157, c_18])).
% 11.86/4.25  tff(c_164, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_107, c_161])).
% 11.86/4.25  tff(c_304, plain, (![C_268, A_269, B_270]: (k7_relat_1(k7_relat_1(C_268, A_269), B_270)=k1_xboole_0 | ~r1_xboole_0(A_269, B_270) | ~v1_relat_1(C_268))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.86/4.25  tff(c_325, plain, (![B_270]: (k7_relat_1('#skF_6', B_270)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_270) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_164, c_304])).
% 11.86/4.25  tff(c_1138, plain, (![B_334]: (k7_relat_1('#skF_6', B_334)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_334))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_325])).
% 11.86/4.25  tff(c_1150, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_1138])).
% 11.86/4.25  tff(c_158, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_64, c_150])).
% 11.86/4.25  tff(c_167, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_158, c_18])).
% 11.86/4.25  tff(c_170, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_167])).
% 11.86/4.25  tff(c_322, plain, (![B_270]: (k7_relat_1('#skF_5', B_270)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_270) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_170, c_304])).
% 11.86/4.25  tff(c_1107, plain, (![B_333]: (k7_relat_1('#skF_5', B_333)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_333))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_322])).
% 11.86/4.25  tff(c_1119, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_1107])).
% 11.86/4.25  tff(c_291, plain, (![B_266, A_267]: (k1_relat_1(B_266)=A_267 | ~v1_partfun1(B_266, A_267) | ~v4_relat_1(B_266, A_267) | ~v1_relat_1(B_266))), inference(cnfTransformation, [status(thm)], [f_118])).
% 11.86/4.25  tff(c_297, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_157, c_291])).
% 11.86/4.25  tff(c_303, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_297])).
% 11.86/4.25  tff(c_858, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_303])).
% 11.86/4.25  tff(c_1083, plain, (![C_330, A_331, B_332]: (v1_partfun1(C_330, A_331) | ~v1_funct_2(C_330, A_331, B_332) | ~v1_funct_1(C_330) | ~m1_subset_1(C_330, k1_zfmisc_1(k2_zfmisc_1(A_331, B_332))) | v1_xboole_0(B_332))), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.86/4.25  tff(c_1086, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_1083])).
% 11.86/4.25  tff(c_1092, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1086])).
% 11.86/4.25  tff(c_1094, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_858, c_1092])).
% 11.86/4.25  tff(c_1095, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_303])).
% 11.86/4.25  tff(c_230, plain, (![B_257, A_258]: (r1_subset_1(B_257, A_258) | ~r1_subset_1(A_258, B_257) | v1_xboole_0(B_257) | v1_xboole_0(A_258))), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.86/4.25  tff(c_232, plain, (r1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_70, c_230])).
% 11.86/4.25  tff(c_235, plain, (r1_subset_1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_78, c_74, c_232])).
% 11.86/4.25  tff(c_1142, plain, (![B_20]: (k7_relat_1('#skF_6', B_20)=k1_xboole_0 | ~r1_subset_1('#skF_4', B_20) | v1_xboole_0(B_20) | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_22, c_1138])).
% 11.86/4.25  tff(c_1206, plain, (![B_339]: (k7_relat_1('#skF_6', B_339)=k1_xboole_0 | ~r1_subset_1('#skF_4', B_339) | v1_xboole_0(B_339))), inference(negUnitSimplification, [status(thm)], [c_74, c_1142])).
% 11.86/4.25  tff(c_1209, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_235, c_1206])).
% 11.86/4.25  tff(c_1212, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_78, c_1209])).
% 11.86/4.25  tff(c_1169, plain, (![A_335, C_336, B_337]: (k3_xboole_0(A_335, k10_relat_1(C_336, B_337))=k10_relat_1(k7_relat_1(C_336, A_335), B_337) | ~v1_relat_1(C_336))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.86/4.25  tff(c_1364, plain, (![A_354, A_355]: (k10_relat_1(k7_relat_1(A_354, A_355), k2_relat_1(A_354))=k3_xboole_0(A_355, k1_relat_1(A_354)) | ~v1_relat_1(A_354) | ~v1_relat_1(A_354))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1169])).
% 11.86/4.25  tff(c_1385, plain, (k3_xboole_0('#skF_3', k1_relat_1('#skF_6'))=k10_relat_1(k1_xboole_0, k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1212, c_1364])).
% 11.86/4.25  tff(c_1414, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_107, c_107, c_1095, c_14, c_1385])).
% 11.86/4.25  tff(c_1266, plain, (![A_342, B_343, C_344, D_345]: (k2_partfun1(A_342, B_343, C_344, D_345)=k7_relat_1(C_344, D_345) | ~m1_subset_1(C_344, k1_zfmisc_1(k2_zfmisc_1(A_342, B_343))) | ~v1_funct_1(C_344))), inference(cnfTransformation, [status(thm)], [f_124])).
% 11.86/4.25  tff(c_1270, plain, (![D_345]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_345)=k7_relat_1('#skF_5', D_345) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_64, c_1266])).
% 11.86/4.25  tff(c_1276, plain, (![D_345]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_345)=k7_relat_1('#skF_5', D_345))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1270])).
% 11.86/4.25  tff(c_1268, plain, (![D_345]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_345)=k7_relat_1('#skF_6', D_345) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_58, c_1266])).
% 11.86/4.25  tff(c_1273, plain, (![D_345]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_345)=k7_relat_1('#skF_6', D_345))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1268])).
% 11.86/4.25  tff(c_241, plain, (![A_259, B_260, C_261]: (k9_subset_1(A_259, B_260, C_261)=k3_xboole_0(B_260, C_261) | ~m1_subset_1(C_261, k1_zfmisc_1(A_259)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.86/4.25  tff(c_252, plain, (![B_260]: (k9_subset_1('#skF_1', B_260, '#skF_4')=k3_xboole_0(B_260, '#skF_4'))), inference(resolution, [status(thm)], [c_72, c_241])).
% 11.86/4.25  tff(c_56, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_248])).
% 11.86/4.25  tff(c_109, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_56])).
% 11.86/4.25  tff(c_254, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_252, c_252, c_109])).
% 11.86/4.25  tff(c_1295, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1273, c_254])).
% 11.86/4.25  tff(c_1348, plain, (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1276, c_1295])).
% 11.86/4.25  tff(c_1437, plain, (k7_relat_1('#skF_5', k1_xboole_0)!=k7_relat_1('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1414, c_1414, c_1348])).
% 11.86/4.25  tff(c_1440, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1150, c_1119, c_1437])).
% 11.86/4.25  tff(c_1441, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_56])).
% 11.86/4.25  tff(c_1521, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_1441])).
% 11.86/4.25  tff(c_7215, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_7204, c_1521])).
% 11.86/4.25  tff(c_7229, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_2532, c_2923, c_2563, c_2923, c_1590, c_1590, c_3203, c_7215])).
% 11.86/4.25  tff(c_7231, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_7229])).
% 11.86/4.25  tff(c_7232, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_1441])).
% 11.86/4.25  tff(c_13081, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_13072, c_7232])).
% 11.86/4.25  tff(c_13092, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_8619, c_9010, c_8675, c_9010, c_8525, c_8525, c_9265, c_13081])).
% 11.86/4.25  tff(c_13094, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_13092])).
% 11.86/4.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.86/4.25  
% 11.86/4.25  Inference rules
% 11.86/4.25  ----------------------
% 11.86/4.25  #Ref     : 0
% 11.86/4.25  #Sup     : 3055
% 11.86/4.25  #Fact    : 0
% 11.86/4.25  #Define  : 0
% 11.86/4.25  #Split   : 46
% 11.86/4.25  #Chain   : 0
% 11.86/4.25  #Close   : 0
% 11.86/4.25  
% 11.86/4.25  Ordering : KBO
% 11.86/4.25  
% 11.86/4.25  Simplification rules
% 11.86/4.25  ----------------------
% 11.86/4.25  #Subsume      : 1004
% 11.86/4.25  #Demod        : 3932
% 11.86/4.25  #Tautology    : 1010
% 11.86/4.25  #SimpNegUnit  : 284
% 11.86/4.25  #BackRed      : 30
% 11.86/4.25  
% 11.86/4.25  #Partial instantiations: 0
% 11.86/4.25  #Strategies tried      : 1
% 11.86/4.25  
% 11.86/4.25  Timing (in seconds)
% 11.86/4.25  ----------------------
% 11.86/4.25  Preprocessing        : 0.45
% 11.86/4.25  Parsing              : 0.21
% 11.86/4.25  CNF conversion       : 0.06
% 11.86/4.25  Main loop            : 3.00
% 11.86/4.25  Inferencing          : 0.94
% 11.86/4.25  Reduction            : 1.14
% 11.86/4.25  Demodulation         : 0.87
% 11.86/4.25  BG Simplification    : 0.10
% 11.86/4.25  Subsumption          : 0.64
% 11.86/4.25  Abstraction          : 0.14
% 11.86/4.25  MUC search           : 0.00
% 11.86/4.25  Cooper               : 0.00
% 11.86/4.25  Total                : 3.52
% 11.86/4.25  Index Insertion      : 0.00
% 11.86/4.25  Index Deletion       : 0.00
% 11.86/4.25  Index Matching       : 0.00
% 11.86/4.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
