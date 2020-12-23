%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:11 EST 2020

% Result     : Theorem 20.61s
% Output     : CNFRefutation 21.41s
% Verified   : 
% Statistics : Number of formulae       :  897 (12478 expanded)
%              Number of leaves         :   57 (4065 expanded)
%              Depth                    :   33
%              Number of atoms          : 2792 (49765 expanded)
%              Number of equality atoms :  727 (12316 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_271,negated_conjecture,(
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

tff(f_99,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_229,axiom,(
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

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_141,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_133,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_75,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_119,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_147,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_195,axiom,(
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

tff(c_100,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_94,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_90,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_96,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_88,plain,(
    r1_subset_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_92,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_40,plain,(
    ! [A_28,B_29] :
      ( r1_xboole_0(A_28,B_29)
      | ~ r1_subset_1(A_28,B_29)
      | v1_xboole_0(B_29)
      | v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_98,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_76,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_7636,plain,(
    ! [C_744,A_745,B_746] :
      ( v1_relat_1(C_744)
      | ~ m1_subset_1(C_744,k1_zfmisc_1(k2_zfmisc_1(A_745,B_746))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_7643,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_76,c_7636])).

tff(c_82,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_7644,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_7636])).

tff(c_86,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_84,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_80,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_78,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_70,plain,(
    ! [C_177,F_180,A_175,D_178,B_176,E_179] :
      ( v1_funct_2(k1_tmap_1(A_175,B_176,C_177,D_178,E_179,F_180),k4_subset_1(A_175,C_177,D_178),B_176)
      | ~ m1_subset_1(F_180,k1_zfmisc_1(k2_zfmisc_1(D_178,B_176)))
      | ~ v1_funct_2(F_180,D_178,B_176)
      | ~ v1_funct_1(F_180)
      | ~ m1_subset_1(E_179,k1_zfmisc_1(k2_zfmisc_1(C_177,B_176)))
      | ~ v1_funct_2(E_179,C_177,B_176)
      | ~ v1_funct_1(E_179)
      | ~ m1_subset_1(D_178,k1_zfmisc_1(A_175))
      | v1_xboole_0(D_178)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(A_175))
      | v1_xboole_0(C_177)
      | v1_xboole_0(B_176)
      | v1_xboole_0(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_8069,plain,(
    ! [C_796,A_797,B_798] :
      ( v4_relat_1(C_796,A_797)
      | ~ m1_subset_1(C_796,k1_zfmisc_1(k2_zfmisc_1(A_797,B_798))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_8076,plain,(
    v4_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_8069])).

tff(c_8510,plain,(
    ! [B_826,A_827] :
      ( k1_relat_1(B_826) = A_827
      | ~ v1_partfun1(B_826,A_827)
      | ~ v4_relat_1(B_826,A_827)
      | ~ v1_relat_1(B_826) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_8516,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_8076,c_8510])).

tff(c_8522,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7643,c_8516])).

tff(c_9547,plain,(
    ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_8522])).

tff(c_10032,plain,(
    ! [C_936,A_937,B_938] :
      ( v1_partfun1(C_936,A_937)
      | ~ v1_funct_2(C_936,A_937,B_938)
      | ~ v1_funct_1(C_936)
      | ~ m1_subset_1(C_936,k1_zfmisc_1(k2_zfmisc_1(A_937,B_938)))
      | v1_xboole_0(B_938) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_10035,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_10032])).

tff(c_10041,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_10035])).

tff(c_10043,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_9547,c_10041])).

tff(c_10044,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_8522])).

tff(c_20,plain,(
    ! [B_16,A_15] :
      ( r1_xboole_0(k1_relat_1(B_16),A_15)
      | k9_relat_1(B_16,A_15) != k1_xboole_0
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10059,plain,(
    ! [A_15] :
      ( r1_xboole_0('#skF_5',A_15)
      | k9_relat_1('#skF_7',A_15) != k1_xboole_0
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10044,c_20])).

tff(c_10096,plain,(
    ! [A_939] :
      ( r1_xboole_0('#skF_5',A_939)
      | k9_relat_1('#skF_7',A_939) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7643,c_10059])).

tff(c_32,plain,(
    ! [A_25] :
      ( k1_relat_1(A_25) != k1_xboole_0
      | k1_xboole_0 = A_25
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_7679,plain,
    ( k1_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_7644,c_32])).

tff(c_7683,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7679])).

tff(c_26,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_7684,plain,(
    ! [A_749] :
      ( k9_relat_1(A_749,k1_relat_1(A_749)) = k2_relat_1(A_749)
      | ~ v1_relat_1(A_749) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_7693,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_7684])).

tff(c_7696,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_7693])).

tff(c_7700,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_7696])).

tff(c_48,plain,(
    ! [A_36] :
      ( r1_xboole_0('#skF_1'(A_36),A_36)
      | k1_xboole_0 = A_36 ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_7719,plain,(
    ! [A_756,B_757] :
      ( k7_relat_1(A_756,B_757) = k1_xboole_0
      | ~ r1_xboole_0(B_757,k1_relat_1(A_756))
      | ~ v1_relat_1(A_756) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_8004,plain,(
    ! [A_791] :
      ( k7_relat_1(A_791,'#skF_1'(k1_relat_1(A_791))) = k1_xboole_0
      | ~ v1_relat_1(A_791)
      | k1_relat_1(A_791) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_48,c_7719])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k7_relat_1(A_12,B_13))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8013,plain,(
    ! [A_791] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_791)
      | ~ v1_relat_1(A_791)
      | k1_relat_1(A_791) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8004,c_14])).

tff(c_8028,plain,(
    ! [A_792] :
      ( ~ v1_relat_1(A_792)
      | ~ v1_relat_1(A_792)
      | k1_relat_1(A_792) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_7700,c_8013])).

tff(c_8030,plain,
    ( ~ v1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7644,c_8028])).

tff(c_8037,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7644,c_8030])).

tff(c_8039,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7683,c_8037])).

tff(c_8041,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_7696])).

tff(c_8078,plain,(
    ! [A_799,B_800] :
      ( k7_relat_1(A_799,B_800) = k1_xboole_0
      | ~ r1_xboole_0(B_800,k1_relat_1(A_799))
      | ~ v1_relat_1(A_799) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_8089,plain,(
    ! [B_800] :
      ( k7_relat_1(k1_xboole_0,B_800) = k1_xboole_0
      | ~ r1_xboole_0(B_800,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_8078])).

tff(c_8093,plain,(
    ! [B_800] :
      ( k7_relat_1(k1_xboole_0,B_800) = k1_xboole_0
      | ~ r1_xboole_0(B_800,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8041,c_8089])).

tff(c_10114,plain,
    ( k7_relat_1(k1_xboole_0,'#skF_5') = k1_xboole_0
    | k9_relat_1('#skF_7',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10096,c_8093])).

tff(c_11752,plain,(
    k9_relat_1('#skF_7',k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_10114])).

tff(c_8040,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_7696])).

tff(c_6,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8077,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_8069])).

tff(c_8513,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_8077,c_8510])).

tff(c_8519,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7644,c_8513])).

tff(c_8523,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_8519])).

tff(c_9489,plain,(
    ! [C_904,A_905,B_906] :
      ( v1_partfun1(C_904,A_905)
      | ~ v1_funct_2(C_904,A_905,B_906)
      | ~ v1_funct_1(C_904)
      | ~ m1_subset_1(C_904,k1_zfmisc_1(k2_zfmisc_1(A_905,B_906)))
      | v1_xboole_0(B_906) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_9495,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_9489])).

tff(c_9502,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_9495])).

tff(c_9504,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_8523,c_9502])).

tff(c_9505,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_8519])).

tff(c_34,plain,(
    ! [B_27,A_26] :
      ( k7_relat_1(B_27,A_26) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_27),A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_9523,plain,(
    ! [A_26] :
      ( k7_relat_1('#skF_6',A_26) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_26)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9505,c_34])).

tff(c_10413,plain,(
    ! [A_955] :
      ( k7_relat_1('#skF_6',A_955) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_955) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7644,c_9523])).

tff(c_10420,plain,(
    ! [B_29] :
      ( k7_relat_1('#skF_6',B_29) = k1_xboole_0
      | ~ r1_subset_1('#skF_4',B_29)
      | v1_xboole_0(B_29)
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_10413])).

tff(c_10559,plain,(
    ! [B_968] :
      ( k7_relat_1('#skF_6',B_968) = k1_xboole_0
      | ~ r1_subset_1('#skF_4',B_968)
      | v1_xboole_0(B_968) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_10420])).

tff(c_10562,plain,
    ( k7_relat_1('#skF_6','#skF_5') = k1_xboole_0
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_10559])).

tff(c_10565,plain,(
    k7_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_10562])).

tff(c_36,plain,(
    ! [B_27,A_26] :
      ( r1_xboole_0(k1_relat_1(B_27),A_26)
      | k7_relat_1(B_27,A_26) != k1_xboole_0
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_9511,plain,(
    ! [A_26] :
      ( r1_xboole_0('#skF_4',A_26)
      | k7_relat_1('#skF_6',A_26) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9505,c_36])).

tff(c_10430,plain,(
    ! [A_956] :
      ( r1_xboole_0('#skF_4',A_956)
      | k7_relat_1('#skF_6',A_956) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7644,c_9511])).

tff(c_18,plain,(
    ! [B_16,A_15] :
      ( k9_relat_1(B_16,A_15) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_16),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_9514,plain,(
    ! [A_15] :
      ( k9_relat_1('#skF_6',A_15) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_15)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9505,c_18])).

tff(c_9535,plain,(
    ! [A_15] :
      ( k9_relat_1('#skF_6',A_15) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7644,c_9514])).

tff(c_10460,plain,(
    ! [A_956] :
      ( k9_relat_1('#skF_6',A_956) = k1_xboole_0
      | k7_relat_1('#skF_6',A_956) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10430,c_9535])).

tff(c_9520,plain,(
    ! [A_15] :
      ( r1_xboole_0('#skF_4',A_15)
      | k9_relat_1('#skF_6',A_15) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9505,c_20])).

tff(c_9539,plain,(
    ! [A_15] :
      ( r1_xboole_0('#skF_4',A_15)
      | k9_relat_1('#skF_6',A_15) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7644,c_9520])).

tff(c_24,plain,(
    ! [A_22,B_24] :
      ( k7_relat_1(A_22,B_24) = k1_xboole_0
      | ~ r1_xboole_0(B_24,k1_relat_1(A_22))
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_10065,plain,(
    ! [B_24] :
      ( k7_relat_1('#skF_7',B_24) = k1_xboole_0
      | ~ r1_xboole_0(B_24,'#skF_5')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10044,c_24])).

tff(c_10196,plain,(
    ! [B_948] :
      ( k7_relat_1('#skF_7',B_948) = k1_xboole_0
      | ~ r1_xboole_0(B_948,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7643,c_10065])).

tff(c_10233,plain,
    ( k7_relat_1('#skF_7','#skF_4') = k1_xboole_0
    | k9_relat_1('#skF_6','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9539,c_10196])).

tff(c_10626,plain,(
    k9_relat_1('#skF_6','#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_10233])).

tff(c_10630,plain,(
    k7_relat_1('#skF_6','#skF_5') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10460,c_10626])).

tff(c_10634,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10565,c_10630])).

tff(c_10635,plain,(
    k7_relat_1('#skF_7','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_10233])).

tff(c_10050,plain,(
    ! [A_26] :
      ( r1_xboole_0('#skF_5',A_26)
      | k7_relat_1('#skF_7',A_26) != k1_xboole_0
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10044,c_36])).

tff(c_10378,plain,(
    ! [A_954] :
      ( r1_xboole_0('#skF_5',A_954)
      | k7_relat_1('#skF_7',A_954) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7643,c_10050])).

tff(c_10053,plain,(
    ! [A_15] :
      ( k9_relat_1('#skF_7',A_15) = k1_xboole_0
      | ~ r1_xboole_0('#skF_5',A_15)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10044,c_18])).

tff(c_10074,plain,(
    ! [A_15] :
      ( k9_relat_1('#skF_7',A_15) = k1_xboole_0
      | ~ r1_xboole_0('#skF_5',A_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7643,c_10053])).

tff(c_10744,plain,(
    ! [A_984] :
      ( k9_relat_1('#skF_7',A_984) = k1_xboole_0
      | k7_relat_1('#skF_7',A_984) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10378,c_10074])).

tff(c_10078,plain,(
    ! [A_15] :
      ( r1_xboole_0('#skF_5',A_15)
      | k9_relat_1('#skF_7',A_15) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7643,c_10059])).

tff(c_9526,plain,(
    ! [B_24] :
      ( k7_relat_1('#skF_6',B_24) = k1_xboole_0
      | ~ r1_xboole_0(B_24,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9505,c_24])).

tff(c_10256,plain,(
    ! [B_949] :
      ( k7_relat_1('#skF_6',B_949) = k1_xboole_0
      | ~ r1_xboole_0(B_949,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7644,c_9526])).

tff(c_10295,plain,
    ( k7_relat_1('#skF_6','#skF_5') = k1_xboole_0
    | k9_relat_1('#skF_7','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10078,c_10256])).

tff(c_10558,plain,(
    k9_relat_1('#skF_7','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_10295])).

tff(c_10750,plain,(
    k7_relat_1('#skF_7','#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10744,c_10558])).

tff(c_10778,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10635,c_10750])).

tff(c_10780,plain,(
    k9_relat_1('#skF_7','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_10295])).

tff(c_10062,plain,(
    ! [A_26] :
      ( k7_relat_1('#skF_7',A_26) = k1_xboole_0
      | ~ r1_xboole_0('#skF_5',A_26)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10044,c_34])).

tff(c_10478,plain,(
    ! [A_958] :
      ( k7_relat_1('#skF_7',A_958) = k1_xboole_0
      | ~ r1_xboole_0('#skF_5',A_958) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7643,c_10062])).

tff(c_10494,plain,(
    ! [A_15] :
      ( k7_relat_1('#skF_7',A_15) = k1_xboole_0
      | k9_relat_1('#skF_7',A_15) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10078,c_10478])).

tff(c_10804,plain,(
    k7_relat_1('#skF_7','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10780,c_10494])).

tff(c_22,plain,(
    ! [A_17,C_21,B_20] :
      ( k9_relat_1(k7_relat_1(A_17,C_21),B_20) = k9_relat_1(A_17,B_20)
      | ~ r1_tarski(B_20,C_21)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10810,plain,(
    ! [B_20] :
      ( k9_relat_1(k1_xboole_0,B_20) = k9_relat_1('#skF_7',B_20)
      | ~ r1_tarski(B_20,'#skF_4')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10804,c_22])).

tff(c_12061,plain,(
    ! [B_1074] :
      ( k9_relat_1(k1_xboole_0,B_1074) = k9_relat_1('#skF_7',B_1074)
      | ~ r1_tarski(B_1074,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7643,c_10810])).

tff(c_12065,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_12061])).

tff(c_12067,plain,(
    k9_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8040,c_12065])).

tff(c_12069,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11752,c_12067])).

tff(c_12071,plain,(
    k9_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_10114])).

tff(c_12130,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12071,c_10494])).

tff(c_8386,plain,(
    ! [B_821,A_822] :
      ( r1_xboole_0(k1_relat_1(B_821),A_822)
      | k7_relat_1(B_821,A_822) != k1_xboole_0
      | ~ v1_relat_1(B_821) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_8409,plain,(
    ! [A_822] :
      ( r1_xboole_0(k1_xboole_0,A_822)
      | k7_relat_1(k1_xboole_0,A_822) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_8386])).

tff(c_8418,plain,(
    ! [A_823] :
      ( r1_xboole_0(k1_xboole_0,A_823)
      | k7_relat_1(k1_xboole_0,A_823) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8041,c_8409])).

tff(c_8252,plain,(
    ! [B_812,A_813] :
      ( k9_relat_1(B_812,A_813) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_812),A_813)
      | ~ v1_relat_1(B_812) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8262,plain,(
    ! [A_813] :
      ( k9_relat_1(k1_xboole_0,A_813) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_813)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_8252])).

tff(c_8266,plain,(
    ! [A_813] :
      ( k9_relat_1(k1_xboole_0,A_813) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_813) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8041,c_8262])).

tff(c_8440,plain,(
    ! [A_823] :
      ( k9_relat_1(k1_xboole_0,A_823) = k1_xboole_0
      | k7_relat_1(k1_xboole_0,A_823) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8418,c_8266])).

tff(c_10466,plain,
    ( k7_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0
    | k7_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10430,c_8093])).

tff(c_11381,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_10466])).

tff(c_8137,plain,(
    ! [B_806,A_807] :
      ( r1_xboole_0(k1_relat_1(B_806),A_807)
      | k9_relat_1(B_806,A_807) != k1_xboole_0
      | ~ v1_relat_1(B_806) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8154,plain,(
    ! [A_807] :
      ( r1_xboole_0(k1_xboole_0,A_807)
      | k9_relat_1(k1_xboole_0,A_807) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_8137])).

tff(c_8160,plain,(
    ! [A_807] :
      ( r1_xboole_0(k1_xboole_0,A_807)
      | k9_relat_1(k1_xboole_0,A_807) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8041,c_8154])).

tff(c_10301,plain,
    ( k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0
    | k9_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8160,c_10256])).

tff(c_11416,plain,(
    k9_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_11381,c_10301])).

tff(c_11423,plain,(
    k7_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8440,c_11416])).

tff(c_10166,plain,(
    ! [A_946] :
      ( r1_xboole_0('#skF_4',A_946)
      | k9_relat_1('#skF_6',A_946) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7644,c_9520])).

tff(c_10184,plain,
    ( k7_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0
    | k9_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10166,c_8093])).

tff(c_11433,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_11423,c_10184])).

tff(c_10779,plain,(
    k7_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_10295])).

tff(c_10784,plain,(
    ! [B_20] :
      ( k9_relat_1(k1_xboole_0,B_20) = k9_relat_1('#skF_6',B_20)
      | ~ r1_tarski(B_20,'#skF_5')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10779,c_22])).

tff(c_11654,plain,(
    ! [B_1049] :
      ( k9_relat_1(k1_xboole_0,B_1049) = k9_relat_1('#skF_6',B_1049)
      | ~ r1_tarski(B_1049,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7644,c_10784])).

tff(c_11658,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_11654])).

tff(c_11660,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8040,c_11658])).

tff(c_11662,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11433,c_11660])).

tff(c_11664,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_10466])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_11344,plain,(
    ! [A_1027] :
      ( k3_xboole_0('#skF_4',A_1027) = k1_xboole_0
      | k7_relat_1('#skF_6',A_1027) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10430,c_2])).

tff(c_11359,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10779,c_11344])).

tff(c_10134,plain,(
    ! [A_941,B_942,C_943] :
      ( k9_subset_1(A_941,B_942,C_943) = k3_xboole_0(B_942,C_943)
      | ~ m1_subset_1(C_943,k1_zfmisc_1(A_941)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10146,plain,(
    ! [B_942] : k9_subset_1('#skF_2',B_942,'#skF_5') = k3_xboole_0(B_942,'#skF_5') ),
    inference(resolution,[status(thm)],[c_90,c_10134])).

tff(c_10929,plain,(
    ! [F_994,D_992,B_996,C_991,E_995,A_993] :
      ( v1_funct_1(k1_tmap_1(A_993,B_996,C_991,D_992,E_995,F_994))
      | ~ m1_subset_1(F_994,k1_zfmisc_1(k2_zfmisc_1(D_992,B_996)))
      | ~ v1_funct_2(F_994,D_992,B_996)
      | ~ v1_funct_1(F_994)
      | ~ m1_subset_1(E_995,k1_zfmisc_1(k2_zfmisc_1(C_991,B_996)))
      | ~ v1_funct_2(E_995,C_991,B_996)
      | ~ v1_funct_1(E_995)
      | ~ m1_subset_1(D_992,k1_zfmisc_1(A_993))
      | v1_xboole_0(D_992)
      | ~ m1_subset_1(C_991,k1_zfmisc_1(A_993))
      | v1_xboole_0(C_991)
      | v1_xboole_0(B_996)
      | v1_xboole_0(A_993) ) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_10931,plain,(
    ! [A_993,C_991,E_995] :
      ( v1_funct_1(k1_tmap_1(A_993,'#skF_3',C_991,'#skF_5',E_995,'#skF_7'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_995,k1_zfmisc_1(k2_zfmisc_1(C_991,'#skF_3')))
      | ~ v1_funct_2(E_995,C_991,'#skF_3')
      | ~ v1_funct_1(E_995)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_993))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_991,k1_zfmisc_1(A_993))
      | v1_xboole_0(C_991)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_993) ) ),
    inference(resolution,[status(thm)],[c_76,c_10929])).

tff(c_10936,plain,(
    ! [A_993,C_991,E_995] :
      ( v1_funct_1(k1_tmap_1(A_993,'#skF_3',C_991,'#skF_5',E_995,'#skF_7'))
      | ~ m1_subset_1(E_995,k1_zfmisc_1(k2_zfmisc_1(C_991,'#skF_3')))
      | ~ v1_funct_2(E_995,C_991,'#skF_3')
      | ~ v1_funct_1(E_995)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_993))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_991,k1_zfmisc_1(A_993))
      | v1_xboole_0(C_991)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_993) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_10931])).

tff(c_12490,plain,(
    ! [A_1096,C_1097,E_1098] :
      ( v1_funct_1(k1_tmap_1(A_1096,'#skF_3',C_1097,'#skF_5',E_1098,'#skF_7'))
      | ~ m1_subset_1(E_1098,k1_zfmisc_1(k2_zfmisc_1(C_1097,'#skF_3')))
      | ~ v1_funct_2(E_1098,C_1097,'#skF_3')
      | ~ v1_funct_1(E_1098)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1096))
      | ~ m1_subset_1(C_1097,k1_zfmisc_1(A_1096))
      | v1_xboole_0(C_1097)
      | v1_xboole_0(A_1096) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_92,c_10936])).

tff(c_12497,plain,(
    ! [A_1096] :
      ( v1_funct_1(k1_tmap_1(A_1096,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1096))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1096))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1096) ) ),
    inference(resolution,[status(thm)],[c_82,c_12490])).

tff(c_12507,plain,(
    ! [A_1096] :
      ( v1_funct_1(k1_tmap_1(A_1096,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1096))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1096))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1096) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_12497])).

tff(c_13082,plain,(
    ! [A_1121] :
      ( v1_funct_1(k1_tmap_1(A_1121,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1121))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1121))
      | v1_xboole_0(A_1121) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_12507])).

tff(c_13085,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_90,c_13082])).

tff(c_13088,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_13085])).

tff(c_13089,plain,(
    v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_13088])).

tff(c_10529,plain,(
    ! [A_962,B_963,C_964,D_965] :
      ( k2_partfun1(A_962,B_963,C_964,D_965) = k7_relat_1(C_964,D_965)
      | ~ m1_subset_1(C_964,k1_zfmisc_1(k2_zfmisc_1(A_962,B_963)))
      | ~ v1_funct_1(C_964) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_10533,plain,(
    ! [D_965] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_6',D_965) = k7_relat_1('#skF_6',D_965)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_82,c_10529])).

tff(c_10539,plain,(
    ! [D_965] : k2_partfun1('#skF_4','#skF_3','#skF_6',D_965) = k7_relat_1('#skF_6',D_965) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_10533])).

tff(c_10531,plain,(
    ! [D_965] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_7',D_965) = k7_relat_1('#skF_7',D_965)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_76,c_10529])).

tff(c_10536,plain,(
    ! [D_965] : k2_partfun1('#skF_5','#skF_3','#skF_7',D_965) = k7_relat_1('#skF_7',D_965) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_10531])).

tff(c_68,plain,(
    ! [C_177,F_180,A_175,D_178,B_176,E_179] :
      ( m1_subset_1(k1_tmap_1(A_175,B_176,C_177,D_178,E_179,F_180),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_175,C_177,D_178),B_176)))
      | ~ m1_subset_1(F_180,k1_zfmisc_1(k2_zfmisc_1(D_178,B_176)))
      | ~ v1_funct_2(F_180,D_178,B_176)
      | ~ v1_funct_1(F_180)
      | ~ m1_subset_1(E_179,k1_zfmisc_1(k2_zfmisc_1(C_177,B_176)))
      | ~ v1_funct_2(E_179,C_177,B_176)
      | ~ v1_funct_1(E_179)
      | ~ m1_subset_1(D_178,k1_zfmisc_1(A_175))
      | v1_xboole_0(D_178)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(A_175))
      | v1_xboole_0(C_177)
      | v1_xboole_0(B_176)
      | v1_xboole_0(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_11340,plain,(
    ! [D_1024,F_1025,B_1026,C_1023,A_1022,E_1021] :
      ( k2_partfun1(k4_subset_1(A_1022,C_1023,D_1024),B_1026,k1_tmap_1(A_1022,B_1026,C_1023,D_1024,E_1021,F_1025),D_1024) = F_1025
      | ~ m1_subset_1(k1_tmap_1(A_1022,B_1026,C_1023,D_1024,E_1021,F_1025),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1022,C_1023,D_1024),B_1026)))
      | ~ v1_funct_2(k1_tmap_1(A_1022,B_1026,C_1023,D_1024,E_1021,F_1025),k4_subset_1(A_1022,C_1023,D_1024),B_1026)
      | ~ v1_funct_1(k1_tmap_1(A_1022,B_1026,C_1023,D_1024,E_1021,F_1025))
      | k2_partfun1(D_1024,B_1026,F_1025,k9_subset_1(A_1022,C_1023,D_1024)) != k2_partfun1(C_1023,B_1026,E_1021,k9_subset_1(A_1022,C_1023,D_1024))
      | ~ m1_subset_1(F_1025,k1_zfmisc_1(k2_zfmisc_1(D_1024,B_1026)))
      | ~ v1_funct_2(F_1025,D_1024,B_1026)
      | ~ v1_funct_1(F_1025)
      | ~ m1_subset_1(E_1021,k1_zfmisc_1(k2_zfmisc_1(C_1023,B_1026)))
      | ~ v1_funct_2(E_1021,C_1023,B_1026)
      | ~ v1_funct_1(E_1021)
      | ~ m1_subset_1(D_1024,k1_zfmisc_1(A_1022))
      | v1_xboole_0(D_1024)
      | ~ m1_subset_1(C_1023,k1_zfmisc_1(A_1022))
      | v1_xboole_0(C_1023)
      | v1_xboole_0(B_1026)
      | v1_xboole_0(A_1022) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_21002,plain,(
    ! [D_1349,F_1351,E_1352,A_1350,C_1348,B_1353] :
      ( k2_partfun1(k4_subset_1(A_1350,C_1348,D_1349),B_1353,k1_tmap_1(A_1350,B_1353,C_1348,D_1349,E_1352,F_1351),D_1349) = F_1351
      | ~ v1_funct_2(k1_tmap_1(A_1350,B_1353,C_1348,D_1349,E_1352,F_1351),k4_subset_1(A_1350,C_1348,D_1349),B_1353)
      | ~ v1_funct_1(k1_tmap_1(A_1350,B_1353,C_1348,D_1349,E_1352,F_1351))
      | k2_partfun1(D_1349,B_1353,F_1351,k9_subset_1(A_1350,C_1348,D_1349)) != k2_partfun1(C_1348,B_1353,E_1352,k9_subset_1(A_1350,C_1348,D_1349))
      | ~ m1_subset_1(F_1351,k1_zfmisc_1(k2_zfmisc_1(D_1349,B_1353)))
      | ~ v1_funct_2(F_1351,D_1349,B_1353)
      | ~ v1_funct_1(F_1351)
      | ~ m1_subset_1(E_1352,k1_zfmisc_1(k2_zfmisc_1(C_1348,B_1353)))
      | ~ v1_funct_2(E_1352,C_1348,B_1353)
      | ~ v1_funct_1(E_1352)
      | ~ m1_subset_1(D_1349,k1_zfmisc_1(A_1350))
      | v1_xboole_0(D_1349)
      | ~ m1_subset_1(C_1348,k1_zfmisc_1(A_1350))
      | v1_xboole_0(C_1348)
      | v1_xboole_0(B_1353)
      | v1_xboole_0(A_1350) ) ),
    inference(resolution,[status(thm)],[c_68,c_11340])).

tff(c_25044,plain,(
    ! [F_1474,A_1473,C_1471,E_1475,D_1472,B_1476] :
      ( k2_partfun1(k4_subset_1(A_1473,C_1471,D_1472),B_1476,k1_tmap_1(A_1473,B_1476,C_1471,D_1472,E_1475,F_1474),D_1472) = F_1474
      | ~ v1_funct_1(k1_tmap_1(A_1473,B_1476,C_1471,D_1472,E_1475,F_1474))
      | k2_partfun1(D_1472,B_1476,F_1474,k9_subset_1(A_1473,C_1471,D_1472)) != k2_partfun1(C_1471,B_1476,E_1475,k9_subset_1(A_1473,C_1471,D_1472))
      | ~ m1_subset_1(F_1474,k1_zfmisc_1(k2_zfmisc_1(D_1472,B_1476)))
      | ~ v1_funct_2(F_1474,D_1472,B_1476)
      | ~ v1_funct_1(F_1474)
      | ~ m1_subset_1(E_1475,k1_zfmisc_1(k2_zfmisc_1(C_1471,B_1476)))
      | ~ v1_funct_2(E_1475,C_1471,B_1476)
      | ~ v1_funct_1(E_1475)
      | ~ m1_subset_1(D_1472,k1_zfmisc_1(A_1473))
      | v1_xboole_0(D_1472)
      | ~ m1_subset_1(C_1471,k1_zfmisc_1(A_1473))
      | v1_xboole_0(C_1471)
      | v1_xboole_0(B_1476)
      | v1_xboole_0(A_1473) ) ),
    inference(resolution,[status(thm)],[c_70,c_21002])).

tff(c_25048,plain,(
    ! [A_1473,C_1471,E_1475] :
      ( k2_partfun1(k4_subset_1(A_1473,C_1471,'#skF_5'),'#skF_3',k1_tmap_1(A_1473,'#skF_3',C_1471,'#skF_5',E_1475,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1473,'#skF_3',C_1471,'#skF_5',E_1475,'#skF_7'))
      | k2_partfun1(C_1471,'#skF_3',E_1475,k9_subset_1(A_1473,C_1471,'#skF_5')) != k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1(A_1473,C_1471,'#skF_5'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_1475,k1_zfmisc_1(k2_zfmisc_1(C_1471,'#skF_3')))
      | ~ v1_funct_2(E_1475,C_1471,'#skF_3')
      | ~ v1_funct_1(E_1475)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1473))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1471,k1_zfmisc_1(A_1473))
      | v1_xboole_0(C_1471)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1473) ) ),
    inference(resolution,[status(thm)],[c_76,c_25044])).

tff(c_25054,plain,(
    ! [A_1473,C_1471,E_1475] :
      ( k2_partfun1(k4_subset_1(A_1473,C_1471,'#skF_5'),'#skF_3',k1_tmap_1(A_1473,'#skF_3',C_1471,'#skF_5',E_1475,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1473,'#skF_3',C_1471,'#skF_5',E_1475,'#skF_7'))
      | k2_partfun1(C_1471,'#skF_3',E_1475,k9_subset_1(A_1473,C_1471,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_1473,C_1471,'#skF_5'))
      | ~ m1_subset_1(E_1475,k1_zfmisc_1(k2_zfmisc_1(C_1471,'#skF_3')))
      | ~ v1_funct_2(E_1475,C_1471,'#skF_3')
      | ~ v1_funct_1(E_1475)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1473))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1471,k1_zfmisc_1(A_1473))
      | v1_xboole_0(C_1471)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1473) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_10536,c_25048])).

tff(c_30151,plain,(
    ! [A_1583,C_1584,E_1585] :
      ( k2_partfun1(k4_subset_1(A_1583,C_1584,'#skF_5'),'#skF_3',k1_tmap_1(A_1583,'#skF_3',C_1584,'#skF_5',E_1585,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1583,'#skF_3',C_1584,'#skF_5',E_1585,'#skF_7'))
      | k2_partfun1(C_1584,'#skF_3',E_1585,k9_subset_1(A_1583,C_1584,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_1583,C_1584,'#skF_5'))
      | ~ m1_subset_1(E_1585,k1_zfmisc_1(k2_zfmisc_1(C_1584,'#skF_3')))
      | ~ v1_funct_2(E_1585,C_1584,'#skF_3')
      | ~ v1_funct_1(E_1585)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1583))
      | ~ m1_subset_1(C_1584,k1_zfmisc_1(A_1583))
      | v1_xboole_0(C_1584)
      | v1_xboole_0(A_1583) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_92,c_25054])).

tff(c_30158,plain,(
    ! [A_1583] :
      ( k2_partfun1(k4_subset_1(A_1583,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_1583,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1583,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1(A_1583,'#skF_4','#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_1583,'#skF_4','#skF_5'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1583))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1583))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1583) ) ),
    inference(resolution,[status(thm)],[c_82,c_30151])).

tff(c_30168,plain,(
    ! [A_1583] :
      ( k2_partfun1(k4_subset_1(A_1583,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_1583,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1583,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_1583,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_1583,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1583))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1583))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1583) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_10539,c_30158])).

tff(c_30865,plain,(
    ! [A_1601] :
      ( k2_partfun1(k4_subset_1(A_1601,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_1601,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1601,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_1601,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_1601,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1601))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1601))
      | v1_xboole_0(A_1601) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_30168])).

tff(c_188,plain,(
    ! [C_255,A_256,B_257] :
      ( v1_relat_1(C_255)
      | ~ m1_subset_1(C_255,k1_zfmisc_1(k2_zfmisc_1(A_256,B_257))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_196,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_188])).

tff(c_212,plain,
    ( k1_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_196,c_32])).

tff(c_215,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_212])).

tff(c_174,plain,(
    ! [A_254] :
      ( k9_relat_1(A_254,k1_relat_1(A_254)) = k2_relat_1(A_254)
      | ~ v1_relat_1(A_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_183,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_174])).

tff(c_186,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_183])).

tff(c_187,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_269,plain,(
    ! [A_270,B_271] :
      ( k7_relat_1(A_270,B_271) = k1_xboole_0
      | ~ r1_xboole_0(B_271,k1_relat_1(A_270))
      | ~ v1_relat_1(A_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_518,plain,(
    ! [A_305] :
      ( k7_relat_1(A_305,'#skF_1'(k1_relat_1(A_305))) = k1_xboole_0
      | ~ v1_relat_1(A_305)
      | k1_relat_1(A_305) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_48,c_269])).

tff(c_530,plain,(
    ! [A_305] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_305)
      | ~ v1_relat_1(A_305)
      | k1_relat_1(A_305) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_518,c_14])).

tff(c_554,plain,(
    ! [A_310] :
      ( ~ v1_relat_1(A_310)
      | ~ v1_relat_1(A_310)
      | k1_relat_1(A_310) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_530])).

tff(c_556,plain,
    ( ~ v1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_196,c_554])).

tff(c_563,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_556])).

tff(c_565,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_215,c_563])).

tff(c_566,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_212])).

tff(c_570,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_566,c_187])).

tff(c_583,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_570])).

tff(c_585,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_668,plain,(
    ! [B_323,A_324] :
      ( r1_xboole_0(k1_relat_1(B_323),A_324)
      | k7_relat_1(B_323,A_324) != k1_xboole_0
      | ~ v1_relat_1(B_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_677,plain,(
    ! [A_324] :
      ( r1_xboole_0(k1_xboole_0,A_324)
      | k7_relat_1(k1_xboole_0,A_324) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_668])).

tff(c_681,plain,(
    ! [A_324] :
      ( r1_xboole_0(k1_xboole_0,A_324)
      | k7_relat_1(k1_xboole_0,A_324) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_585,c_677])).

tff(c_961,plain,(
    ! [B_343,A_344] :
      ( k9_relat_1(B_343,A_344) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_343),A_344)
      | ~ v1_relat_1(B_343) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_978,plain,(
    ! [A_344] :
      ( k9_relat_1(k1_xboole_0,A_344) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_344)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_961])).

tff(c_998,plain,(
    ! [A_348] :
      ( k9_relat_1(k1_xboole_0,A_348) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_348) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_585,c_978])).

tff(c_1015,plain,(
    ! [A_324] :
      ( k9_relat_1(k1_xboole_0,A_324) = k1_xboole_0
      | k7_relat_1(k1_xboole_0,A_324) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_681,c_998])).

tff(c_790,plain,(
    ! [B_334,A_335] :
      ( r1_xboole_0(k1_relat_1(B_334),A_335)
      | k9_relat_1(B_334,A_335) != k1_xboole_0
      | ~ v1_relat_1(B_334) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_807,plain,(
    ! [A_335] :
      ( r1_xboole_0(k1_xboole_0,A_335)
      | k9_relat_1(k1_xboole_0,A_335) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_790])).

tff(c_813,plain,(
    ! [A_335] :
      ( r1_xboole_0(k1_xboole_0,A_335)
      | k9_relat_1(k1_xboole_0,A_335) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_585,c_807])).

tff(c_600,plain,(
    ! [C_311,A_312,B_313] :
      ( v1_relat_1(C_311)
      | ~ m1_subset_1(C_311,k1_zfmisc_1(k2_zfmisc_1(A_312,B_313))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_608,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_600])).

tff(c_630,plain,(
    ! [C_314,A_315,B_316] :
      ( v4_relat_1(C_314,A_315)
      | ~ m1_subset_1(C_314,k1_zfmisc_1(k2_zfmisc_1(A_315,B_316))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_638,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_630])).

tff(c_1126,plain,(
    ! [B_353,A_354] :
      ( k1_relat_1(B_353) = A_354
      | ~ v1_partfun1(B_353,A_354)
      | ~ v4_relat_1(B_353,A_354)
      | ~ v1_relat_1(B_353) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1129,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_638,c_1126])).

tff(c_1135,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_1129])).

tff(c_1139,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1135])).

tff(c_1812,plain,(
    ! [C_407,A_408,B_409] :
      ( v1_partfun1(C_407,A_408)
      | ~ v1_funct_2(C_407,A_408,B_409)
      | ~ v1_funct_1(C_407)
      | ~ m1_subset_1(C_407,k1_zfmisc_1(k2_zfmisc_1(A_408,B_409)))
      | v1_xboole_0(B_409) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1818,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_1812])).

tff(c_1825,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_1818])).

tff(c_1827,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_1139,c_1825])).

tff(c_1828,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1135])).

tff(c_1840,plain,(
    ! [B_24] :
      ( k7_relat_1('#skF_6',B_24) = k1_xboole_0
      | ~ r1_xboole_0(B_24,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1828,c_24])).

tff(c_2492,plain,(
    ! [B_445] :
      ( k7_relat_1('#skF_6',B_445) = k1_xboole_0
      | ~ r1_xboole_0(B_445,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_1840])).

tff(c_2537,plain,
    ( k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0
    | k9_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_813,c_2492])).

tff(c_4500,plain,(
    k9_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2537])).

tff(c_4508,plain,(
    k7_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1015,c_4500])).

tff(c_1837,plain,(
    ! [A_15] :
      ( r1_xboole_0('#skF_4',A_15)
      | k9_relat_1('#skF_6',A_15) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1828,c_20])).

tff(c_2418,plain,(
    ! [A_441] :
      ( r1_xboole_0('#skF_4',A_441)
      | k9_relat_1('#skF_6',A_441) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_1837])).

tff(c_732,plain,(
    ! [A_331,B_332] :
      ( k7_relat_1(A_331,B_332) = k1_xboole_0
      | ~ r1_xboole_0(B_332,k1_relat_1(A_331))
      | ~ v1_relat_1(A_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_755,plain,(
    ! [B_332] :
      ( k7_relat_1(k1_xboole_0,B_332) = k1_xboole_0
      | ~ r1_xboole_0(B_332,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_732])).

tff(c_762,plain,(
    ! [B_332] :
      ( k7_relat_1(k1_xboole_0,B_332) = k1_xboole_0
      | ~ r1_xboole_0(B_332,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_585,c_755])).

tff(c_2441,plain,
    ( k7_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0
    | k9_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2418,c_762])).

tff(c_4980,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_4508,c_2441])).

tff(c_584,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_607,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_76,c_600])).

tff(c_637,plain,(
    v4_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_630])).

tff(c_1132,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_637,c_1126])).

tff(c_1138,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_607,c_1132])).

tff(c_1884,plain,(
    ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1138])).

tff(c_2201,plain,(
    ! [C_430,A_431,B_432] :
      ( v1_partfun1(C_430,A_431)
      | ~ v1_funct_2(C_430,A_431,B_432)
      | ~ v1_funct_1(C_430)
      | ~ m1_subset_1(C_430,k1_zfmisc_1(k2_zfmisc_1(A_431,B_432)))
      | v1_xboole_0(B_432) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2204,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_2201])).

tff(c_2210,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_2204])).

tff(c_2212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_1884,c_2210])).

tff(c_2213,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1138])).

tff(c_2225,plain,(
    ! [B_24] :
      ( k7_relat_1('#skF_7',B_24) = k1_xboole_0
      | ~ r1_xboole_0(B_24,'#skF_5')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2213,c_24])).

tff(c_2359,plain,(
    ! [B_440] :
      ( k7_relat_1('#skF_7',B_440) = k1_xboole_0
      | ~ r1_xboole_0(B_440,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_607,c_2225])).

tff(c_2375,plain,(
    ! [A_28] :
      ( k7_relat_1('#skF_7',A_28) = k1_xboole_0
      | ~ r1_subset_1(A_28,'#skF_5')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_28) ) ),
    inference(resolution,[status(thm)],[c_40,c_2359])).

tff(c_4283,plain,(
    ! [A_565] :
      ( k7_relat_1('#skF_7',A_565) = k1_xboole_0
      | ~ r1_subset_1(A_565,'#skF_5')
      | v1_xboole_0(A_565) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_2375])).

tff(c_4290,plain,
    ( k7_relat_1('#skF_7','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_88,c_4283])).

tff(c_4296,plain,(
    k7_relat_1('#skF_7','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_4290])).

tff(c_2231,plain,(
    ! [A_26] :
      ( r1_xboole_0('#skF_5',A_26)
      | k7_relat_1('#skF_7',A_26) != k1_xboole_0
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2213,c_36])).

tff(c_2269,plain,(
    ! [A_434] :
      ( r1_xboole_0('#skF_5',A_434)
      | k7_relat_1('#skF_7',A_434) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_607,c_2231])).

tff(c_4454,plain,(
    ! [A_573] :
      ( k3_xboole_0('#skF_5',A_573) = k1_xboole_0
      | k7_relat_1('#skF_7',A_573) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2269,c_2])).

tff(c_4468,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4296,c_4454])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2219,plain,(
    ! [A_15] :
      ( k9_relat_1('#skF_7',A_15) = k1_xboole_0
      | ~ r1_xboole_0('#skF_5',A_15)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2213,c_18])).

tff(c_2307,plain,(
    ! [A_436] :
      ( k9_relat_1('#skF_7',A_436) = k1_xboole_0
      | ~ r1_xboole_0('#skF_5',A_436) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_607,c_2219])).

tff(c_4716,plain,(
    ! [B_599] :
      ( k9_relat_1('#skF_7',B_599) = k1_xboole_0
      | k3_xboole_0('#skF_5',B_599) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_2307])).

tff(c_2222,plain,(
    ! [A_15] :
      ( r1_xboole_0('#skF_5',A_15)
      | k9_relat_1('#skF_7',A_15) != k1_xboole_0
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2213,c_20])).

tff(c_2594,plain,(
    ! [A_451] :
      ( r1_xboole_0('#skF_5',A_451)
      | k9_relat_1('#skF_7',A_451) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_607,c_2222])).

tff(c_1860,plain,(
    ! [B_24] :
      ( k7_relat_1('#skF_6',B_24) = k1_xboole_0
      | ~ r1_xboole_0(B_24,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_1840])).

tff(c_2623,plain,
    ( k7_relat_1('#skF_6','#skF_5') = k1_xboole_0
    | k9_relat_1('#skF_7','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2594,c_1860])).

tff(c_4666,plain,(
    k9_relat_1('#skF_7','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2623])).

tff(c_4722,plain,(
    k3_xboole_0('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4716,c_4666])).

tff(c_4750,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4468,c_4722])).

tff(c_4751,plain,(
    k7_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2623])).

tff(c_4759,plain,(
    ! [B_20] :
      ( k9_relat_1(k1_xboole_0,B_20) = k9_relat_1('#skF_6',B_20)
      | ~ r1_tarski(B_20,'#skF_5')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4751,c_22])).

tff(c_5276,plain,(
    ! [B_632] :
      ( k9_relat_1(k1_xboole_0,B_632) = k9_relat_1('#skF_6',B_632)
      | ~ r1_tarski(B_632,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_4759])).

tff(c_5280,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_5276])).

tff(c_5282,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_584,c_5280])).

tff(c_5284,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4980,c_5282])).

tff(c_5285,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2537])).

tff(c_1834,plain,(
    ! [A_15] :
      ( k9_relat_1('#skF_6',A_15) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_15)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1828,c_18])).

tff(c_2562,plain,(
    ! [A_446] :
      ( k9_relat_1('#skF_6',A_446) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_446) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_1834])).

tff(c_2572,plain,(
    ! [B_29] :
      ( k9_relat_1('#skF_6',B_29) = k1_xboole_0
      | ~ r1_subset_1('#skF_4',B_29)
      | v1_xboole_0(B_29)
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_2562])).

tff(c_5732,plain,(
    ! [B_665] :
      ( k9_relat_1('#skF_6',B_665) = k1_xboole_0
      | ~ r1_subset_1('#skF_4',B_665)
      | v1_xboole_0(B_665) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_2572])).

tff(c_5735,plain,
    ( k9_relat_1('#skF_6','#skF_5') = k1_xboole_0
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_5732])).

tff(c_5738,plain,(
    k9_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_5735])).

tff(c_2443,plain,(
    ! [A_441] :
      ( k3_xboole_0('#skF_4',A_441) = k1_xboole_0
      | k9_relat_1('#skF_6',A_441) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2418,c_2])).

tff(c_5754,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5738,c_2443])).

tff(c_2287,plain,
    ( k7_relat_1(k1_xboole_0,'#skF_5') = k1_xboole_0
    | k7_relat_1('#skF_7',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2269,c_762])).

tff(c_2657,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2287])).

tff(c_2393,plain,
    ( k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0
    | k9_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_813,c_2359])).

tff(c_2704,plain,(
    k9_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_2657,c_2393])).

tff(c_2712,plain,(
    k7_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1015,c_2704])).

tff(c_2631,plain,
    ( k7_relat_1(k1_xboole_0,'#skF_5') = k1_xboole_0
    | k9_relat_1('#skF_7',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2594,c_762])).

tff(c_3860,plain,(
    k9_relat_1('#skF_7',k1_xboole_0) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_2712,c_2631])).

tff(c_2245,plain,(
    ! [B_24] :
      ( k7_relat_1('#skF_7',B_24) = k1_xboole_0
      | ~ r1_xboole_0(B_24,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_607,c_2225])).

tff(c_2437,plain,
    ( k7_relat_1('#skF_7','#skF_4') = k1_xboole_0
    | k9_relat_1('#skF_6','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2418,c_2245])).

tff(c_2817,plain,(
    k9_relat_1('#skF_6','#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2437])).

tff(c_2818,plain,(
    ! [B_469] :
      ( k9_relat_1('#skF_6',B_469) = k1_xboole_0
      | ~ r1_subset_1('#skF_4',B_469)
      | v1_xboole_0(B_469) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_2572])).

tff(c_2821,plain,
    ( k9_relat_1('#skF_6','#skF_5') = k1_xboole_0
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_2818])).

tff(c_2824,plain,(
    k9_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_2821])).

tff(c_2825,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2817,c_2824])).

tff(c_2826,plain,(
    k7_relat_1('#skF_7','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2437])).

tff(c_2834,plain,(
    ! [B_20] :
      ( k9_relat_1(k1_xboole_0,B_20) = k9_relat_1('#skF_7',B_20)
      | ~ r1_tarski(B_20,'#skF_4')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2826,c_22])).

tff(c_4272,plain,(
    ! [B_564] :
      ( k9_relat_1(k1_xboole_0,B_564) = k9_relat_1('#skF_7',B_564)
      | ~ r1_tarski(B_564,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_607,c_2834])).

tff(c_4276,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_4272])).

tff(c_4278,plain,(
    k9_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_584,c_4276])).

tff(c_4280,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3860,c_4278])).

tff(c_4282,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2287])).

tff(c_2583,plain,(
    ! [A_447,B_448,C_449,D_450] :
      ( k2_partfun1(A_447,B_448,C_449,D_450) = k7_relat_1(C_449,D_450)
      | ~ m1_subset_1(C_449,k1_zfmisc_1(k2_zfmisc_1(A_447,B_448)))
      | ~ v1_funct_1(C_449) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_2585,plain,(
    ! [D_450] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_7',D_450) = k7_relat_1('#skF_7',D_450)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_76,c_2583])).

tff(c_2590,plain,(
    ! [D_450] : k2_partfun1('#skF_5','#skF_3','#skF_7',D_450) = k7_relat_1('#skF_7',D_450) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2585])).

tff(c_2587,plain,(
    ! [D_450] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_6',D_450) = k7_relat_1('#skF_6',D_450)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_82,c_2583])).

tff(c_2593,plain,(
    ! [D_450] : k2_partfun1('#skF_4','#skF_3','#skF_6',D_450) = k7_relat_1('#skF_6',D_450) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_2587])).

tff(c_985,plain,(
    ! [A_345,B_346,C_347] :
      ( k9_subset_1(A_345,B_346,C_347) = k3_xboole_0(B_346,C_347)
      | ~ m1_subset_1(C_347,k1_zfmisc_1(A_345)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_997,plain,(
    ! [B_346] : k9_subset_1('#skF_2',B_346,'#skF_5') = k3_xboole_0(B_346,'#skF_5') ),
    inference(resolution,[status(thm)],[c_90,c_985])).

tff(c_74,plain,
    ( k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') != '#skF_7'
    | k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') != '#skF_6'
    | k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_113,plain,(
    k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_1026,plain,(
    k2_partfun1('#skF_5','#skF_3','#skF_7',k3_xboole_0('#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3','#skF_6',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_997,c_997,c_113])).

tff(c_7590,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5285,c_5754,c_4282,c_5754,c_2590,c_2593,c_1026])).

tff(c_7591,plain,
    ( k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_7699,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_7591])).

tff(c_30876,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_30865,c_7699])).

tff(c_30890,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_90,c_12130,c_11664,c_11359,c_10146,c_11359,c_10146,c_13089,c_30876])).

tff(c_30892,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_30890])).

tff(c_30893,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_7591])).

tff(c_31560,plain,(
    ! [C_1672,A_1673,B_1674] :
      ( v4_relat_1(C_1672,A_1673)
      | ~ m1_subset_1(C_1672,k1_zfmisc_1(k2_zfmisc_1(A_1673,B_1674))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_31568,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_31560])).

tff(c_32055,plain,(
    ! [B_1706,A_1707] :
      ( k1_relat_1(B_1706) = A_1707
      | ~ v1_partfun1(B_1706,A_1707)
      | ~ v4_relat_1(B_1706,A_1707)
      | ~ v1_relat_1(B_1706) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_32058,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_31568,c_32055])).

tff(c_32064,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7644,c_32058])).

tff(c_32068,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_32064])).

tff(c_32971,plain,(
    ! [C_1774,A_1775,B_1776] :
      ( v1_partfun1(C_1774,A_1775)
      | ~ v1_funct_2(C_1774,A_1775,B_1776)
      | ~ v1_funct_1(C_1774)
      | ~ m1_subset_1(C_1774,k1_zfmisc_1(k2_zfmisc_1(A_1775,B_1776)))
      | v1_xboole_0(B_1776) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_32977,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_32971])).

tff(c_32984,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_32977])).

tff(c_32986,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_32068,c_32984])).

tff(c_32987,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_32064])).

tff(c_33000,plain,(
    ! [B_24] :
      ( k7_relat_1('#skF_6',B_24) = k1_xboole_0
      | ~ r1_xboole_0(B_24,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32987,c_24])).

tff(c_33873,plain,(
    ! [B_1826] :
      ( k7_relat_1('#skF_6',B_1826) = k1_xboole_0
      | ~ r1_xboole_0(B_1826,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7644,c_33000])).

tff(c_33925,plain,(
    ! [A_1] :
      ( k7_relat_1('#skF_6',A_1) = k1_xboole_0
      | k3_xboole_0(A_1,'#skF_4') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_33873])).

tff(c_32997,plain,(
    ! [A_26] :
      ( r1_xboole_0('#skF_4',A_26)
      | k7_relat_1('#skF_6',A_26) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32987,c_36])).

tff(c_33727,plain,(
    ! [A_1818] :
      ( r1_xboole_0('#skF_4',A_1818)
      | k7_relat_1('#skF_6',A_1818) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7644,c_32997])).

tff(c_30895,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_7696])).

tff(c_30905,plain,(
    ! [C_1605,A_1606,B_1607] :
      ( v4_relat_1(C_1605,A_1606)
      | ~ m1_subset_1(C_1605,k1_zfmisc_1(k2_zfmisc_1(A_1606,B_1607))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_30912,plain,(
    v4_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_30905])).

tff(c_31094,plain,(
    ! [B_1627,A_1628] :
      ( k1_relat_1(B_1627) = A_1628
      | ~ v1_partfun1(B_1627,A_1628)
      | ~ v4_relat_1(B_1627,A_1628)
      | ~ v1_relat_1(B_1627) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_31100,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_30912,c_31094])).

tff(c_31106,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7643,c_31100])).

tff(c_31108,plain,(
    ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_31106])).

tff(c_31295,plain,(
    ! [C_1655,A_1656,B_1657] :
      ( v1_partfun1(C_1655,A_1656)
      | ~ v1_funct_2(C_1655,A_1656,B_1657)
      | ~ v1_funct_1(C_1655)
      | ~ m1_subset_1(C_1655,k1_zfmisc_1(k2_zfmisc_1(A_1656,B_1657)))
      | v1_xboole_0(B_1657) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_31298,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_31295])).

tff(c_31304,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_31298])).

tff(c_31306,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_31108,c_31304])).

tff(c_31307,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_31106])).

tff(c_7652,plain,
    ( k1_relat_1('#skF_7') != k1_xboole_0
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_7643,c_32])).

tff(c_7680,plain,(
    k1_relat_1('#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7652])).

tff(c_31310,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31307,c_7680])).

tff(c_31326,plain,(
    ! [B_24] :
      ( k7_relat_1('#skF_7',B_24) = k1_xboole_0
      | ~ r1_xboole_0(B_24,'#skF_5')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31307,c_24])).

tff(c_31478,plain,(
    ! [B_1668] :
      ( k7_relat_1('#skF_7',B_1668) = k1_xboole_0
      | ~ r1_xboole_0(B_1668,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7643,c_31326])).

tff(c_31506,plain,
    ( k7_relat_1('#skF_7','#skF_1'('#skF_5')) = k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_48,c_31478])).

tff(c_31520,plain,(
    k7_relat_1('#skF_7','#skF_1'('#skF_5')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_31310,c_31506])).

tff(c_31524,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_31520,c_14])).

tff(c_31528,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7643,c_31524])).

tff(c_31530,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30895,c_31528])).

tff(c_31532,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_7696])).

tff(c_31669,plain,(
    ! [A_1684,B_1685] :
      ( k7_relat_1(A_1684,B_1685) = k1_xboole_0
      | ~ r1_xboole_0(B_1685,k1_relat_1(A_1684))
      | ~ v1_relat_1(A_1684) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_31688,plain,(
    ! [B_1685] :
      ( k7_relat_1(k1_xboole_0,B_1685) = k1_xboole_0
      | ~ r1_xboole_0(B_1685,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_31669])).

tff(c_31694,plain,(
    ! [B_1685] :
      ( k7_relat_1(k1_xboole_0,B_1685) = k1_xboole_0
      | ~ r1_xboole_0(B_1685,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31532,c_31688])).

tff(c_33749,plain,
    ( k7_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0
    | k7_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_33727,c_31694])).

tff(c_34831,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_33749])).

tff(c_34838,plain,(
    k3_xboole_0(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_33925,c_34831])).

tff(c_33003,plain,(
    ! [A_15] :
      ( r1_xboole_0('#skF_4',A_15)
      | k9_relat_1('#skF_6',A_15) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32987,c_20])).

tff(c_33943,plain,(
    ! [A_1827] :
      ( r1_xboole_0('#skF_4',A_1827)
      | k9_relat_1('#skF_6',A_1827) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7644,c_33003])).

tff(c_33981,plain,
    ( k7_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0
    | k9_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_33943,c_31694])).

tff(c_34928,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_33981])).

tff(c_31531,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_7696])).

tff(c_33018,plain,(
    ! [A_26] :
      ( r1_xboole_0('#skF_4',A_26)
      | k7_relat_1('#skF_6',A_26) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7644,c_32997])).

tff(c_31567,plain,(
    v4_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_31560])).

tff(c_32061,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_31567,c_32055])).

tff(c_32067,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7643,c_32061])).

tff(c_33079,plain,(
    ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_32067])).

tff(c_33520,plain,(
    ! [C_1805,A_1806,B_1807] :
      ( v1_partfun1(C_1805,A_1806)
      | ~ v1_funct_2(C_1805,A_1806,B_1807)
      | ~ v1_funct_1(C_1805)
      | ~ m1_subset_1(C_1805,k1_zfmisc_1(k2_zfmisc_1(A_1806,B_1807)))
      | v1_xboole_0(B_1807) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_33523,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_33520])).

tff(c_33529,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_33523])).

tff(c_33531,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_33079,c_33529])).

tff(c_33532,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_32067])).

tff(c_33545,plain,(
    ! [B_24] :
      ( k7_relat_1('#skF_7',B_24) = k1_xboole_0
      | ~ r1_xboole_0(B_24,'#skF_5')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33532,c_24])).

tff(c_33769,plain,(
    ! [B_1820] :
      ( k7_relat_1('#skF_7',B_1820) = k1_xboole_0
      | ~ r1_xboole_0(B_1820,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7643,c_33545])).

tff(c_33810,plain,
    ( k7_relat_1('#skF_7','#skF_4') = k1_xboole_0
    | k7_relat_1('#skF_6','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_33018,c_33769])).

tff(c_34145,plain,(
    k7_relat_1('#skF_6','#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_33810])).

tff(c_33542,plain,(
    ! [A_26] :
      ( r1_xboole_0('#skF_5',A_26)
      | k7_relat_1('#skF_7',A_26) != k1_xboole_0
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33532,c_36])).

tff(c_33563,plain,(
    ! [A_26] :
      ( r1_xboole_0('#skF_5',A_26)
      | k7_relat_1('#skF_7',A_26) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7643,c_33542])).

tff(c_33916,plain,
    ( k7_relat_1('#skF_6','#skF_5') = k1_xboole_0
    | k7_relat_1('#skF_7','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_33563,c_33873])).

tff(c_34397,plain,(
    k7_relat_1('#skF_7','#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_34145,c_33916])).

tff(c_33785,plain,(
    ! [A_28] :
      ( k7_relat_1('#skF_7',A_28) = k1_xboole_0
      | ~ r1_subset_1(A_28,'#skF_5')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_28) ) ),
    inference(resolution,[status(thm)],[c_40,c_33769])).

tff(c_34471,plain,(
    ! [A_1867] :
      ( k7_relat_1('#skF_7',A_1867) = k1_xboole_0
      | ~ r1_subset_1(A_1867,'#skF_5')
      | v1_xboole_0(A_1867) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_33785])).

tff(c_34486,plain,
    ( k7_relat_1('#skF_7','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_88,c_34471])).

tff(c_34496,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_34397,c_34486])).

tff(c_34498,plain,(
    k7_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_33810])).

tff(c_34531,plain,(
    ! [B_20] :
      ( k9_relat_1(k1_xboole_0,B_20) = k9_relat_1('#skF_6',B_20)
      | ~ r1_tarski(B_20,'#skF_5')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34498,c_22])).

tff(c_35105,plain,(
    ! [B_1917] :
      ( k9_relat_1(k1_xboole_0,B_1917) = k9_relat_1('#skF_6',B_1917)
      | ~ r1_tarski(B_1917,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7644,c_34531])).

tff(c_35109,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_35105])).

tff(c_35111,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_31531,c_35109])).

tff(c_35113,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34928,c_35111])).

tff(c_35114,plain,(
    k7_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_33981])).

tff(c_31771,plain,(
    ! [B_1690,A_1691] :
      ( r1_xboole_0(k1_relat_1(B_1690),A_1691)
      | k7_relat_1(B_1690,A_1691) != k1_xboole_0
      | ~ v1_relat_1(B_1690) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_31791,plain,(
    ! [A_1691] :
      ( r1_xboole_0(k1_xboole_0,A_1691)
      | k7_relat_1(k1_xboole_0,A_1691) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_31771])).

tff(c_31799,plain,(
    ! [A_1692] :
      ( r1_xboole_0(k1_xboole_0,A_1692)
      | k7_relat_1(k1_xboole_0,A_1692) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31532,c_31791])).

tff(c_31823,plain,(
    ! [A_1692] :
      ( k3_xboole_0(k1_xboole_0,A_1692) = k1_xboole_0
      | k7_relat_1(k1_xboole_0,A_1692) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_31799,c_2])).

tff(c_35125,plain,(
    k3_xboole_0(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_35114,c_31823])).

tff(c_35146,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34838,c_35125])).

tff(c_35148,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_33749])).

tff(c_34719,plain,(
    ! [A_1880] :
      ( k3_xboole_0('#skF_4',A_1880) = k1_xboole_0
      | k7_relat_1('#skF_6',A_1880) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_33727,c_2])).

tff(c_34733,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_34498,c_34719])).

tff(c_33066,plain,(
    ! [A_1778,B_1779,C_1780] :
      ( k9_subset_1(A_1778,B_1779,C_1780) = k3_xboole_0(B_1779,C_1780)
      | ~ m1_subset_1(C_1780,k1_zfmisc_1(A_1778)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_33078,plain,(
    ! [B_1779] : k9_subset_1('#skF_2',B_1779,'#skF_5') = k3_xboole_0(B_1779,'#skF_5') ),
    inference(resolution,[status(thm)],[c_90,c_33066])).

tff(c_31798,plain,(
    ! [A_1691] :
      ( r1_xboole_0(k1_xboole_0,A_1691)
      | k7_relat_1(k1_xboole_0,A_1691) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31532,c_31791])).

tff(c_33819,plain,
    ( k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0
    | k7_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_31798,c_33769])).

tff(c_35261,plain,(
    k7_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_33819])).

tff(c_33548,plain,(
    ! [A_15] :
      ( r1_xboole_0('#skF_5',A_15)
      | k9_relat_1('#skF_7',A_15) != k1_xboole_0
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33532,c_20])).

tff(c_33607,plain,(
    ! [A_1810] :
      ( r1_xboole_0('#skF_5',A_1810)
      | k9_relat_1('#skF_7',A_1810) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7643,c_33548])).

tff(c_33625,plain,
    ( k7_relat_1(k1_xboole_0,'#skF_5') = k1_xboole_0
    | k9_relat_1('#skF_7',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_33607,c_31694])).

tff(c_35315,plain,(
    k9_relat_1('#skF_7',k1_xboole_0) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_35261,c_33625])).

tff(c_34497,plain,(
    k7_relat_1('#skF_7','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_33810])).

tff(c_34508,plain,(
    ! [B_20] :
      ( k9_relat_1(k1_xboole_0,B_20) = k9_relat_1('#skF_7',B_20)
      | ~ r1_tarski(B_20,'#skF_4')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34497,c_22])).

tff(c_35476,plain,(
    ! [B_1945] :
      ( k9_relat_1(k1_xboole_0,B_1945) = k9_relat_1('#skF_7',B_1945)
      | ~ r1_tarski(B_1945,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7643,c_34508])).

tff(c_35480,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_35476])).

tff(c_35482,plain,(
    k9_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_31531,c_35480])).

tff(c_35484,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35315,c_35482])).

tff(c_35485,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_33819])).

tff(c_33862,plain,(
    ! [A_1822,B_1823,C_1824,D_1825] :
      ( k2_partfun1(A_1822,B_1823,C_1824,D_1825) = k7_relat_1(C_1824,D_1825)
      | ~ m1_subset_1(C_1824,k1_zfmisc_1(k2_zfmisc_1(A_1822,B_1823)))
      | ~ v1_funct_1(C_1824) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_33866,plain,(
    ! [D_1825] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_6',D_1825) = k7_relat_1('#skF_6',D_1825)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_82,c_33862])).

tff(c_33872,plain,(
    ! [D_1825] : k2_partfun1('#skF_4','#skF_3','#skF_6',D_1825) = k7_relat_1('#skF_6',D_1825) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_33866])).

tff(c_33864,plain,(
    ! [D_1825] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_7',D_1825) = k7_relat_1('#skF_7',D_1825)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_76,c_33862])).

tff(c_33869,plain,(
    ! [D_1825] : k2_partfun1('#skF_5','#skF_3','#skF_7',D_1825) = k7_relat_1('#skF_7',D_1825) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_33864])).

tff(c_34568,plain,(
    ! [D_1870,A_1871,B_1874,E_1873,F_1872,C_1869] :
      ( v1_funct_1(k1_tmap_1(A_1871,B_1874,C_1869,D_1870,E_1873,F_1872))
      | ~ m1_subset_1(F_1872,k1_zfmisc_1(k2_zfmisc_1(D_1870,B_1874)))
      | ~ v1_funct_2(F_1872,D_1870,B_1874)
      | ~ v1_funct_1(F_1872)
      | ~ m1_subset_1(E_1873,k1_zfmisc_1(k2_zfmisc_1(C_1869,B_1874)))
      | ~ v1_funct_2(E_1873,C_1869,B_1874)
      | ~ v1_funct_1(E_1873)
      | ~ m1_subset_1(D_1870,k1_zfmisc_1(A_1871))
      | v1_xboole_0(D_1870)
      | ~ m1_subset_1(C_1869,k1_zfmisc_1(A_1871))
      | v1_xboole_0(C_1869)
      | v1_xboole_0(B_1874)
      | v1_xboole_0(A_1871) ) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_34570,plain,(
    ! [A_1871,C_1869,E_1873] :
      ( v1_funct_1(k1_tmap_1(A_1871,'#skF_3',C_1869,'#skF_5',E_1873,'#skF_7'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_1873,k1_zfmisc_1(k2_zfmisc_1(C_1869,'#skF_3')))
      | ~ v1_funct_2(E_1873,C_1869,'#skF_3')
      | ~ v1_funct_1(E_1873)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1871))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1869,k1_zfmisc_1(A_1871))
      | v1_xboole_0(C_1869)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1871) ) ),
    inference(resolution,[status(thm)],[c_76,c_34568])).

tff(c_34575,plain,(
    ! [A_1871,C_1869,E_1873] :
      ( v1_funct_1(k1_tmap_1(A_1871,'#skF_3',C_1869,'#skF_5',E_1873,'#skF_7'))
      | ~ m1_subset_1(E_1873,k1_zfmisc_1(k2_zfmisc_1(C_1869,'#skF_3')))
      | ~ v1_funct_2(E_1873,C_1869,'#skF_3')
      | ~ v1_funct_1(E_1873)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1871))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1869,k1_zfmisc_1(A_1871))
      | v1_xboole_0(C_1869)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1871) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_34570])).

tff(c_35812,plain,(
    ! [A_1974,C_1975,E_1976] :
      ( v1_funct_1(k1_tmap_1(A_1974,'#skF_3',C_1975,'#skF_5',E_1976,'#skF_7'))
      | ~ m1_subset_1(E_1976,k1_zfmisc_1(k2_zfmisc_1(C_1975,'#skF_3')))
      | ~ v1_funct_2(E_1976,C_1975,'#skF_3')
      | ~ v1_funct_1(E_1976)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1974))
      | ~ m1_subset_1(C_1975,k1_zfmisc_1(A_1974))
      | v1_xboole_0(C_1975)
      | v1_xboole_0(A_1974) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_92,c_34575])).

tff(c_35819,plain,(
    ! [A_1974] :
      ( v1_funct_1(k1_tmap_1(A_1974,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1974))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1974))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1974) ) ),
    inference(resolution,[status(thm)],[c_82,c_35812])).

tff(c_35829,plain,(
    ! [A_1974] :
      ( v1_funct_1(k1_tmap_1(A_1974,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1974))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1974))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1974) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_35819])).

tff(c_36525,plain,(
    ! [A_2004] :
      ( v1_funct_1(k1_tmap_1(A_2004,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2004))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2004))
      | v1_xboole_0(A_2004) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_35829])).

tff(c_36528,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_90,c_36525])).

tff(c_36531,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_36528])).

tff(c_36532,plain,(
    v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_36531])).

tff(c_35563,plain,(
    ! [B_1951,C_1948,D_1949,A_1947,E_1946,F_1950] :
      ( k2_partfun1(k4_subset_1(A_1947,C_1948,D_1949),B_1951,k1_tmap_1(A_1947,B_1951,C_1948,D_1949,E_1946,F_1950),C_1948) = E_1946
      | ~ m1_subset_1(k1_tmap_1(A_1947,B_1951,C_1948,D_1949,E_1946,F_1950),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1947,C_1948,D_1949),B_1951)))
      | ~ v1_funct_2(k1_tmap_1(A_1947,B_1951,C_1948,D_1949,E_1946,F_1950),k4_subset_1(A_1947,C_1948,D_1949),B_1951)
      | ~ v1_funct_1(k1_tmap_1(A_1947,B_1951,C_1948,D_1949,E_1946,F_1950))
      | k2_partfun1(D_1949,B_1951,F_1950,k9_subset_1(A_1947,C_1948,D_1949)) != k2_partfun1(C_1948,B_1951,E_1946,k9_subset_1(A_1947,C_1948,D_1949))
      | ~ m1_subset_1(F_1950,k1_zfmisc_1(k2_zfmisc_1(D_1949,B_1951)))
      | ~ v1_funct_2(F_1950,D_1949,B_1951)
      | ~ v1_funct_1(F_1950)
      | ~ m1_subset_1(E_1946,k1_zfmisc_1(k2_zfmisc_1(C_1948,B_1951)))
      | ~ v1_funct_2(E_1946,C_1948,B_1951)
      | ~ v1_funct_1(E_1946)
      | ~ m1_subset_1(D_1949,k1_zfmisc_1(A_1947))
      | v1_xboole_0(D_1949)
      | ~ m1_subset_1(C_1948,k1_zfmisc_1(A_1947))
      | v1_xboole_0(C_1948)
      | v1_xboole_0(B_1951)
      | v1_xboole_0(A_1947) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_44541,plain,(
    ! [C_2233,B_2238,A_2235,D_2234,E_2237,F_2236] :
      ( k2_partfun1(k4_subset_1(A_2235,C_2233,D_2234),B_2238,k1_tmap_1(A_2235,B_2238,C_2233,D_2234,E_2237,F_2236),C_2233) = E_2237
      | ~ v1_funct_2(k1_tmap_1(A_2235,B_2238,C_2233,D_2234,E_2237,F_2236),k4_subset_1(A_2235,C_2233,D_2234),B_2238)
      | ~ v1_funct_1(k1_tmap_1(A_2235,B_2238,C_2233,D_2234,E_2237,F_2236))
      | k2_partfun1(D_2234,B_2238,F_2236,k9_subset_1(A_2235,C_2233,D_2234)) != k2_partfun1(C_2233,B_2238,E_2237,k9_subset_1(A_2235,C_2233,D_2234))
      | ~ m1_subset_1(F_2236,k1_zfmisc_1(k2_zfmisc_1(D_2234,B_2238)))
      | ~ v1_funct_2(F_2236,D_2234,B_2238)
      | ~ v1_funct_1(F_2236)
      | ~ m1_subset_1(E_2237,k1_zfmisc_1(k2_zfmisc_1(C_2233,B_2238)))
      | ~ v1_funct_2(E_2237,C_2233,B_2238)
      | ~ v1_funct_1(E_2237)
      | ~ m1_subset_1(D_2234,k1_zfmisc_1(A_2235))
      | v1_xboole_0(D_2234)
      | ~ m1_subset_1(C_2233,k1_zfmisc_1(A_2235))
      | v1_xboole_0(C_2233)
      | v1_xboole_0(B_2238)
      | v1_xboole_0(A_2235) ) ),
    inference(resolution,[status(thm)],[c_68,c_35563])).

tff(c_47637,plain,(
    ! [F_2341,E_2342,D_2339,C_2338,A_2340,B_2343] :
      ( k2_partfun1(k4_subset_1(A_2340,C_2338,D_2339),B_2343,k1_tmap_1(A_2340,B_2343,C_2338,D_2339,E_2342,F_2341),C_2338) = E_2342
      | ~ v1_funct_1(k1_tmap_1(A_2340,B_2343,C_2338,D_2339,E_2342,F_2341))
      | k2_partfun1(D_2339,B_2343,F_2341,k9_subset_1(A_2340,C_2338,D_2339)) != k2_partfun1(C_2338,B_2343,E_2342,k9_subset_1(A_2340,C_2338,D_2339))
      | ~ m1_subset_1(F_2341,k1_zfmisc_1(k2_zfmisc_1(D_2339,B_2343)))
      | ~ v1_funct_2(F_2341,D_2339,B_2343)
      | ~ v1_funct_1(F_2341)
      | ~ m1_subset_1(E_2342,k1_zfmisc_1(k2_zfmisc_1(C_2338,B_2343)))
      | ~ v1_funct_2(E_2342,C_2338,B_2343)
      | ~ v1_funct_1(E_2342)
      | ~ m1_subset_1(D_2339,k1_zfmisc_1(A_2340))
      | v1_xboole_0(D_2339)
      | ~ m1_subset_1(C_2338,k1_zfmisc_1(A_2340))
      | v1_xboole_0(C_2338)
      | v1_xboole_0(B_2343)
      | v1_xboole_0(A_2340) ) ),
    inference(resolution,[status(thm)],[c_70,c_44541])).

tff(c_47641,plain,(
    ! [A_2340,C_2338,E_2342] :
      ( k2_partfun1(k4_subset_1(A_2340,C_2338,'#skF_5'),'#skF_3',k1_tmap_1(A_2340,'#skF_3',C_2338,'#skF_5',E_2342,'#skF_7'),C_2338) = E_2342
      | ~ v1_funct_1(k1_tmap_1(A_2340,'#skF_3',C_2338,'#skF_5',E_2342,'#skF_7'))
      | k2_partfun1(C_2338,'#skF_3',E_2342,k9_subset_1(A_2340,C_2338,'#skF_5')) != k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1(A_2340,C_2338,'#skF_5'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_2342,k1_zfmisc_1(k2_zfmisc_1(C_2338,'#skF_3')))
      | ~ v1_funct_2(E_2342,C_2338,'#skF_3')
      | ~ v1_funct_1(E_2342)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2340))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_2338,k1_zfmisc_1(A_2340))
      | v1_xboole_0(C_2338)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2340) ) ),
    inference(resolution,[status(thm)],[c_76,c_47637])).

tff(c_47647,plain,(
    ! [A_2340,C_2338,E_2342] :
      ( k2_partfun1(k4_subset_1(A_2340,C_2338,'#skF_5'),'#skF_3',k1_tmap_1(A_2340,'#skF_3',C_2338,'#skF_5',E_2342,'#skF_7'),C_2338) = E_2342
      | ~ v1_funct_1(k1_tmap_1(A_2340,'#skF_3',C_2338,'#skF_5',E_2342,'#skF_7'))
      | k2_partfun1(C_2338,'#skF_3',E_2342,k9_subset_1(A_2340,C_2338,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_2340,C_2338,'#skF_5'))
      | ~ m1_subset_1(E_2342,k1_zfmisc_1(k2_zfmisc_1(C_2338,'#skF_3')))
      | ~ v1_funct_2(E_2342,C_2338,'#skF_3')
      | ~ v1_funct_1(E_2342)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2340))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_2338,k1_zfmisc_1(A_2340))
      | v1_xboole_0(C_2338)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2340) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_33869,c_47641])).

tff(c_47655,plain,(
    ! [A_2344,C_2345,E_2346] :
      ( k2_partfun1(k4_subset_1(A_2344,C_2345,'#skF_5'),'#skF_3',k1_tmap_1(A_2344,'#skF_3',C_2345,'#skF_5',E_2346,'#skF_7'),C_2345) = E_2346
      | ~ v1_funct_1(k1_tmap_1(A_2344,'#skF_3',C_2345,'#skF_5',E_2346,'#skF_7'))
      | k2_partfun1(C_2345,'#skF_3',E_2346,k9_subset_1(A_2344,C_2345,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_2344,C_2345,'#skF_5'))
      | ~ m1_subset_1(E_2346,k1_zfmisc_1(k2_zfmisc_1(C_2345,'#skF_3')))
      | ~ v1_funct_2(E_2346,C_2345,'#skF_3')
      | ~ v1_funct_1(E_2346)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2344))
      | ~ m1_subset_1(C_2345,k1_zfmisc_1(A_2344))
      | v1_xboole_0(C_2345)
      | v1_xboole_0(A_2344) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_92,c_47647])).

tff(c_47662,plain,(
    ! [A_2344] :
      ( k2_partfun1(k4_subset_1(A_2344,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_2344,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_2344,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1(A_2344,'#skF_4','#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_2344,'#skF_4','#skF_5'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2344))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2344))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_2344) ) ),
    inference(resolution,[status(thm)],[c_82,c_47655])).

tff(c_47672,plain,(
    ! [A_2344] :
      ( k2_partfun1(k4_subset_1(A_2344,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_2344,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_2344,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_2344,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_2344,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2344))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2344))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_2344) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_33872,c_47662])).

tff(c_49132,plain,(
    ! [A_2377] :
      ( k2_partfun1(k4_subset_1(A_2377,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_2377,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_2377,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_2377,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_2377,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2377))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2377))
      | v1_xboole_0(A_2377) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_47672])).

tff(c_30894,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_7591])).

tff(c_35754,plain,(
    ! [D_1969,C_1968,B_1971,G_1970,A_1967] :
      ( k1_tmap_1(A_1967,B_1971,C_1968,D_1969,k2_partfun1(k4_subset_1(A_1967,C_1968,D_1969),B_1971,G_1970,C_1968),k2_partfun1(k4_subset_1(A_1967,C_1968,D_1969),B_1971,G_1970,D_1969)) = G_1970
      | ~ m1_subset_1(G_1970,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1967,C_1968,D_1969),B_1971)))
      | ~ v1_funct_2(G_1970,k4_subset_1(A_1967,C_1968,D_1969),B_1971)
      | ~ v1_funct_1(G_1970)
      | k2_partfun1(D_1969,B_1971,k2_partfun1(k4_subset_1(A_1967,C_1968,D_1969),B_1971,G_1970,D_1969),k9_subset_1(A_1967,C_1968,D_1969)) != k2_partfun1(C_1968,B_1971,k2_partfun1(k4_subset_1(A_1967,C_1968,D_1969),B_1971,G_1970,C_1968),k9_subset_1(A_1967,C_1968,D_1969))
      | ~ m1_subset_1(k2_partfun1(k4_subset_1(A_1967,C_1968,D_1969),B_1971,G_1970,D_1969),k1_zfmisc_1(k2_zfmisc_1(D_1969,B_1971)))
      | ~ v1_funct_2(k2_partfun1(k4_subset_1(A_1967,C_1968,D_1969),B_1971,G_1970,D_1969),D_1969,B_1971)
      | ~ v1_funct_1(k2_partfun1(k4_subset_1(A_1967,C_1968,D_1969),B_1971,G_1970,D_1969))
      | ~ m1_subset_1(k2_partfun1(k4_subset_1(A_1967,C_1968,D_1969),B_1971,G_1970,C_1968),k1_zfmisc_1(k2_zfmisc_1(C_1968,B_1971)))
      | ~ v1_funct_2(k2_partfun1(k4_subset_1(A_1967,C_1968,D_1969),B_1971,G_1970,C_1968),C_1968,B_1971)
      | ~ v1_funct_1(k2_partfun1(k4_subset_1(A_1967,C_1968,D_1969),B_1971,G_1970,C_1968))
      | ~ m1_subset_1(D_1969,k1_zfmisc_1(A_1967))
      | v1_xboole_0(D_1969)
      | ~ m1_subset_1(C_1968,k1_zfmisc_1(A_1967))
      | v1_xboole_0(C_1968)
      | v1_xboole_0(B_1971)
      | v1_xboole_0(A_1967) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_35756,plain,
    ( k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5',k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5')) = k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3')))
    | ~ v1_funct_2(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3')
    | ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | k2_partfun1('#skF_5','#skF_3',k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5'),k9_subset_1('#skF_2','#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3',k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),k9_subset_1('#skF_2','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5'),'#skF_5','#skF_3')
    | ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5'))
    | ~ m1_subset_1(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_30894,c_35754])).

tff(c_35758,plain,
    ( k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5',k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),'#skF_7') = k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3')))
    | ~ v1_funct_2(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3')
    | ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | k2_partfun1('#skF_4','#skF_3',k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),k1_xboole_0) != k1_xboole_0
    | ~ m1_subset_1(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'))
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_90,c_80,c_30894,c_78,c_30894,c_76,c_35485,c_33869,c_30894,c_34733,c_33078,c_34733,c_33078,c_30894,c_35756])).

tff(c_35759,plain,
    ( k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5',k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),'#skF_7') = k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3')))
    | ~ v1_funct_2(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3')
    | ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | k2_partfun1('#skF_4','#skF_3',k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),k1_xboole_0) != k1_xboole_0
    | ~ m1_subset_1(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_98,c_96,c_92,c_35758])).

tff(c_38471,plain,
    ( k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5',k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),'#skF_7') = k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3')))
    | ~ v1_funct_2(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3')
    | k2_partfun1('#skF_4','#skF_3',k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),k1_xboole_0) != k1_xboole_0
    | ~ m1_subset_1(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36532,c_35759])).

tff(c_38472,plain,(
    ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_38471])).

tff(c_49141,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_49132,c_38472])).

tff(c_49154,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_90,c_35485,c_35148,c_34733,c_33078,c_34733,c_33078,c_36532,c_86,c_49141])).

tff(c_49156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_49154])).

tff(c_49157,plain,
    ( ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | k2_partfun1('#skF_4','#skF_3',k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),k1_xboole_0) != k1_xboole_0
    | ~ v1_funct_2(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3')
    | ~ m1_subset_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3')))
    | k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5',k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4'),'#skF_7') = k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_38471])).

tff(c_49516,plain,(
    ~ m1_subset_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_49157])).

tff(c_49519,plain,
    ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_49516])).

tff(c_49522,plain,
    ( v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_90,c_86,c_84,c_82,c_80,c_78,c_76,c_49519])).

tff(c_49524,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_98,c_96,c_92,c_49522])).

tff(c_49526,plain,(
    m1_subset_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_49157])).

tff(c_66,plain,(
    ! [C_144,A_48,D_160,E_168,F_172,B_112] :
      ( k2_partfun1(k4_subset_1(A_48,C_144,D_160),B_112,k1_tmap_1(A_48,B_112,C_144,D_160,E_168,F_172),C_144) = E_168
      | ~ m1_subset_1(k1_tmap_1(A_48,B_112,C_144,D_160,E_168,F_172),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_48,C_144,D_160),B_112)))
      | ~ v1_funct_2(k1_tmap_1(A_48,B_112,C_144,D_160,E_168,F_172),k4_subset_1(A_48,C_144,D_160),B_112)
      | ~ v1_funct_1(k1_tmap_1(A_48,B_112,C_144,D_160,E_168,F_172))
      | k2_partfun1(D_160,B_112,F_172,k9_subset_1(A_48,C_144,D_160)) != k2_partfun1(C_144,B_112,E_168,k9_subset_1(A_48,C_144,D_160))
      | ~ m1_subset_1(F_172,k1_zfmisc_1(k2_zfmisc_1(D_160,B_112)))
      | ~ v1_funct_2(F_172,D_160,B_112)
      | ~ v1_funct_1(F_172)
      | ~ m1_subset_1(E_168,k1_zfmisc_1(k2_zfmisc_1(C_144,B_112)))
      | ~ v1_funct_2(E_168,C_144,B_112)
      | ~ v1_funct_1(E_168)
      | ~ m1_subset_1(D_160,k1_zfmisc_1(A_48))
      | v1_xboole_0(D_160)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(A_48))
      | v1_xboole_0(C_144)
      | v1_xboole_0(B_112)
      | v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_49534,plain,
    ( k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
    | ~ v1_funct_2(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3')
    | ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_49526,c_66])).

tff(c_49568,plain,
    ( k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
    | ~ v1_funct_2(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3')
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_90,c_86,c_84,c_82,c_80,c_78,c_76,c_35148,c_34733,c_33078,c_35485,c_34733,c_33078,c_33872,c_33869,c_36532,c_49534])).

tff(c_49569,plain,(
    ~ v1_funct_2(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_98,c_96,c_92,c_30893,c_49568])).

tff(c_49605,plain,
    ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_49569])).

tff(c_49608,plain,
    ( v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_90,c_86,c_84,c_82,c_80,c_78,c_76,c_49605])).

tff(c_49610,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_98,c_96,c_92,c_49608])).

tff(c_49611,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_7679])).

tff(c_49612,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_7679])).

tff(c_49629,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_49611,c_49612])).

tff(c_61924,plain,(
    ! [C_3113,A_3114,B_3115] :
      ( v4_relat_1(C_3113,A_3114)
      | ~ m1_subset_1(C_3113,k1_zfmisc_1(k2_zfmisc_1(A_3114,B_3115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_61932,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_61924])).

tff(c_64925,plain,(
    ! [B_3315,A_3316] :
      ( k1_relat_1(B_3315) = A_3316
      | ~ v1_partfun1(B_3315,A_3316)
      | ~ v4_relat_1(B_3315,A_3316)
      | ~ v1_relat_1(B_3315) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_64931,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_61932,c_64925])).

tff(c_64940,plain,
    ( '#skF_6' = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7644,c_49629,c_64931])).

tff(c_64944,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_64940])).

tff(c_65991,plain,(
    ! [C_3384,A_3385,B_3386] :
      ( v1_partfun1(C_3384,A_3385)
      | ~ v1_funct_2(C_3384,A_3385,B_3386)
      | ~ v1_funct_1(C_3384)
      | ~ m1_subset_1(C_3384,k1_zfmisc_1(k2_zfmisc_1(A_3385,B_3386)))
      | v1_xboole_0(B_3386) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_65997,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_65991])).

tff(c_66004,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_65997])).

tff(c_66006,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_64944,c_66004])).

tff(c_66007,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_64940])).

tff(c_49624,plain,(
    ! [A_3] : r1_tarski('#skF_6',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49611,c_6])).

tff(c_66046,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66007,c_49624])).

tff(c_49623,plain,(
    k2_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_49611,c_49611,c_26])).

tff(c_49641,plain,(
    ! [A_2395] :
      ( k9_relat_1(A_2395,k1_relat_1(A_2395)) = k2_relat_1(A_2395)
      | ~ v1_relat_1(A_2395) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_49650,plain,
    ( k9_relat_1('#skF_6','#skF_6') = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_49629,c_49641])).

tff(c_49654,plain,(
    k9_relat_1('#skF_6','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7644,c_49623,c_49650])).

tff(c_66043,plain,(
    k9_relat_1('#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66007,c_66007,c_66007,c_49654])).

tff(c_62028,plain,(
    ! [B_3124,A_3125] :
      ( k7_relat_1(B_3124,A_3125) = '#skF_6'
      | ~ r1_xboole_0(k1_relat_1(B_3124),A_3125)
      | ~ v1_relat_1(B_3124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49611,c_34])).

tff(c_62035,plain,(
    ! [A_3125] :
      ( k7_relat_1('#skF_6',A_3125) = '#skF_6'
      | ~ r1_xboole_0('#skF_6',A_3125)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49629,c_62028])).

tff(c_62038,plain,(
    ! [A_3125] :
      ( k7_relat_1('#skF_6',A_3125) = '#skF_6'
      | ~ r1_xboole_0('#skF_6',A_3125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7644,c_62035])).

tff(c_66535,plain,(
    ! [A_3437] :
      ( k7_relat_1('#skF_4',A_3437) = '#skF_4'
      | ~ r1_xboole_0('#skF_4',A_3437) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66007,c_66007,c_66007,c_62038])).

tff(c_66546,plain,(
    ! [B_29] :
      ( k7_relat_1('#skF_4',B_29) = '#skF_4'
      | ~ r1_subset_1('#skF_4',B_29)
      | v1_xboole_0(B_29)
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_66535])).

tff(c_66593,plain,(
    ! [B_3439] :
      ( k7_relat_1('#skF_4',B_3439) = '#skF_4'
      | ~ r1_subset_1('#skF_4',B_3439)
      | v1_xboole_0(B_3439) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_66546])).

tff(c_66596,plain,
    ( k7_relat_1('#skF_4','#skF_5') = '#skF_4'
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_66593])).

tff(c_66599,plain,(
    k7_relat_1('#skF_4','#skF_5') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_66596])).

tff(c_62074,plain,(
    ! [B_3129,A_3130] :
      ( r1_xboole_0(k1_relat_1(B_3129),A_3130)
      | k7_relat_1(B_3129,A_3130) != '#skF_6'
      | ~ v1_relat_1(B_3129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49611,c_36])).

tff(c_62094,plain,(
    ! [A_3130] :
      ( r1_xboole_0('#skF_6',A_3130)
      | k7_relat_1('#skF_6',A_3130) != '#skF_6'
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49629,c_62074])).

tff(c_62101,plain,(
    ! [A_3130] :
      ( r1_xboole_0('#skF_6',A_3130)
      | k7_relat_1('#skF_6',A_3130) != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7644,c_62094])).

tff(c_66019,plain,(
    ! [A_3130] :
      ( r1_xboole_0('#skF_4',A_3130)
      | k7_relat_1('#skF_4',A_3130) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66007,c_66007,c_66007,c_62101])).

tff(c_61931,plain,(
    v4_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_61924])).

tff(c_64934,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_61931,c_64925])).

tff(c_64943,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7643,c_64934])).

tff(c_66124,plain,(
    ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_64943])).

tff(c_66342,plain,(
    ! [C_3414,A_3415,B_3416] :
      ( v1_partfun1(C_3414,A_3415)
      | ~ v1_funct_2(C_3414,A_3415,B_3416)
      | ~ v1_funct_1(C_3414)
      | ~ m1_subset_1(C_3414,k1_zfmisc_1(k2_zfmisc_1(A_3415,B_3416)))
      | v1_xboole_0(B_3416) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_66348,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_66342])).

tff(c_66355,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_66348])).

tff(c_66357,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_66124,c_66355])).

tff(c_66358,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_64943])).

tff(c_61933,plain,(
    ! [A_22,B_24] :
      ( k7_relat_1(A_22,B_24) = '#skF_6'
      | ~ r1_xboole_0(B_24,k1_relat_1(A_22))
      | ~ v1_relat_1(A_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49611,c_24])).

tff(c_67311,plain,(
    ! [A_3511,B_3512] :
      ( k7_relat_1(A_3511,B_3512) = '#skF_4'
      | ~ r1_xboole_0(B_3512,k1_relat_1(A_3511))
      | ~ v1_relat_1(A_3511) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66007,c_61933])).

tff(c_67338,plain,(
    ! [B_3512] :
      ( k7_relat_1('#skF_7',B_3512) = '#skF_4'
      | ~ r1_xboole_0(B_3512,'#skF_5')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66358,c_67311])).

tff(c_67357,plain,(
    ! [B_3513] :
      ( k7_relat_1('#skF_7',B_3513) = '#skF_4'
      | ~ r1_xboole_0(B_3513,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7643,c_67338])).

tff(c_67369,plain,
    ( k7_relat_1('#skF_7','#skF_4') = '#skF_4'
    | k7_relat_1('#skF_4','#skF_5') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_66019,c_67357])).

tff(c_67391,plain,(
    k7_relat_1('#skF_7','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66599,c_67369])).

tff(c_67411,plain,(
    ! [B_20] :
      ( k9_relat_1('#skF_7',B_20) = k9_relat_1('#skF_4',B_20)
      | ~ r1_tarski(B_20,'#skF_4')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67391,c_22])).

tff(c_67604,plain,(
    ! [B_3519] :
      ( k9_relat_1('#skF_7',B_3519) = k9_relat_1('#skF_4',B_3519)
      | ~ r1_tarski(B_3519,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7643,c_67411])).

tff(c_67608,plain,(
    k9_relat_1('#skF_7','#skF_4') = k9_relat_1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_66046,c_67604])).

tff(c_67610,plain,(
    k9_relat_1('#skF_7','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66043,c_67608])).

tff(c_66054,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66007,c_86])).

tff(c_66053,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66007,c_84])).

tff(c_66052,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66007,c_82])).

tff(c_66937,plain,(
    ! [A_3468,D_3467,B_3471,E_3470,F_3469,C_3466] :
      ( m1_subset_1(k1_tmap_1(A_3468,B_3471,C_3466,D_3467,E_3470,F_3469),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_3468,C_3466,D_3467),B_3471)))
      | ~ m1_subset_1(F_3469,k1_zfmisc_1(k2_zfmisc_1(D_3467,B_3471)))
      | ~ v1_funct_2(F_3469,D_3467,B_3471)
      | ~ v1_funct_1(F_3469)
      | ~ m1_subset_1(E_3470,k1_zfmisc_1(k2_zfmisc_1(C_3466,B_3471)))
      | ~ v1_funct_2(E_3470,C_3466,B_3471)
      | ~ v1_funct_1(E_3470)
      | ~ m1_subset_1(D_3467,k1_zfmisc_1(A_3468))
      | v1_xboole_0(D_3467)
      | ~ m1_subset_1(C_3466,k1_zfmisc_1(A_3468))
      | v1_xboole_0(C_3466)
      | v1_xboole_0(B_3471)
      | v1_xboole_0(A_3468) ) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_42,plain,(
    ! [C_32,A_30,B_31] :
      ( v1_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_68297,plain,(
    ! [F_3556,E_3555,A_3559,B_3560,C_3557,D_3558] :
      ( v1_relat_1(k1_tmap_1(A_3559,B_3560,C_3557,D_3558,E_3555,F_3556))
      | ~ m1_subset_1(F_3556,k1_zfmisc_1(k2_zfmisc_1(D_3558,B_3560)))
      | ~ v1_funct_2(F_3556,D_3558,B_3560)
      | ~ v1_funct_1(F_3556)
      | ~ m1_subset_1(E_3555,k1_zfmisc_1(k2_zfmisc_1(C_3557,B_3560)))
      | ~ v1_funct_2(E_3555,C_3557,B_3560)
      | ~ v1_funct_1(E_3555)
      | ~ m1_subset_1(D_3558,k1_zfmisc_1(A_3559))
      | v1_xboole_0(D_3558)
      | ~ m1_subset_1(C_3557,k1_zfmisc_1(A_3559))
      | v1_xboole_0(C_3557)
      | v1_xboole_0(B_3560)
      | v1_xboole_0(A_3559) ) ),
    inference(resolution,[status(thm)],[c_66937,c_42])).

tff(c_68303,plain,(
    ! [A_3559,C_3557,E_3555] :
      ( v1_relat_1(k1_tmap_1(A_3559,'#skF_3',C_3557,'#skF_5',E_3555,'#skF_7'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_3555,k1_zfmisc_1(k2_zfmisc_1(C_3557,'#skF_3')))
      | ~ v1_funct_2(E_3555,C_3557,'#skF_3')
      | ~ v1_funct_1(E_3555)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3559))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_3557,k1_zfmisc_1(A_3559))
      | v1_xboole_0(C_3557)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_3559) ) ),
    inference(resolution,[status(thm)],[c_76,c_68297])).

tff(c_68311,plain,(
    ! [A_3559,C_3557,E_3555] :
      ( v1_relat_1(k1_tmap_1(A_3559,'#skF_3',C_3557,'#skF_5',E_3555,'#skF_7'))
      | ~ m1_subset_1(E_3555,k1_zfmisc_1(k2_zfmisc_1(C_3557,'#skF_3')))
      | ~ v1_funct_2(E_3555,C_3557,'#skF_3')
      | ~ v1_funct_1(E_3555)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3559))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_3557,k1_zfmisc_1(A_3559))
      | v1_xboole_0(C_3557)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_3559) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_68303])).

tff(c_68448,plain,(
    ! [A_3572,C_3573,E_3574] :
      ( v1_relat_1(k1_tmap_1(A_3572,'#skF_3',C_3573,'#skF_5',E_3574,'#skF_7'))
      | ~ m1_subset_1(E_3574,k1_zfmisc_1(k2_zfmisc_1(C_3573,'#skF_3')))
      | ~ v1_funct_2(E_3574,C_3573,'#skF_3')
      | ~ v1_funct_1(E_3574)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3572))
      | ~ m1_subset_1(C_3573,k1_zfmisc_1(A_3572))
      | v1_xboole_0(C_3573)
      | v1_xboole_0(A_3572) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_92,c_68311])).

tff(c_68453,plain,(
    ! [A_3572] :
      ( v1_relat_1(k1_tmap_1(A_3572,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | ~ v1_funct_2('#skF_4','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3572))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3572))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_3572) ) ),
    inference(resolution,[status(thm)],[c_66052,c_68448])).

tff(c_68461,plain,(
    ! [A_3572] :
      ( v1_relat_1(k1_tmap_1(A_3572,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3572))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3572))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_3572) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66054,c_66053,c_68453])).

tff(c_68895,plain,(
    ! [A_3598] :
      ( v1_relat_1(k1_tmap_1(A_3598,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3598))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3598))
      | v1_xboole_0(A_3598) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_68461])).

tff(c_68898,plain,
    ( v1_relat_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_90,c_68895])).

tff(c_68901,plain,
    ( v1_relat_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_68898])).

tff(c_68902,plain,(
    v1_relat_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_68901])).

tff(c_66676,plain,(
    ! [A_3446,B_3449,D_3445,E_3448,F_3447,C_3444] :
      ( v1_funct_1(k1_tmap_1(A_3446,B_3449,C_3444,D_3445,E_3448,F_3447))
      | ~ m1_subset_1(F_3447,k1_zfmisc_1(k2_zfmisc_1(D_3445,B_3449)))
      | ~ v1_funct_2(F_3447,D_3445,B_3449)
      | ~ v1_funct_1(F_3447)
      | ~ m1_subset_1(E_3448,k1_zfmisc_1(k2_zfmisc_1(C_3444,B_3449)))
      | ~ v1_funct_2(E_3448,C_3444,B_3449)
      | ~ v1_funct_1(E_3448)
      | ~ m1_subset_1(D_3445,k1_zfmisc_1(A_3446))
      | v1_xboole_0(D_3445)
      | ~ m1_subset_1(C_3444,k1_zfmisc_1(A_3446))
      | v1_xboole_0(C_3444)
      | v1_xboole_0(B_3449)
      | v1_xboole_0(A_3446) ) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_66680,plain,(
    ! [A_3446,C_3444,E_3448] :
      ( v1_funct_1(k1_tmap_1(A_3446,'#skF_3',C_3444,'#skF_5',E_3448,'#skF_7'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_3448,k1_zfmisc_1(k2_zfmisc_1(C_3444,'#skF_3')))
      | ~ v1_funct_2(E_3448,C_3444,'#skF_3')
      | ~ v1_funct_1(E_3448)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3446))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_3444,k1_zfmisc_1(A_3446))
      | v1_xboole_0(C_3444)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_3446) ) ),
    inference(resolution,[status(thm)],[c_76,c_66676])).

tff(c_66687,plain,(
    ! [A_3446,C_3444,E_3448] :
      ( v1_funct_1(k1_tmap_1(A_3446,'#skF_3',C_3444,'#skF_5',E_3448,'#skF_7'))
      | ~ m1_subset_1(E_3448,k1_zfmisc_1(k2_zfmisc_1(C_3444,'#skF_3')))
      | ~ v1_funct_2(E_3448,C_3444,'#skF_3')
      | ~ v1_funct_1(E_3448)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3446))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_3444,k1_zfmisc_1(A_3446))
      | v1_xboole_0(C_3444)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_3446) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_66680])).

tff(c_67096,plain,(
    ! [A_3486,C_3487,E_3488] :
      ( v1_funct_1(k1_tmap_1(A_3486,'#skF_3',C_3487,'#skF_5',E_3488,'#skF_7'))
      | ~ m1_subset_1(E_3488,k1_zfmisc_1(k2_zfmisc_1(C_3487,'#skF_3')))
      | ~ v1_funct_2(E_3488,C_3487,'#skF_3')
      | ~ v1_funct_1(E_3488)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3486))
      | ~ m1_subset_1(C_3487,k1_zfmisc_1(A_3486))
      | v1_xboole_0(C_3487)
      | v1_xboole_0(A_3486) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_92,c_66687])).

tff(c_67101,plain,(
    ! [A_3486] :
      ( v1_funct_1(k1_tmap_1(A_3486,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | ~ v1_funct_2('#skF_4','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3486))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3486))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_3486) ) ),
    inference(resolution,[status(thm)],[c_66052,c_67096])).

tff(c_67109,plain,(
    ! [A_3486] :
      ( v1_funct_1(k1_tmap_1(A_3486,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3486))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3486))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_3486) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66054,c_66053,c_67101])).

tff(c_67897,plain,(
    ! [A_3533] :
      ( v1_funct_1(k1_tmap_1(A_3533,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3533))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3533))
      | v1_xboole_0(A_3533) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_67109])).

tff(c_67900,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_90,c_67897])).

tff(c_67903,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_67900])).

tff(c_67904,plain,(
    v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_67903])).

tff(c_60,plain,(
    ! [A_44,B_45,C_46,D_47] :
      ( k2_partfun1(A_44,B_45,C_46,D_47) = k7_relat_1(C_46,D_47)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45)))
      | ~ v1_funct_1(C_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_69408,plain,(
    ! [F_3620,D_3622,E_3619,D_3623,B_3625,C_3621,A_3624] :
      ( k2_partfun1(k4_subset_1(A_3624,C_3621,D_3623),B_3625,k1_tmap_1(A_3624,B_3625,C_3621,D_3623,E_3619,F_3620),D_3622) = k7_relat_1(k1_tmap_1(A_3624,B_3625,C_3621,D_3623,E_3619,F_3620),D_3622)
      | ~ v1_funct_1(k1_tmap_1(A_3624,B_3625,C_3621,D_3623,E_3619,F_3620))
      | ~ m1_subset_1(F_3620,k1_zfmisc_1(k2_zfmisc_1(D_3623,B_3625)))
      | ~ v1_funct_2(F_3620,D_3623,B_3625)
      | ~ v1_funct_1(F_3620)
      | ~ m1_subset_1(E_3619,k1_zfmisc_1(k2_zfmisc_1(C_3621,B_3625)))
      | ~ v1_funct_2(E_3619,C_3621,B_3625)
      | ~ v1_funct_1(E_3619)
      | ~ m1_subset_1(D_3623,k1_zfmisc_1(A_3624))
      | v1_xboole_0(D_3623)
      | ~ m1_subset_1(C_3621,k1_zfmisc_1(A_3624))
      | v1_xboole_0(C_3621)
      | v1_xboole_0(B_3625)
      | v1_xboole_0(A_3624) ) ),
    inference(resolution,[status(thm)],[c_66937,c_60])).

tff(c_69414,plain,(
    ! [A_3624,C_3621,E_3619,D_3622] :
      ( k2_partfun1(k4_subset_1(A_3624,C_3621,'#skF_5'),'#skF_3',k1_tmap_1(A_3624,'#skF_3',C_3621,'#skF_5',E_3619,'#skF_7'),D_3622) = k7_relat_1(k1_tmap_1(A_3624,'#skF_3',C_3621,'#skF_5',E_3619,'#skF_7'),D_3622)
      | ~ v1_funct_1(k1_tmap_1(A_3624,'#skF_3',C_3621,'#skF_5',E_3619,'#skF_7'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_3619,k1_zfmisc_1(k2_zfmisc_1(C_3621,'#skF_3')))
      | ~ v1_funct_2(E_3619,C_3621,'#skF_3')
      | ~ v1_funct_1(E_3619)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3624))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_3621,k1_zfmisc_1(A_3624))
      | v1_xboole_0(C_3621)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_3624) ) ),
    inference(resolution,[status(thm)],[c_76,c_69408])).

tff(c_69422,plain,(
    ! [A_3624,C_3621,E_3619,D_3622] :
      ( k2_partfun1(k4_subset_1(A_3624,C_3621,'#skF_5'),'#skF_3',k1_tmap_1(A_3624,'#skF_3',C_3621,'#skF_5',E_3619,'#skF_7'),D_3622) = k7_relat_1(k1_tmap_1(A_3624,'#skF_3',C_3621,'#skF_5',E_3619,'#skF_7'),D_3622)
      | ~ v1_funct_1(k1_tmap_1(A_3624,'#skF_3',C_3621,'#skF_5',E_3619,'#skF_7'))
      | ~ m1_subset_1(E_3619,k1_zfmisc_1(k2_zfmisc_1(C_3621,'#skF_3')))
      | ~ v1_funct_2(E_3619,C_3621,'#skF_3')
      | ~ v1_funct_1(E_3619)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3624))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_3621,k1_zfmisc_1(A_3624))
      | v1_xboole_0(C_3621)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_3624) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_69414])).

tff(c_70176,plain,(
    ! [A_3701,C_3702,E_3703,D_3704] :
      ( k2_partfun1(k4_subset_1(A_3701,C_3702,'#skF_5'),'#skF_3',k1_tmap_1(A_3701,'#skF_3',C_3702,'#skF_5',E_3703,'#skF_7'),D_3704) = k7_relat_1(k1_tmap_1(A_3701,'#skF_3',C_3702,'#skF_5',E_3703,'#skF_7'),D_3704)
      | ~ v1_funct_1(k1_tmap_1(A_3701,'#skF_3',C_3702,'#skF_5',E_3703,'#skF_7'))
      | ~ m1_subset_1(E_3703,k1_zfmisc_1(k2_zfmisc_1(C_3702,'#skF_3')))
      | ~ v1_funct_2(E_3703,C_3702,'#skF_3')
      | ~ v1_funct_1(E_3703)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3701))
      | ~ m1_subset_1(C_3702,k1_zfmisc_1(A_3701))
      | v1_xboole_0(C_3702)
      | v1_xboole_0(A_3701) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_92,c_69422])).

tff(c_70181,plain,(
    ! [A_3701,D_3704] :
      ( k2_partfun1(k4_subset_1(A_3701,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_3701,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),D_3704) = k7_relat_1(k1_tmap_1(A_3701,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),D_3704)
      | ~ v1_funct_1(k1_tmap_1(A_3701,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | ~ v1_funct_2('#skF_4','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3701))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3701))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_3701) ) ),
    inference(resolution,[status(thm)],[c_66052,c_70176])).

tff(c_70189,plain,(
    ! [A_3701,D_3704] :
      ( k2_partfun1(k4_subset_1(A_3701,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_3701,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),D_3704) = k7_relat_1(k1_tmap_1(A_3701,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),D_3704)
      | ~ v1_funct_1(k1_tmap_1(A_3701,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3701))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3701))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_3701) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66054,c_66053,c_70181])).

tff(c_70332,plain,(
    ! [A_3719,D_3720] :
      ( k2_partfun1(k4_subset_1(A_3719,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_3719,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),D_3720) = k7_relat_1(k1_tmap_1(A_3719,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),D_3720)
      | ~ v1_funct_1(k1_tmap_1(A_3719,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3719))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3719))
      | v1_xboole_0(A_3719) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_70189])).

tff(c_49725,plain,(
    ! [C_2408,A_2409,B_2410] :
      ( v4_relat_1(C_2408,A_2409)
      | ~ m1_subset_1(C_2408,k1_zfmisc_1(k2_zfmisc_1(A_2409,B_2410))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_49733,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_49725])).

tff(c_53185,plain,(
    ! [B_2645,A_2646] :
      ( k1_relat_1(B_2645) = A_2646
      | ~ v1_partfun1(B_2645,A_2646)
      | ~ v4_relat_1(B_2645,A_2646)
      | ~ v1_relat_1(B_2645) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_53191,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_49733,c_53185])).

tff(c_53200,plain,
    ( '#skF_6' = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7644,c_49629,c_53191])).

tff(c_53204,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_53200])).

tff(c_53918,plain,(
    ! [C_2690,A_2691,B_2692] :
      ( v1_partfun1(C_2690,A_2691)
      | ~ v1_funct_2(C_2690,A_2691,B_2692)
      | ~ v1_funct_1(C_2690)
      | ~ m1_subset_1(C_2690,k1_zfmisc_1(k2_zfmisc_1(A_2691,B_2692)))
      | v1_xboole_0(B_2692) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_53924,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_53918])).

tff(c_53931,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_53924])).

tff(c_53933,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_53204,c_53931])).

tff(c_53934,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_53200])).

tff(c_51297,plain,(
    ! [B_2520,A_2521] :
      ( k7_relat_1(B_2520,A_2521) = '#skF_6'
      | ~ r1_xboole_0(k1_relat_1(B_2520),A_2521)
      | ~ v1_relat_1(B_2520) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49611,c_34])).

tff(c_51308,plain,(
    ! [A_2521] :
      ( k7_relat_1('#skF_6',A_2521) = '#skF_6'
      | ~ r1_xboole_0('#skF_6',A_2521)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49629,c_51297])).

tff(c_51312,plain,(
    ! [A_2521] :
      ( k7_relat_1('#skF_6',A_2521) = '#skF_6'
      | ~ r1_xboole_0('#skF_6',A_2521) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7644,c_51308])).

tff(c_54347,plain,(
    ! [A_2731] :
      ( k7_relat_1('#skF_4',A_2731) = '#skF_4'
      | ~ r1_xboole_0('#skF_4',A_2731) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53934,c_53934,c_53934,c_51312])).

tff(c_54361,plain,(
    ! [B_29] :
      ( k7_relat_1('#skF_4',B_29) = '#skF_4'
      | ~ r1_subset_1('#skF_4',B_29)
      | v1_xboole_0(B_29)
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_54347])).

tff(c_54368,plain,(
    ! [B_2732] :
      ( k7_relat_1('#skF_4',B_2732) = '#skF_4'
      | ~ r1_subset_1('#skF_4',B_2732)
      | v1_xboole_0(B_2732) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_54361])).

tff(c_54371,plain,
    ( k7_relat_1('#skF_4','#skF_5') = '#skF_4'
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_54368])).

tff(c_54374,plain,(
    k7_relat_1('#skF_4','#skF_5') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_54371])).

tff(c_51415,plain,(
    ! [B_2529,A_2530] :
      ( r1_xboole_0(k1_relat_1(B_2529),A_2530)
      | k7_relat_1(B_2529,A_2530) != '#skF_6'
      | ~ v1_relat_1(B_2529) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49611,c_36])).

tff(c_51427,plain,(
    ! [A_2530] :
      ( r1_xboole_0('#skF_6',A_2530)
      | k7_relat_1('#skF_6',A_2530) != '#skF_6'
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49629,c_51415])).

tff(c_51432,plain,(
    ! [A_2530] :
      ( r1_xboole_0('#skF_6',A_2530)
      | k7_relat_1('#skF_6',A_2530) != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7644,c_51427])).

tff(c_53956,plain,(
    ! [A_2530] :
      ( r1_xboole_0('#skF_4',A_2530)
      | k7_relat_1('#skF_4',A_2530) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53934,c_53934,c_53934,c_51432])).

tff(c_49732,plain,(
    v4_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_49725])).

tff(c_53194,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_49732,c_53185])).

tff(c_53203,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7643,c_53194])).

tff(c_54102,plain,(
    ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_53203])).

tff(c_54119,plain,(
    ! [C_2704,A_2705,B_2706] :
      ( v1_partfun1(C_2704,A_2705)
      | ~ v1_funct_2(C_2704,A_2705,B_2706)
      | ~ v1_funct_1(C_2704)
      | ~ m1_subset_1(C_2704,k1_zfmisc_1(k2_zfmisc_1(A_2705,B_2706)))
      | v1_xboole_0(B_2706) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_54125,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_54119])).

tff(c_54132,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_54125])).

tff(c_54134,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_54102,c_54132])).

tff(c_54135,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_53203])).

tff(c_52778,plain,(
    ! [A_22,B_24] :
      ( k7_relat_1(A_22,B_24) = '#skF_6'
      | ~ r1_xboole_0(B_24,k1_relat_1(A_22))
      | ~ v1_relat_1(A_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49611,c_24])).

tff(c_54846,plain,(
    ! [A_2776,B_2777] :
      ( k7_relat_1(A_2776,B_2777) = '#skF_4'
      | ~ r1_xboole_0(B_2777,k1_relat_1(A_2776))
      | ~ v1_relat_1(A_2776) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53934,c_52778])).

tff(c_54865,plain,(
    ! [B_2777] :
      ( k7_relat_1('#skF_7',B_2777) = '#skF_4'
      | ~ r1_xboole_0(B_2777,'#skF_5')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54135,c_54846])).

tff(c_54882,plain,(
    ! [B_2778] :
      ( k7_relat_1('#skF_7',B_2778) = '#skF_4'
      | ~ r1_xboole_0(B_2778,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7643,c_54865])).

tff(c_54886,plain,
    ( k7_relat_1('#skF_7','#skF_4') = '#skF_4'
    | k7_relat_1('#skF_4','#skF_5') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_53956,c_54882])).

tff(c_54905,plain,(
    k7_relat_1('#skF_7','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54374,c_54886])).

tff(c_51339,plain,(
    ! [B_2524,A_2525] :
      ( r1_xboole_0(k1_relat_1(B_2524),A_2525)
      | k9_relat_1(B_2524,A_2525) != '#skF_6'
      | ~ v1_relat_1(B_2524) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49611,c_20])).

tff(c_51351,plain,(
    ! [A_2525] :
      ( r1_xboole_0('#skF_6',A_2525)
      | k9_relat_1('#skF_6',A_2525) != '#skF_6'
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49629,c_51339])).

tff(c_51357,plain,(
    ! [A_2526] :
      ( r1_xboole_0('#skF_6',A_2526)
      | k9_relat_1('#skF_6',A_2526) != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7644,c_51351])).

tff(c_51370,plain,(
    ! [A_2527] :
      ( k7_relat_1('#skF_6',A_2527) = '#skF_6'
      | k9_relat_1('#skF_6',A_2527) != '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_51357,c_51312])).

tff(c_51378,plain,(
    k7_relat_1('#skF_6','#skF_6') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_49654,c_51370])).

tff(c_53960,plain,(
    k7_relat_1('#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53934,c_53934,c_53934,c_51378])).

tff(c_54295,plain,(
    ! [A_2723] :
      ( r1_xboole_0('#skF_4',A_2723)
      | k7_relat_1('#skF_4',A_2723) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53934,c_53934,c_53934,c_51432])).

tff(c_49617,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = '#skF_6'
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49611,c_2])).

tff(c_53975,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = '#skF_4'
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53934,c_49617])).

tff(c_54432,plain,(
    ! [A_2735] :
      ( k3_xboole_0('#skF_4',A_2735) = '#skF_4'
      | k7_relat_1('#skF_4',A_2735) != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_54295,c_53975])).

tff(c_54439,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_54374,c_54432])).

tff(c_53135,plain,(
    ! [A_2638,B_2639,C_2640] :
      ( k9_subset_1(A_2638,B_2639,C_2640) = k3_xboole_0(B_2639,C_2640)
      | ~ m1_subset_1(C_2640,k1_zfmisc_1(A_2638)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_53147,plain,(
    ! [B_2639] : k9_subset_1('#skF_2',B_2639,'#skF_5') = k3_xboole_0(B_2639,'#skF_5') ),
    inference(resolution,[status(thm)],[c_90,c_53135])).

tff(c_53989,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53934,c_86])).

tff(c_53988,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53934,c_84])).

tff(c_53987,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53934,c_82])).

tff(c_54313,plain,(
    ! [B_2729,A_2726,D_2725,C_2724,F_2727,E_2728] :
      ( v1_funct_1(k1_tmap_1(A_2726,B_2729,C_2724,D_2725,E_2728,F_2727))
      | ~ m1_subset_1(F_2727,k1_zfmisc_1(k2_zfmisc_1(D_2725,B_2729)))
      | ~ v1_funct_2(F_2727,D_2725,B_2729)
      | ~ v1_funct_1(F_2727)
      | ~ m1_subset_1(E_2728,k1_zfmisc_1(k2_zfmisc_1(C_2724,B_2729)))
      | ~ v1_funct_2(E_2728,C_2724,B_2729)
      | ~ v1_funct_1(E_2728)
      | ~ m1_subset_1(D_2725,k1_zfmisc_1(A_2726))
      | v1_xboole_0(D_2725)
      | ~ m1_subset_1(C_2724,k1_zfmisc_1(A_2726))
      | v1_xboole_0(C_2724)
      | v1_xboole_0(B_2729)
      | v1_xboole_0(A_2726) ) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_54317,plain,(
    ! [A_2726,C_2724,E_2728] :
      ( v1_funct_1(k1_tmap_1(A_2726,'#skF_3',C_2724,'#skF_5',E_2728,'#skF_7'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_2728,k1_zfmisc_1(k2_zfmisc_1(C_2724,'#skF_3')))
      | ~ v1_funct_2(E_2728,C_2724,'#skF_3')
      | ~ v1_funct_1(E_2728)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2726))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_2724,k1_zfmisc_1(A_2726))
      | v1_xboole_0(C_2724)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2726) ) ),
    inference(resolution,[status(thm)],[c_76,c_54313])).

tff(c_54324,plain,(
    ! [A_2726,C_2724,E_2728] :
      ( v1_funct_1(k1_tmap_1(A_2726,'#skF_3',C_2724,'#skF_5',E_2728,'#skF_7'))
      | ~ m1_subset_1(E_2728,k1_zfmisc_1(k2_zfmisc_1(C_2724,'#skF_3')))
      | ~ v1_funct_2(E_2728,C_2724,'#skF_3')
      | ~ v1_funct_1(E_2728)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2726))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_2724,k1_zfmisc_1(A_2726))
      | v1_xboole_0(C_2724)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2726) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_54317])).

tff(c_55043,plain,(
    ! [A_2787,C_2788,E_2789] :
      ( v1_funct_1(k1_tmap_1(A_2787,'#skF_3',C_2788,'#skF_5',E_2789,'#skF_7'))
      | ~ m1_subset_1(E_2789,k1_zfmisc_1(k2_zfmisc_1(C_2788,'#skF_3')))
      | ~ v1_funct_2(E_2789,C_2788,'#skF_3')
      | ~ v1_funct_1(E_2789)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2787))
      | ~ m1_subset_1(C_2788,k1_zfmisc_1(A_2787))
      | v1_xboole_0(C_2788)
      | v1_xboole_0(A_2787) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_92,c_54324])).

tff(c_55048,plain,(
    ! [A_2787] :
      ( v1_funct_1(k1_tmap_1(A_2787,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | ~ v1_funct_2('#skF_4','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2787))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2787))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_2787) ) ),
    inference(resolution,[status(thm)],[c_53987,c_55043])).

tff(c_55056,plain,(
    ! [A_2787] :
      ( v1_funct_1(k1_tmap_1(A_2787,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2787))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2787))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_2787) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53989,c_53988,c_55048])).

tff(c_55625,plain,(
    ! [A_2819] :
      ( v1_funct_1(k1_tmap_1(A_2819,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2819))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2819))
      | v1_xboole_0(A_2819) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_55056])).

tff(c_55628,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_90,c_55625])).

tff(c_55631,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_55628])).

tff(c_55632,plain,(
    v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_55631])).

tff(c_54075,plain,(
    ! [D_47] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_4',D_47) = k7_relat_1('#skF_4',D_47)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_53987,c_60])).

tff(c_54092,plain,(
    ! [D_47] : k2_partfun1('#skF_4','#skF_3','#skF_4',D_47) = k7_relat_1('#skF_4',D_47) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53989,c_54075])).

tff(c_54052,plain,(
    ! [A_2697,B_2698,C_2699,D_2700] :
      ( k2_partfun1(A_2697,B_2698,C_2699,D_2700) = k7_relat_1(C_2699,D_2700)
      | ~ m1_subset_1(C_2699,k1_zfmisc_1(k2_zfmisc_1(A_2697,B_2698)))
      | ~ v1_funct_1(C_2699) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_54054,plain,(
    ! [D_2700] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_7',D_2700) = k7_relat_1('#skF_7',D_2700)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_76,c_54052])).

tff(c_54057,plain,(
    ! [D_2700] : k2_partfun1('#skF_5','#skF_3','#skF_7',D_2700) = k7_relat_1('#skF_7',D_2700) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_54054])).

tff(c_54753,plain,(
    ! [F_2761,A_2758,C_2759,B_2762,E_2757,D_2760] :
      ( k2_partfun1(k4_subset_1(A_2758,C_2759,D_2760),B_2762,k1_tmap_1(A_2758,B_2762,C_2759,D_2760,E_2757,F_2761),D_2760) = F_2761
      | ~ m1_subset_1(k1_tmap_1(A_2758,B_2762,C_2759,D_2760,E_2757,F_2761),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_2758,C_2759,D_2760),B_2762)))
      | ~ v1_funct_2(k1_tmap_1(A_2758,B_2762,C_2759,D_2760,E_2757,F_2761),k4_subset_1(A_2758,C_2759,D_2760),B_2762)
      | ~ v1_funct_1(k1_tmap_1(A_2758,B_2762,C_2759,D_2760,E_2757,F_2761))
      | k2_partfun1(D_2760,B_2762,F_2761,k9_subset_1(A_2758,C_2759,D_2760)) != k2_partfun1(C_2759,B_2762,E_2757,k9_subset_1(A_2758,C_2759,D_2760))
      | ~ m1_subset_1(F_2761,k1_zfmisc_1(k2_zfmisc_1(D_2760,B_2762)))
      | ~ v1_funct_2(F_2761,D_2760,B_2762)
      | ~ v1_funct_1(F_2761)
      | ~ m1_subset_1(E_2757,k1_zfmisc_1(k2_zfmisc_1(C_2759,B_2762)))
      | ~ v1_funct_2(E_2757,C_2759,B_2762)
      | ~ v1_funct_1(E_2757)
      | ~ m1_subset_1(D_2760,k1_zfmisc_1(A_2758))
      | v1_xboole_0(D_2760)
      | ~ m1_subset_1(C_2759,k1_zfmisc_1(A_2758))
      | v1_xboole_0(C_2759)
      | v1_xboole_0(B_2762)
      | v1_xboole_0(A_2758) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_57702,plain,(
    ! [C_2953,F_2956,B_2958,A_2955,E_2957,D_2954] :
      ( k2_partfun1(k4_subset_1(A_2955,C_2953,D_2954),B_2958,k1_tmap_1(A_2955,B_2958,C_2953,D_2954,E_2957,F_2956),D_2954) = F_2956
      | ~ v1_funct_2(k1_tmap_1(A_2955,B_2958,C_2953,D_2954,E_2957,F_2956),k4_subset_1(A_2955,C_2953,D_2954),B_2958)
      | ~ v1_funct_1(k1_tmap_1(A_2955,B_2958,C_2953,D_2954,E_2957,F_2956))
      | k2_partfun1(D_2954,B_2958,F_2956,k9_subset_1(A_2955,C_2953,D_2954)) != k2_partfun1(C_2953,B_2958,E_2957,k9_subset_1(A_2955,C_2953,D_2954))
      | ~ m1_subset_1(F_2956,k1_zfmisc_1(k2_zfmisc_1(D_2954,B_2958)))
      | ~ v1_funct_2(F_2956,D_2954,B_2958)
      | ~ v1_funct_1(F_2956)
      | ~ m1_subset_1(E_2957,k1_zfmisc_1(k2_zfmisc_1(C_2953,B_2958)))
      | ~ v1_funct_2(E_2957,C_2953,B_2958)
      | ~ v1_funct_1(E_2957)
      | ~ m1_subset_1(D_2954,k1_zfmisc_1(A_2955))
      | v1_xboole_0(D_2954)
      | ~ m1_subset_1(C_2953,k1_zfmisc_1(A_2955))
      | v1_xboole_0(C_2953)
      | v1_xboole_0(B_2958)
      | v1_xboole_0(A_2955) ) ),
    inference(resolution,[status(thm)],[c_68,c_54753])).

tff(c_59811,plain,(
    ! [A_3049,E_3051,F_3050,D_3048,B_3052,C_3047] :
      ( k2_partfun1(k4_subset_1(A_3049,C_3047,D_3048),B_3052,k1_tmap_1(A_3049,B_3052,C_3047,D_3048,E_3051,F_3050),D_3048) = F_3050
      | ~ v1_funct_1(k1_tmap_1(A_3049,B_3052,C_3047,D_3048,E_3051,F_3050))
      | k2_partfun1(D_3048,B_3052,F_3050,k9_subset_1(A_3049,C_3047,D_3048)) != k2_partfun1(C_3047,B_3052,E_3051,k9_subset_1(A_3049,C_3047,D_3048))
      | ~ m1_subset_1(F_3050,k1_zfmisc_1(k2_zfmisc_1(D_3048,B_3052)))
      | ~ v1_funct_2(F_3050,D_3048,B_3052)
      | ~ v1_funct_1(F_3050)
      | ~ m1_subset_1(E_3051,k1_zfmisc_1(k2_zfmisc_1(C_3047,B_3052)))
      | ~ v1_funct_2(E_3051,C_3047,B_3052)
      | ~ v1_funct_1(E_3051)
      | ~ m1_subset_1(D_3048,k1_zfmisc_1(A_3049))
      | v1_xboole_0(D_3048)
      | ~ m1_subset_1(C_3047,k1_zfmisc_1(A_3049))
      | v1_xboole_0(C_3047)
      | v1_xboole_0(B_3052)
      | v1_xboole_0(A_3049) ) ),
    inference(resolution,[status(thm)],[c_70,c_57702])).

tff(c_59817,plain,(
    ! [A_3049,C_3047,E_3051] :
      ( k2_partfun1(k4_subset_1(A_3049,C_3047,'#skF_5'),'#skF_3',k1_tmap_1(A_3049,'#skF_3',C_3047,'#skF_5',E_3051,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_3049,'#skF_3',C_3047,'#skF_5',E_3051,'#skF_7'))
      | k2_partfun1(C_3047,'#skF_3',E_3051,k9_subset_1(A_3049,C_3047,'#skF_5')) != k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1(A_3049,C_3047,'#skF_5'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_3051,k1_zfmisc_1(k2_zfmisc_1(C_3047,'#skF_3')))
      | ~ v1_funct_2(E_3051,C_3047,'#skF_3')
      | ~ v1_funct_1(E_3051)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3049))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_3047,k1_zfmisc_1(A_3049))
      | v1_xboole_0(C_3047)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_3049) ) ),
    inference(resolution,[status(thm)],[c_76,c_59811])).

tff(c_59825,plain,(
    ! [A_3049,C_3047,E_3051] :
      ( k2_partfun1(k4_subset_1(A_3049,C_3047,'#skF_5'),'#skF_3',k1_tmap_1(A_3049,'#skF_3',C_3047,'#skF_5',E_3051,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_3049,'#skF_3',C_3047,'#skF_5',E_3051,'#skF_7'))
      | k2_partfun1(C_3047,'#skF_3',E_3051,k9_subset_1(A_3049,C_3047,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_3049,C_3047,'#skF_5'))
      | ~ m1_subset_1(E_3051,k1_zfmisc_1(k2_zfmisc_1(C_3047,'#skF_3')))
      | ~ v1_funct_2(E_3051,C_3047,'#skF_3')
      | ~ v1_funct_1(E_3051)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3049))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_3047,k1_zfmisc_1(A_3049))
      | v1_xboole_0(C_3047)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_3049) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_54057,c_59817])).

tff(c_60660,plain,(
    ! [A_3069,C_3070,E_3071] :
      ( k2_partfun1(k4_subset_1(A_3069,C_3070,'#skF_5'),'#skF_3',k1_tmap_1(A_3069,'#skF_3',C_3070,'#skF_5',E_3071,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_3069,'#skF_3',C_3070,'#skF_5',E_3071,'#skF_7'))
      | k2_partfun1(C_3070,'#skF_3',E_3071,k9_subset_1(A_3069,C_3070,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_3069,C_3070,'#skF_5'))
      | ~ m1_subset_1(E_3071,k1_zfmisc_1(k2_zfmisc_1(C_3070,'#skF_3')))
      | ~ v1_funct_2(E_3071,C_3070,'#skF_3')
      | ~ v1_funct_1(E_3071)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3069))
      | ~ m1_subset_1(C_3070,k1_zfmisc_1(A_3069))
      | v1_xboole_0(C_3070)
      | v1_xboole_0(A_3069) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_92,c_59825])).

tff(c_60665,plain,(
    ! [A_3069] :
      ( k2_partfun1(k4_subset_1(A_3069,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_3069,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_3069,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | k2_partfun1('#skF_4','#skF_3','#skF_4',k9_subset_1(A_3069,'#skF_4','#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_3069,'#skF_4','#skF_5'))
      | ~ v1_funct_2('#skF_4','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3069))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3069))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_3069) ) ),
    inference(resolution,[status(thm)],[c_53987,c_60660])).

tff(c_60673,plain,(
    ! [A_3069] :
      ( k2_partfun1(k4_subset_1(A_3069,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_3069,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_3069,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_3069,'#skF_4','#skF_5')) != k7_relat_1('#skF_4',k9_subset_1(A_3069,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3069))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3069))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_3069) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53989,c_53988,c_54092,c_60665])).

tff(c_61834,plain,(
    ! [A_3100] :
      ( k2_partfun1(k4_subset_1(A_3100,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_3100,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_3100,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_3100,'#skF_4','#skF_5')) != k7_relat_1('#skF_4',k9_subset_1(A_3100,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3100))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3100))
      | v1_xboole_0(A_3100) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_60673])).

tff(c_49661,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_7591])).

tff(c_53971,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),'#skF_5') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53934,c_49661])).

tff(c_61843,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k7_relat_1('#skF_4',k9_subset_1('#skF_2','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_61834,c_53971])).

tff(c_61856,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_90,c_54905,c_53960,c_54439,c_54439,c_53147,c_53147,c_55632,c_61843])).

tff(c_61858,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_61856])).

tff(c_61860,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_7591])).

tff(c_66027,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),'#skF_5') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66007,c_61860])).

tff(c_70341,plain,
    ( k7_relat_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),'#skF_5') = '#skF_7'
    | ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_70332,c_66027])).

tff(c_70356,plain,
    ( k7_relat_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),'#skF_5') = '#skF_7'
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_90,c_67904,c_70341])).

tff(c_70357,plain,(
    k7_relat_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),'#skF_5') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_70356])).

tff(c_70380,plain,(
    ! [B_20] :
      ( k9_relat_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),B_20) = k9_relat_1('#skF_7',B_20)
      | ~ r1_tarski(B_20,'#skF_5')
      | ~ v1_relat_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70357,c_22])).

tff(c_70408,plain,(
    ! [B_3727] :
      ( k9_relat_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),B_3727) = k9_relat_1('#skF_7',B_3727)
      | ~ r1_tarski(B_3727,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68902,c_70380])).

tff(c_64892,plain,(
    ! [B_16,A_15] :
      ( r1_xboole_0(k1_relat_1(B_16),A_15)
      | k9_relat_1(B_16,A_15) != '#skF_6'
      | ~ v1_relat_1(B_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49611,c_20])).

tff(c_67646,plain,(
    ! [B_3521,A_3522] :
      ( r1_xboole_0(k1_relat_1(B_3521),A_3522)
      | k9_relat_1(B_3521,A_3522) != '#skF_4'
      | ~ v1_relat_1(B_3521) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66007,c_64892])).

tff(c_62027,plain,(
    ! [B_27,A_26] :
      ( k7_relat_1(B_27,A_26) = '#skF_6'
      | ~ r1_xboole_0(k1_relat_1(B_27),A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49611,c_34])).

tff(c_66025,plain,(
    ! [B_27,A_26] :
      ( k7_relat_1(B_27,A_26) = '#skF_4'
      | ~ r1_xboole_0(k1_relat_1(B_27),A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66007,c_62027])).

tff(c_67680,plain,(
    ! [B_3521,A_3522] :
      ( k7_relat_1(B_3521,A_3522) = '#skF_4'
      | k9_relat_1(B_3521,A_3522) != '#skF_4'
      | ~ v1_relat_1(B_3521) ) ),
    inference(resolution,[status(thm)],[c_67646,c_66025])).

tff(c_70417,plain,(
    ! [B_3727] :
      ( k7_relat_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),B_3727) = '#skF_4'
      | k9_relat_1('#skF_7',B_3727) != '#skF_4'
      | ~ v1_relat_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | ~ r1_tarski(B_3727,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70408,c_67680])).

tff(c_70500,plain,(
    ! [B_3733] :
      ( k7_relat_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),B_3733) = '#skF_4'
      | k9_relat_1('#skF_7',B_3733) != '#skF_4'
      | ~ r1_tarski(B_3733,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68902,c_70417])).

tff(c_61859,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_7591])).

tff(c_66035,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),'#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66007,c_66007,c_61859])).

tff(c_70338,plain,
    ( k7_relat_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),'#skF_4') != '#skF_4'
    | ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_70332,c_66035])).

tff(c_70353,plain,
    ( k7_relat_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),'#skF_4') != '#skF_4'
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_90,c_67904,c_70338])).

tff(c_70354,plain,(
    k7_relat_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),'#skF_4') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_70353])).

tff(c_70509,plain,
    ( k9_relat_1('#skF_7','#skF_4') != '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_70500,c_70354])).

tff(c_70560,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66046,c_67610,c_70509])).

tff(c_70561,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_7652])).

tff(c_70562,plain,(
    k1_relat_1('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_7652])).

tff(c_70577,plain,(
    k1_relat_1('#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70561,c_70562])).

tff(c_70609,plain,(
    ! [C_3736,A_3737,B_3738] :
      ( v4_relat_1(C_3736,A_3737)
      | ~ m1_subset_1(C_3736,k1_zfmisc_1(k2_zfmisc_1(A_3737,B_3738))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_70616,plain,(
    v4_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_70609])).

tff(c_81604,plain,(
    ! [B_4500,A_4501] :
      ( k1_relat_1(B_4500) = A_4501
      | ~ v1_partfun1(B_4500,A_4501)
      | ~ v4_relat_1(B_4500,A_4501)
      | ~ v1_relat_1(B_4500) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_81613,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_70616,c_81604])).

tff(c_81622,plain,
    ( '#skF_7' = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7643,c_70577,c_81613])).

tff(c_81623,plain,(
    ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_81622])).

tff(c_81864,plain,(
    ! [C_4525,A_4526,B_4527] :
      ( v1_partfun1(C_4525,A_4526)
      | ~ v1_funct_2(C_4525,A_4526,B_4527)
      | ~ v1_funct_1(C_4525)
      | ~ m1_subset_1(C_4525,k1_zfmisc_1(k2_zfmisc_1(A_4526,B_4527)))
      | v1_xboole_0(B_4527) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_81867,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_81864])).

tff(c_81873,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_81867])).

tff(c_81875,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_81623,c_81873])).

tff(c_81876,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_81622])).

tff(c_81368,plain,(
    ! [A_4483,B_4484] :
      ( k7_relat_1(A_4483,B_4484) = '#skF_7'
      | ~ r1_xboole_0(B_4484,k1_relat_1(A_4483))
      | ~ v1_relat_1(A_4483) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70561,c_24])).

tff(c_81399,plain,(
    ! [B_4484] :
      ( k7_relat_1('#skF_7',B_4484) = '#skF_7'
      | ~ r1_xboole_0(B_4484,'#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70577,c_81368])).

tff(c_81408,plain,(
    ! [B_4484] :
      ( k7_relat_1('#skF_7',B_4484) = '#skF_7'
      | ~ r1_xboole_0(B_4484,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7643,c_81399])).

tff(c_82189,plain,(
    ! [B_4555] :
      ( k7_relat_1('#skF_5',B_4555) = '#skF_5'
      | ~ r1_xboole_0(B_4555,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81876,c_81876,c_81876,c_81408])).

tff(c_82201,plain,(
    ! [A_28] :
      ( k7_relat_1('#skF_5',A_28) = '#skF_5'
      | ~ r1_subset_1(A_28,'#skF_5')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_28) ) ),
    inference(resolution,[status(thm)],[c_40,c_82189])).

tff(c_82576,plain,(
    ! [A_4589] :
      ( k7_relat_1('#skF_5',A_4589) = '#skF_5'
      | ~ r1_subset_1(A_4589,'#skF_5')
      | v1_xboole_0(A_4589) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_82201])).

tff(c_82583,plain,
    ( k7_relat_1('#skF_5','#skF_4') = '#skF_5'
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_88,c_82576])).

tff(c_82590,plain,(
    k7_relat_1('#skF_5','#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_82583])).

tff(c_81183,plain,(
    ! [B_4473,A_4474] :
      ( r1_xboole_0(k1_relat_1(B_4473),A_4474)
      | k7_relat_1(B_4473,A_4474) != '#skF_7'
      | ~ v1_relat_1(B_4473) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70561,c_36])).

tff(c_81198,plain,(
    ! [A_4474] :
      ( r1_xboole_0('#skF_7',A_4474)
      | k7_relat_1('#skF_7',A_4474) != '#skF_7'
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70577,c_81183])).

tff(c_81204,plain,(
    ! [A_4474] :
      ( r1_xboole_0('#skF_7',A_4474)
      | k7_relat_1('#skF_7',A_4474) != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7643,c_81198])).

tff(c_81893,plain,(
    ! [A_4474] :
      ( r1_xboole_0('#skF_5',A_4474)
      | k7_relat_1('#skF_5',A_4474) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81876,c_81876,c_81876,c_81204])).

tff(c_70617,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_70609])).

tff(c_81610,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_70617,c_81604])).

tff(c_81619,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7644,c_81610])).

tff(c_82047,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_81619])).

tff(c_82056,plain,(
    ! [C_4539,A_4540,B_4541] :
      ( v1_partfun1(C_4539,A_4540)
      | ~ v1_funct_2(C_4539,A_4540,B_4541)
      | ~ v1_funct_1(C_4539)
      | ~ m1_subset_1(C_4539,k1_zfmisc_1(k2_zfmisc_1(A_4540,B_4541)))
      | v1_xboole_0(B_4541) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_82062,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_82056])).

tff(c_82069,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82062])).

tff(c_82071,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_82047,c_82069])).

tff(c_82072,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_81619])).

tff(c_81367,plain,(
    ! [A_22,B_24] :
      ( k7_relat_1(A_22,B_24) = '#skF_7'
      | ~ r1_xboole_0(B_24,k1_relat_1(A_22))
      | ~ v1_relat_1(A_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70561,c_24])).

tff(c_82735,plain,(
    ! [A_4607,B_4608] :
      ( k7_relat_1(A_4607,B_4608) = '#skF_5'
      | ~ r1_xboole_0(B_4608,k1_relat_1(A_4607))
      | ~ v1_relat_1(A_4607) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81876,c_81367])).

tff(c_82762,plain,(
    ! [B_4608] :
      ( k7_relat_1('#skF_6',B_4608) = '#skF_5'
      | ~ r1_xboole_0(B_4608,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82072,c_82735])).

tff(c_82785,plain,(
    ! [B_4615] :
      ( k7_relat_1('#skF_6',B_4615) = '#skF_5'
      | ~ r1_xboole_0(B_4615,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7644,c_82762])).

tff(c_82801,plain,
    ( k7_relat_1('#skF_6','#skF_5') = '#skF_5'
    | k7_relat_1('#skF_5','#skF_4') != '#skF_5' ),
    inference(resolution,[status(thm)],[c_81893,c_82785])).

tff(c_82820,plain,(
    k7_relat_1('#skF_6','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82590,c_82801])).

tff(c_81182,plain,(
    ! [B_27,A_26] :
      ( r1_xboole_0(k1_relat_1(B_27),A_26)
      | k7_relat_1(B_27,A_26) != '#skF_7'
      | ~ v1_relat_1(B_27) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70561,c_36])).

tff(c_82685,plain,(
    ! [B_4602,A_4603] :
      ( r1_xboole_0(k1_relat_1(B_4602),A_4603)
      | k7_relat_1(B_4602,A_4603) != '#skF_5'
      | ~ v1_relat_1(B_4602) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81876,c_81182])).

tff(c_82698,plain,(
    ! [A_4603] :
      ( r1_xboole_0('#skF_4',A_4603)
      | k7_relat_1('#skF_6',A_4603) != '#skF_5'
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82072,c_82685])).

tff(c_82709,plain,(
    ! [A_4604] :
      ( r1_xboole_0('#skF_4',A_4604)
      | k7_relat_1('#skF_6',A_4604) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7644,c_82698])).

tff(c_70565,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = '#skF_7'
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70561,c_2])).

tff(c_81909,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = '#skF_5'
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81876,c_70565])).

tff(c_82722,plain,(
    ! [A_4604] :
      ( k3_xboole_0('#skF_4',A_4604) = '#skF_5'
      | k7_relat_1('#skF_6',A_4604) != '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_82709,c_81909])).

tff(c_82840,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_82820,c_82722])).

tff(c_70571,plain,(
    k2_relat_1('#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70561,c_70561,c_26])).

tff(c_70582,plain,(
    ! [A_3734] :
      ( k9_relat_1(A_3734,k1_relat_1(A_3734)) = k2_relat_1(A_3734)
      | ~ v1_relat_1(A_3734) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_70591,plain,
    ( k9_relat_1('#skF_7','#skF_7') = k2_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_70577,c_70582])).

tff(c_70595,plain,(
    k9_relat_1('#skF_7','#skF_7') = k2_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7643,c_70591])).

tff(c_70619,plain,(
    k9_relat_1('#skF_7','#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70571,c_70595])).

tff(c_81051,plain,(
    ! [B_4461,A_4462] :
      ( r1_xboole_0(k1_relat_1(B_4461),A_4462)
      | k9_relat_1(B_4461,A_4462) != '#skF_7'
      | ~ v1_relat_1(B_4461) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70561,c_20])).

tff(c_81057,plain,(
    ! [A_4462] :
      ( r1_xboole_0('#skF_7',A_4462)
      | k9_relat_1('#skF_7',A_4462) != '#skF_7'
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70577,c_81051])).

tff(c_81060,plain,(
    ! [A_4462] :
      ( r1_xboole_0('#skF_7',A_4462)
      | k9_relat_1('#skF_7',A_4462) != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7643,c_81057])).

tff(c_81167,plain,(
    ! [B_4471,A_4472] :
      ( k7_relat_1(B_4471,A_4472) = '#skF_7'
      | ~ r1_xboole_0(k1_relat_1(B_4471),A_4472)
      | ~ v1_relat_1(B_4471) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70561,c_34])).

tff(c_81177,plain,(
    ! [A_4472] :
      ( k7_relat_1('#skF_7',A_4472) = '#skF_7'
      | ~ r1_xboole_0('#skF_7',A_4472)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70577,c_81167])).

tff(c_81205,plain,(
    ! [A_4475] :
      ( k7_relat_1('#skF_7',A_4475) = '#skF_7'
      | ~ r1_xboole_0('#skF_7',A_4475) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7643,c_81177])).

tff(c_81292,plain,(
    ! [A_4480] :
      ( k7_relat_1('#skF_7',A_4480) = '#skF_7'
      | k9_relat_1('#skF_7',A_4480) != '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_81060,c_81205])).

tff(c_81308,plain,(
    k7_relat_1('#skF_7','#skF_7') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_70619,c_81292])).

tff(c_81887,plain,(
    k7_relat_1('#skF_5','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81876,c_81876,c_81876,c_81308])).

tff(c_81554,plain,(
    ! [A_4493,B_4494,C_4495] :
      ( k9_subset_1(A_4493,B_4494,C_4495) = k3_xboole_0(B_4494,C_4495)
      | ~ m1_subset_1(C_4495,k1_zfmisc_1(A_4493)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_81566,plain,(
    ! [B_4494] : k9_subset_1('#skF_2',B_4494,'#skF_5') = k3_xboole_0(B_4494,'#skF_5') ),
    inference(resolution,[status(thm)],[c_90,c_81554])).

tff(c_81926,plain,(
    v1_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81876,c_80])).

tff(c_81925,plain,(
    v1_funct_2('#skF_5','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81876,c_78])).

tff(c_81924,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81876,c_76])).

tff(c_82226,plain,(
    ! [F_4560,A_4559,B_4562,C_4557,D_4558,E_4561] :
      ( v1_funct_1(k1_tmap_1(A_4559,B_4562,C_4557,D_4558,E_4561,F_4560))
      | ~ m1_subset_1(F_4560,k1_zfmisc_1(k2_zfmisc_1(D_4558,B_4562)))
      | ~ v1_funct_2(F_4560,D_4558,B_4562)
      | ~ v1_funct_1(F_4560)
      | ~ m1_subset_1(E_4561,k1_zfmisc_1(k2_zfmisc_1(C_4557,B_4562)))
      | ~ v1_funct_2(E_4561,C_4557,B_4562)
      | ~ v1_funct_1(E_4561)
      | ~ m1_subset_1(D_4558,k1_zfmisc_1(A_4559))
      | v1_xboole_0(D_4558)
      | ~ m1_subset_1(C_4557,k1_zfmisc_1(A_4559))
      | v1_xboole_0(C_4557)
      | v1_xboole_0(B_4562)
      | v1_xboole_0(A_4559) ) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_82228,plain,(
    ! [A_4559,C_4557,E_4561] :
      ( v1_funct_1(k1_tmap_1(A_4559,'#skF_3',C_4557,'#skF_5',E_4561,'#skF_5'))
      | ~ v1_funct_2('#skF_5','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_4561,k1_zfmisc_1(k2_zfmisc_1(C_4557,'#skF_3')))
      | ~ v1_funct_2(E_4561,C_4557,'#skF_3')
      | ~ v1_funct_1(E_4561)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4559))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_4557,k1_zfmisc_1(A_4559))
      | v1_xboole_0(C_4557)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_4559) ) ),
    inference(resolution,[status(thm)],[c_81924,c_82226])).

tff(c_82233,plain,(
    ! [A_4559,C_4557,E_4561] :
      ( v1_funct_1(k1_tmap_1(A_4559,'#skF_3',C_4557,'#skF_5',E_4561,'#skF_5'))
      | ~ m1_subset_1(E_4561,k1_zfmisc_1(k2_zfmisc_1(C_4557,'#skF_3')))
      | ~ v1_funct_2(E_4561,C_4557,'#skF_3')
      | ~ v1_funct_1(E_4561)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4559))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_4557,k1_zfmisc_1(A_4559))
      | v1_xboole_0(C_4557)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_4559) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81926,c_81925,c_82228])).

tff(c_83692,plain,(
    ! [A_4659,C_4660,E_4661] :
      ( v1_funct_1(k1_tmap_1(A_4659,'#skF_3',C_4660,'#skF_5',E_4661,'#skF_5'))
      | ~ m1_subset_1(E_4661,k1_zfmisc_1(k2_zfmisc_1(C_4660,'#skF_3')))
      | ~ v1_funct_2(E_4661,C_4660,'#skF_3')
      | ~ v1_funct_1(E_4661)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4659))
      | ~ m1_subset_1(C_4660,k1_zfmisc_1(A_4659))
      | v1_xboole_0(C_4660)
      | v1_xboole_0(A_4659) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_92,c_82233])).

tff(c_83699,plain,(
    ! [A_4659] :
      ( v1_funct_1(k1_tmap_1(A_4659,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_5'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4659))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4659))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_4659) ) ),
    inference(resolution,[status(thm)],[c_82,c_83692])).

tff(c_83709,plain,(
    ! [A_4659] :
      ( v1_funct_1(k1_tmap_1(A_4659,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4659))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4659))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_4659) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_83699])).

tff(c_83919,plain,(
    ! [A_4674] :
      ( v1_funct_1(k1_tmap_1(A_4674,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4674))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4674))
      | v1_xboole_0(A_4674) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_83709])).

tff(c_83925,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_5'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_90,c_83919])).

tff(c_83931,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_5'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_83925])).

tff(c_83932,plain,(
    v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_83931])).

tff(c_82003,plain,(
    ! [A_4532,B_4533,C_4534,D_4535] :
      ( k2_partfun1(A_4532,B_4533,C_4534,D_4535) = k7_relat_1(C_4534,D_4535)
      | ~ m1_subset_1(C_4534,k1_zfmisc_1(k2_zfmisc_1(A_4532,B_4533)))
      | ~ v1_funct_1(C_4534) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_82005,plain,(
    ! [D_4535] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_6',D_4535) = k7_relat_1('#skF_6',D_4535)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_82,c_82003])).

tff(c_82008,plain,(
    ! [D_4535] : k2_partfun1('#skF_4','#skF_3','#skF_6',D_4535) = k7_relat_1('#skF_6',D_4535) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82005])).

tff(c_82011,plain,(
    ! [D_47] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_5',D_47) = k7_relat_1('#skF_5',D_47)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_81924,c_60])).

tff(c_82028,plain,(
    ! [D_47] : k2_partfun1('#skF_5','#skF_3','#skF_5',D_47) = k7_relat_1('#skF_5',D_47) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81926,c_82011])).

tff(c_82781,plain,(
    ! [F_4613,C_4611,B_4614,A_4610,E_4609,D_4612] :
      ( k2_partfun1(k4_subset_1(A_4610,C_4611,D_4612),B_4614,k1_tmap_1(A_4610,B_4614,C_4611,D_4612,E_4609,F_4613),C_4611) = E_4609
      | ~ m1_subset_1(k1_tmap_1(A_4610,B_4614,C_4611,D_4612,E_4609,F_4613),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_4610,C_4611,D_4612),B_4614)))
      | ~ v1_funct_2(k1_tmap_1(A_4610,B_4614,C_4611,D_4612,E_4609,F_4613),k4_subset_1(A_4610,C_4611,D_4612),B_4614)
      | ~ v1_funct_1(k1_tmap_1(A_4610,B_4614,C_4611,D_4612,E_4609,F_4613))
      | k2_partfun1(D_4612,B_4614,F_4613,k9_subset_1(A_4610,C_4611,D_4612)) != k2_partfun1(C_4611,B_4614,E_4609,k9_subset_1(A_4610,C_4611,D_4612))
      | ~ m1_subset_1(F_4613,k1_zfmisc_1(k2_zfmisc_1(D_4612,B_4614)))
      | ~ v1_funct_2(F_4613,D_4612,B_4614)
      | ~ v1_funct_1(F_4613)
      | ~ m1_subset_1(E_4609,k1_zfmisc_1(k2_zfmisc_1(C_4611,B_4614)))
      | ~ v1_funct_2(E_4609,C_4611,B_4614)
      | ~ v1_funct_1(E_4609)
      | ~ m1_subset_1(D_4612,k1_zfmisc_1(A_4610))
      | v1_xboole_0(D_4612)
      | ~ m1_subset_1(C_4611,k1_zfmisc_1(A_4610))
      | v1_xboole_0(C_4611)
      | v1_xboole_0(B_4614)
      | v1_xboole_0(A_4610) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_85598,plain,(
    ! [A_4785,D_4784,C_4783,F_4786,E_4787,B_4788] :
      ( k2_partfun1(k4_subset_1(A_4785,C_4783,D_4784),B_4788,k1_tmap_1(A_4785,B_4788,C_4783,D_4784,E_4787,F_4786),C_4783) = E_4787
      | ~ v1_funct_2(k1_tmap_1(A_4785,B_4788,C_4783,D_4784,E_4787,F_4786),k4_subset_1(A_4785,C_4783,D_4784),B_4788)
      | ~ v1_funct_1(k1_tmap_1(A_4785,B_4788,C_4783,D_4784,E_4787,F_4786))
      | k2_partfun1(D_4784,B_4788,F_4786,k9_subset_1(A_4785,C_4783,D_4784)) != k2_partfun1(C_4783,B_4788,E_4787,k9_subset_1(A_4785,C_4783,D_4784))
      | ~ m1_subset_1(F_4786,k1_zfmisc_1(k2_zfmisc_1(D_4784,B_4788)))
      | ~ v1_funct_2(F_4786,D_4784,B_4788)
      | ~ v1_funct_1(F_4786)
      | ~ m1_subset_1(E_4787,k1_zfmisc_1(k2_zfmisc_1(C_4783,B_4788)))
      | ~ v1_funct_2(E_4787,C_4783,B_4788)
      | ~ v1_funct_1(E_4787)
      | ~ m1_subset_1(D_4784,k1_zfmisc_1(A_4785))
      | v1_xboole_0(D_4784)
      | ~ m1_subset_1(C_4783,k1_zfmisc_1(A_4785))
      | v1_xboole_0(C_4783)
      | v1_xboole_0(B_4788)
      | v1_xboole_0(A_4785) ) ),
    inference(resolution,[status(thm)],[c_68,c_82781])).

tff(c_86297,plain,(
    ! [D_4857,A_4858,C_4856,F_4859,E_4860,B_4861] :
      ( k2_partfun1(k4_subset_1(A_4858,C_4856,D_4857),B_4861,k1_tmap_1(A_4858,B_4861,C_4856,D_4857,E_4860,F_4859),C_4856) = E_4860
      | ~ v1_funct_1(k1_tmap_1(A_4858,B_4861,C_4856,D_4857,E_4860,F_4859))
      | k2_partfun1(D_4857,B_4861,F_4859,k9_subset_1(A_4858,C_4856,D_4857)) != k2_partfun1(C_4856,B_4861,E_4860,k9_subset_1(A_4858,C_4856,D_4857))
      | ~ m1_subset_1(F_4859,k1_zfmisc_1(k2_zfmisc_1(D_4857,B_4861)))
      | ~ v1_funct_2(F_4859,D_4857,B_4861)
      | ~ v1_funct_1(F_4859)
      | ~ m1_subset_1(E_4860,k1_zfmisc_1(k2_zfmisc_1(C_4856,B_4861)))
      | ~ v1_funct_2(E_4860,C_4856,B_4861)
      | ~ v1_funct_1(E_4860)
      | ~ m1_subset_1(D_4857,k1_zfmisc_1(A_4858))
      | v1_xboole_0(D_4857)
      | ~ m1_subset_1(C_4856,k1_zfmisc_1(A_4858))
      | v1_xboole_0(C_4856)
      | v1_xboole_0(B_4861)
      | v1_xboole_0(A_4858) ) ),
    inference(resolution,[status(thm)],[c_70,c_85598])).

tff(c_86301,plain,(
    ! [A_4858,C_4856,E_4860] :
      ( k2_partfun1(k4_subset_1(A_4858,C_4856,'#skF_5'),'#skF_3',k1_tmap_1(A_4858,'#skF_3',C_4856,'#skF_5',E_4860,'#skF_5'),C_4856) = E_4860
      | ~ v1_funct_1(k1_tmap_1(A_4858,'#skF_3',C_4856,'#skF_5',E_4860,'#skF_5'))
      | k2_partfun1(C_4856,'#skF_3',E_4860,k9_subset_1(A_4858,C_4856,'#skF_5')) != k2_partfun1('#skF_5','#skF_3','#skF_5',k9_subset_1(A_4858,C_4856,'#skF_5'))
      | ~ v1_funct_2('#skF_5','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_4860,k1_zfmisc_1(k2_zfmisc_1(C_4856,'#skF_3')))
      | ~ v1_funct_2(E_4860,C_4856,'#skF_3')
      | ~ v1_funct_1(E_4860)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4858))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_4856,k1_zfmisc_1(A_4858))
      | v1_xboole_0(C_4856)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_4858) ) ),
    inference(resolution,[status(thm)],[c_81924,c_86297])).

tff(c_86307,plain,(
    ! [A_4858,C_4856,E_4860] :
      ( k2_partfun1(k4_subset_1(A_4858,C_4856,'#skF_5'),'#skF_3',k1_tmap_1(A_4858,'#skF_3',C_4856,'#skF_5',E_4860,'#skF_5'),C_4856) = E_4860
      | ~ v1_funct_1(k1_tmap_1(A_4858,'#skF_3',C_4856,'#skF_5',E_4860,'#skF_5'))
      | k2_partfun1(C_4856,'#skF_3',E_4860,k9_subset_1(A_4858,C_4856,'#skF_5')) != k7_relat_1('#skF_5',k9_subset_1(A_4858,C_4856,'#skF_5'))
      | ~ m1_subset_1(E_4860,k1_zfmisc_1(k2_zfmisc_1(C_4856,'#skF_3')))
      | ~ v1_funct_2(E_4860,C_4856,'#skF_3')
      | ~ v1_funct_1(E_4860)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4858))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_4856,k1_zfmisc_1(A_4858))
      | v1_xboole_0(C_4856)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_4858) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81926,c_81925,c_82028,c_86301])).

tff(c_87946,plain,(
    ! [A_4896,C_4897,E_4898] :
      ( k2_partfun1(k4_subset_1(A_4896,C_4897,'#skF_5'),'#skF_3',k1_tmap_1(A_4896,'#skF_3',C_4897,'#skF_5',E_4898,'#skF_5'),C_4897) = E_4898
      | ~ v1_funct_1(k1_tmap_1(A_4896,'#skF_3',C_4897,'#skF_5',E_4898,'#skF_5'))
      | k2_partfun1(C_4897,'#skF_3',E_4898,k9_subset_1(A_4896,C_4897,'#skF_5')) != k7_relat_1('#skF_5',k9_subset_1(A_4896,C_4897,'#skF_5'))
      | ~ m1_subset_1(E_4898,k1_zfmisc_1(k2_zfmisc_1(C_4897,'#skF_3')))
      | ~ v1_funct_2(E_4898,C_4897,'#skF_3')
      | ~ v1_funct_1(E_4898)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4896))
      | ~ m1_subset_1(C_4897,k1_zfmisc_1(A_4896))
      | v1_xboole_0(C_4897)
      | v1_xboole_0(A_4896) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_92,c_86307])).

tff(c_87953,plain,(
    ! [A_4896] :
      ( k2_partfun1(k4_subset_1(A_4896,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_4896,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_5'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_4896,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_5'))
      | k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1(A_4896,'#skF_4','#skF_5')) != k7_relat_1('#skF_5',k9_subset_1(A_4896,'#skF_4','#skF_5'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4896))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4896))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_4896) ) ),
    inference(resolution,[status(thm)],[c_82,c_87946])).

tff(c_87963,plain,(
    ! [A_4896] :
      ( k2_partfun1(k4_subset_1(A_4896,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_4896,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_5'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_4896,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_5'))
      | k7_relat_1('#skF_5',k9_subset_1(A_4896,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_4896,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4896))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4896))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_4896) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82008,c_87953])).

tff(c_89431,plain,(
    ! [A_4932] :
      ( k2_partfun1(k4_subset_1(A_4932,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_4932,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_5'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_4932,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_5'))
      | k7_relat_1('#skF_5',k9_subset_1(A_4932,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_4932,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4932))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4932))
      | v1_xboole_0(A_4932) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_87963])).

tff(c_73386,plain,(
    ! [B_3956,A_3957] :
      ( k1_relat_1(B_3956) = A_3957
      | ~ v1_partfun1(B_3956,A_3957)
      | ~ v4_relat_1(B_3956,A_3957)
      | ~ v1_relat_1(B_3956) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_73395,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_70616,c_73386])).

tff(c_73404,plain,
    ( '#skF_7' = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7643,c_70577,c_73395])).

tff(c_73405,plain,(
    ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_73404])).

tff(c_73751,plain,(
    ! [C_3987,A_3988,B_3989] :
      ( v1_partfun1(C_3987,A_3988)
      | ~ v1_funct_2(C_3987,A_3988,B_3989)
      | ~ v1_funct_1(C_3987)
      | ~ m1_subset_1(C_3987,k1_zfmisc_1(k2_zfmisc_1(A_3988,B_3989)))
      | v1_xboole_0(B_3989) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_73754,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_73751])).

tff(c_73760,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_73754])).

tff(c_73762,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_73405,c_73760])).

tff(c_73763,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_73404])).

tff(c_73815,plain,(
    v1_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73763,c_80])).

tff(c_73814,plain,(
    v1_funct_2('#skF_5','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73763,c_78])).

tff(c_73813,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73763,c_76])).

tff(c_74399,plain,(
    ! [A_4049,E_4051,D_4048,F_4050,C_4047,B_4052] :
      ( v1_funct_1(k1_tmap_1(A_4049,B_4052,C_4047,D_4048,E_4051,F_4050))
      | ~ m1_subset_1(F_4050,k1_zfmisc_1(k2_zfmisc_1(D_4048,B_4052)))
      | ~ v1_funct_2(F_4050,D_4048,B_4052)
      | ~ v1_funct_1(F_4050)
      | ~ m1_subset_1(E_4051,k1_zfmisc_1(k2_zfmisc_1(C_4047,B_4052)))
      | ~ v1_funct_2(E_4051,C_4047,B_4052)
      | ~ v1_funct_1(E_4051)
      | ~ m1_subset_1(D_4048,k1_zfmisc_1(A_4049))
      | v1_xboole_0(D_4048)
      | ~ m1_subset_1(C_4047,k1_zfmisc_1(A_4049))
      | v1_xboole_0(C_4047)
      | v1_xboole_0(B_4052)
      | v1_xboole_0(A_4049) ) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_74401,plain,(
    ! [A_4049,C_4047,E_4051] :
      ( v1_funct_1(k1_tmap_1(A_4049,'#skF_3',C_4047,'#skF_5',E_4051,'#skF_5'))
      | ~ v1_funct_2('#skF_5','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_4051,k1_zfmisc_1(k2_zfmisc_1(C_4047,'#skF_3')))
      | ~ v1_funct_2(E_4051,C_4047,'#skF_3')
      | ~ v1_funct_1(E_4051)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4049))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_4047,k1_zfmisc_1(A_4049))
      | v1_xboole_0(C_4047)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_4049) ) ),
    inference(resolution,[status(thm)],[c_73813,c_74399])).

tff(c_74406,plain,(
    ! [A_4049,C_4047,E_4051] :
      ( v1_funct_1(k1_tmap_1(A_4049,'#skF_3',C_4047,'#skF_5',E_4051,'#skF_5'))
      | ~ m1_subset_1(E_4051,k1_zfmisc_1(k2_zfmisc_1(C_4047,'#skF_3')))
      | ~ v1_funct_2(E_4051,C_4047,'#skF_3')
      | ~ v1_funct_1(E_4051)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4049))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_4047,k1_zfmisc_1(A_4049))
      | v1_xboole_0(C_4047)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_4049) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73815,c_73814,c_74401])).

tff(c_75723,plain,(
    ! [A_4139,C_4140,E_4141] :
      ( v1_funct_1(k1_tmap_1(A_4139,'#skF_3',C_4140,'#skF_5',E_4141,'#skF_5'))
      | ~ m1_subset_1(E_4141,k1_zfmisc_1(k2_zfmisc_1(C_4140,'#skF_3')))
      | ~ v1_funct_2(E_4141,C_4140,'#skF_3')
      | ~ v1_funct_1(E_4141)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4139))
      | ~ m1_subset_1(C_4140,k1_zfmisc_1(A_4139))
      | v1_xboole_0(C_4140)
      | v1_xboole_0(A_4139) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_92,c_74406])).

tff(c_75730,plain,(
    ! [A_4139] :
      ( v1_funct_1(k1_tmap_1(A_4139,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_5'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4139))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4139))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_4139) ) ),
    inference(resolution,[status(thm)],[c_82,c_75723])).

tff(c_75740,plain,(
    ! [A_4139] :
      ( v1_funct_1(k1_tmap_1(A_4139,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4139))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4139))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_4139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_75730])).

tff(c_75986,plain,(
    ! [A_4158] :
      ( v1_funct_1(k1_tmap_1(A_4158,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4158))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4158))
      | v1_xboole_0(A_4158) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_75740])).

tff(c_75992,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_5'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_90,c_75986])).

tff(c_75998,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_5'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_75992])).

tff(c_75999,plain,(
    v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_75998])).

tff(c_74638,plain,(
    ! [A_4072,B_4075,E_4074,F_4073,C_4070,D_4071] :
      ( m1_subset_1(k1_tmap_1(A_4072,B_4075,C_4070,D_4071,E_4074,F_4073),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_4072,C_4070,D_4071),B_4075)))
      | ~ m1_subset_1(F_4073,k1_zfmisc_1(k2_zfmisc_1(D_4071,B_4075)))
      | ~ v1_funct_2(F_4073,D_4071,B_4075)
      | ~ v1_funct_1(F_4073)
      | ~ m1_subset_1(E_4074,k1_zfmisc_1(k2_zfmisc_1(C_4070,B_4075)))
      | ~ v1_funct_2(E_4074,C_4070,B_4075)
      | ~ v1_funct_1(E_4074)
      | ~ m1_subset_1(D_4071,k1_zfmisc_1(A_4072))
      | v1_xboole_0(D_4071)
      | ~ m1_subset_1(C_4070,k1_zfmisc_1(A_4072))
      | v1_xboole_0(C_4070)
      | v1_xboole_0(B_4075)
      | v1_xboole_0(A_4072) ) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_77077,plain,(
    ! [A_4222,C_4224,D_4221,E_4219,B_4220,F_4225,D_4223] :
      ( k2_partfun1(k4_subset_1(A_4222,C_4224,D_4223),B_4220,k1_tmap_1(A_4222,B_4220,C_4224,D_4223,E_4219,F_4225),D_4221) = k7_relat_1(k1_tmap_1(A_4222,B_4220,C_4224,D_4223,E_4219,F_4225),D_4221)
      | ~ v1_funct_1(k1_tmap_1(A_4222,B_4220,C_4224,D_4223,E_4219,F_4225))
      | ~ m1_subset_1(F_4225,k1_zfmisc_1(k2_zfmisc_1(D_4223,B_4220)))
      | ~ v1_funct_2(F_4225,D_4223,B_4220)
      | ~ v1_funct_1(F_4225)
      | ~ m1_subset_1(E_4219,k1_zfmisc_1(k2_zfmisc_1(C_4224,B_4220)))
      | ~ v1_funct_2(E_4219,C_4224,B_4220)
      | ~ v1_funct_1(E_4219)
      | ~ m1_subset_1(D_4223,k1_zfmisc_1(A_4222))
      | v1_xboole_0(D_4223)
      | ~ m1_subset_1(C_4224,k1_zfmisc_1(A_4222))
      | v1_xboole_0(C_4224)
      | v1_xboole_0(B_4220)
      | v1_xboole_0(A_4222) ) ),
    inference(resolution,[status(thm)],[c_74638,c_60])).

tff(c_77081,plain,(
    ! [A_4222,C_4224,E_4219,D_4221] :
      ( k2_partfun1(k4_subset_1(A_4222,C_4224,'#skF_5'),'#skF_3',k1_tmap_1(A_4222,'#skF_3',C_4224,'#skF_5',E_4219,'#skF_5'),D_4221) = k7_relat_1(k1_tmap_1(A_4222,'#skF_3',C_4224,'#skF_5',E_4219,'#skF_5'),D_4221)
      | ~ v1_funct_1(k1_tmap_1(A_4222,'#skF_3',C_4224,'#skF_5',E_4219,'#skF_5'))
      | ~ v1_funct_2('#skF_5','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_4219,k1_zfmisc_1(k2_zfmisc_1(C_4224,'#skF_3')))
      | ~ v1_funct_2(E_4219,C_4224,'#skF_3')
      | ~ v1_funct_1(E_4219)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4222))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_4224,k1_zfmisc_1(A_4222))
      | v1_xboole_0(C_4224)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_4222) ) ),
    inference(resolution,[status(thm)],[c_73813,c_77077])).

tff(c_77087,plain,(
    ! [A_4222,C_4224,E_4219,D_4221] :
      ( k2_partfun1(k4_subset_1(A_4222,C_4224,'#skF_5'),'#skF_3',k1_tmap_1(A_4222,'#skF_3',C_4224,'#skF_5',E_4219,'#skF_5'),D_4221) = k7_relat_1(k1_tmap_1(A_4222,'#skF_3',C_4224,'#skF_5',E_4219,'#skF_5'),D_4221)
      | ~ v1_funct_1(k1_tmap_1(A_4222,'#skF_3',C_4224,'#skF_5',E_4219,'#skF_5'))
      | ~ m1_subset_1(E_4219,k1_zfmisc_1(k2_zfmisc_1(C_4224,'#skF_3')))
      | ~ v1_funct_2(E_4219,C_4224,'#skF_3')
      | ~ v1_funct_1(E_4219)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4222))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_4224,k1_zfmisc_1(A_4222))
      | v1_xboole_0(C_4224)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_4222) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73815,c_73814,c_77081])).

tff(c_78416,plain,(
    ! [A_4336,C_4337,E_4338,D_4339] :
      ( k2_partfun1(k4_subset_1(A_4336,C_4337,'#skF_5'),'#skF_3',k1_tmap_1(A_4336,'#skF_3',C_4337,'#skF_5',E_4338,'#skF_5'),D_4339) = k7_relat_1(k1_tmap_1(A_4336,'#skF_3',C_4337,'#skF_5',E_4338,'#skF_5'),D_4339)
      | ~ v1_funct_1(k1_tmap_1(A_4336,'#skF_3',C_4337,'#skF_5',E_4338,'#skF_5'))
      | ~ m1_subset_1(E_4338,k1_zfmisc_1(k2_zfmisc_1(C_4337,'#skF_3')))
      | ~ v1_funct_2(E_4338,C_4337,'#skF_3')
      | ~ v1_funct_1(E_4338)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4336))
      | ~ m1_subset_1(C_4337,k1_zfmisc_1(A_4336))
      | v1_xboole_0(C_4337)
      | v1_xboole_0(A_4336) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_92,c_77087])).

tff(c_78423,plain,(
    ! [A_4336,D_4339] :
      ( k2_partfun1(k4_subset_1(A_4336,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_4336,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_5'),D_4339) = k7_relat_1(k1_tmap_1(A_4336,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_5'),D_4339)
      | ~ v1_funct_1(k1_tmap_1(A_4336,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_5'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4336))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4336))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_4336) ) ),
    inference(resolution,[status(thm)],[c_82,c_78416])).

tff(c_78433,plain,(
    ! [A_4336,D_4339] :
      ( k2_partfun1(k4_subset_1(A_4336,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_4336,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_5'),D_4339) = k7_relat_1(k1_tmap_1(A_4336,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_5'),D_4339)
      | ~ v1_funct_1(k1_tmap_1(A_4336,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4336))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4336))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_4336) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_78423])).

tff(c_79831,plain,(
    ! [A_4372,D_4373] :
      ( k2_partfun1(k4_subset_1(A_4372,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_4372,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_5'),D_4373) = k7_relat_1(k1_tmap_1(A_4372,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_5'),D_4373)
      | ~ v1_funct_1(k1_tmap_1(A_4372,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4372))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4372))
      | v1_xboole_0(A_4372) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_78433])).

tff(c_70661,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_7591])).

tff(c_73786,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_5'),'#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73763,c_73763,c_70661])).

tff(c_79837,plain,
    ( k7_relat_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_5'),'#skF_5') != '#skF_5'
    | ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_79831,c_73786])).

tff(c_79846,plain,
    ( k7_relat_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_5'),'#skF_5') != '#skF_5'
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_90,c_75999,c_79837])).

tff(c_79847,plain,(
    k7_relat_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_5'),'#skF_5') != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_79846])).

tff(c_76002,plain,(
    ! [A_4161,B_4160,D_4162,F_4164,E_4159,C_4163] :
      ( v1_relat_1(k1_tmap_1(A_4161,B_4160,C_4163,D_4162,E_4159,F_4164))
      | ~ m1_subset_1(F_4164,k1_zfmisc_1(k2_zfmisc_1(D_4162,B_4160)))
      | ~ v1_funct_2(F_4164,D_4162,B_4160)
      | ~ v1_funct_1(F_4164)
      | ~ m1_subset_1(E_4159,k1_zfmisc_1(k2_zfmisc_1(C_4163,B_4160)))
      | ~ v1_funct_2(E_4159,C_4163,B_4160)
      | ~ v1_funct_1(E_4159)
      | ~ m1_subset_1(D_4162,k1_zfmisc_1(A_4161))
      | v1_xboole_0(D_4162)
      | ~ m1_subset_1(C_4163,k1_zfmisc_1(A_4161))
      | v1_xboole_0(C_4163)
      | v1_xboole_0(B_4160)
      | v1_xboole_0(A_4161) ) ),
    inference(resolution,[status(thm)],[c_74638,c_42])).

tff(c_76006,plain,(
    ! [A_4161,C_4163,E_4159] :
      ( v1_relat_1(k1_tmap_1(A_4161,'#skF_3',C_4163,'#skF_5',E_4159,'#skF_5'))
      | ~ v1_funct_2('#skF_5','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_4159,k1_zfmisc_1(k2_zfmisc_1(C_4163,'#skF_3')))
      | ~ v1_funct_2(E_4159,C_4163,'#skF_3')
      | ~ v1_funct_1(E_4159)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4161))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_4163,k1_zfmisc_1(A_4161))
      | v1_xboole_0(C_4163)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_4161) ) ),
    inference(resolution,[status(thm)],[c_73813,c_76002])).

tff(c_76012,plain,(
    ! [A_4161,C_4163,E_4159] :
      ( v1_relat_1(k1_tmap_1(A_4161,'#skF_3',C_4163,'#skF_5',E_4159,'#skF_5'))
      | ~ m1_subset_1(E_4159,k1_zfmisc_1(k2_zfmisc_1(C_4163,'#skF_3')))
      | ~ v1_funct_2(E_4159,C_4163,'#skF_3')
      | ~ v1_funct_1(E_4159)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4161))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_4163,k1_zfmisc_1(A_4161))
      | v1_xboole_0(C_4163)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_4161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73815,c_73814,c_76006])).

tff(c_76604,plain,(
    ! [A_4200,C_4201,E_4202] :
      ( v1_relat_1(k1_tmap_1(A_4200,'#skF_3',C_4201,'#skF_5',E_4202,'#skF_5'))
      | ~ m1_subset_1(E_4202,k1_zfmisc_1(k2_zfmisc_1(C_4201,'#skF_3')))
      | ~ v1_funct_2(E_4202,C_4201,'#skF_3')
      | ~ v1_funct_1(E_4202)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4200))
      | ~ m1_subset_1(C_4201,k1_zfmisc_1(A_4200))
      | v1_xboole_0(C_4201)
      | v1_xboole_0(A_4200) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_92,c_76012])).

tff(c_76611,plain,(
    ! [A_4200] :
      ( v1_relat_1(k1_tmap_1(A_4200,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_5'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4200))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4200))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_4200) ) ),
    inference(resolution,[status(thm)],[c_82,c_76604])).

tff(c_76621,plain,(
    ! [A_4200] :
      ( v1_relat_1(k1_tmap_1(A_4200,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4200))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4200))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_4200) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_76611])).

tff(c_77248,plain,(
    ! [A_4231] :
      ( v1_relat_1(k1_tmap_1(A_4231,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4231))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4231))
      | v1_xboole_0(A_4231) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_76621])).

tff(c_77254,plain,
    ( v1_relat_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_5'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_90,c_77248])).

tff(c_77260,plain,
    ( v1_relat_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_5'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_77254])).

tff(c_77261,plain,(
    v1_relat_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_77260])).

tff(c_70572,plain,(
    ! [A_3] : r1_tarski('#skF_7',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70561,c_6])).

tff(c_73808,plain,(
    ! [A_3] : r1_tarski('#skF_5',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73763,c_70572])).

tff(c_73807,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73763,c_73763,c_70571])).

tff(c_70568,plain,(
    ! [A_36] :
      ( r1_xboole_0('#skF_1'(A_36),A_36)
      | A_36 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70561,c_48])).

tff(c_73801,plain,(
    ! [A_36] :
      ( r1_xboole_0('#skF_1'(A_36),A_36)
      | A_36 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73763,c_70568])).

tff(c_72638,plain,(
    ! [A_22,B_24] :
      ( k7_relat_1(A_22,B_24) = '#skF_7'
      | ~ r1_xboole_0(B_24,k1_relat_1(A_22))
      | ~ v1_relat_1(A_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70561,c_24])).

tff(c_74749,plain,(
    ! [A_4080,B_4081] :
      ( k7_relat_1(A_4080,B_4081) = '#skF_5'
      | ~ r1_xboole_0(B_4081,k1_relat_1(A_4080))
      | ~ v1_relat_1(A_4080) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73763,c_72638])).

tff(c_74781,plain,(
    ! [A_4080] :
      ( k7_relat_1(A_4080,'#skF_1'(k1_relat_1(A_4080))) = '#skF_5'
      | ~ v1_relat_1(A_4080)
      | k1_relat_1(A_4080) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_73801,c_74749])).

tff(c_73803,plain,(
    k9_relat_1('#skF_5','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73763,c_73763,c_73763,c_70619])).

tff(c_16,plain,(
    ! [A_14] :
      ( k9_relat_1(A_14,k1_relat_1(A_14)) = k2_relat_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_72467,plain,(
    ! [B_16,A_15] :
      ( r1_xboole_0(k1_relat_1(B_16),A_15)
      | k9_relat_1(B_16,A_15) != '#skF_7'
      | ~ v1_relat_1(B_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70561,c_20])).

tff(c_72515,plain,(
    ! [B_3893,A_3894] :
      ( k7_relat_1(B_3893,A_3894) = '#skF_7'
      | ~ r1_xboole_0(k1_relat_1(B_3893),A_3894)
      | ~ v1_relat_1(B_3893) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70561,c_34])).

tff(c_72529,plain,(
    ! [B_16,A_15] :
      ( k7_relat_1(B_16,A_15) = '#skF_7'
      | k9_relat_1(B_16,A_15) != '#skF_7'
      | ~ v1_relat_1(B_16) ) ),
    inference(resolution,[status(thm)],[c_72467,c_72515])).

tff(c_75470,plain,(
    ! [B_4128,A_4129] :
      ( k7_relat_1(B_4128,A_4129) = '#skF_5'
      | k9_relat_1(B_4128,A_4129) != '#skF_5'
      | ~ v1_relat_1(B_4128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73763,c_73763,c_72529])).

tff(c_76623,plain,(
    ! [A_4203] :
      ( k7_relat_1(A_4203,k1_relat_1(A_4203)) = '#skF_5'
      | k2_relat_1(A_4203) != '#skF_5'
      | ~ v1_relat_1(A_4203)
      | ~ v1_relat_1(A_4203) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_75470])).

tff(c_73810,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73763,c_70561])).

tff(c_7598,plain,(
    ! [A_736] :
      ( k2_relat_1(A_736) != k1_xboole_0
      | k1_xboole_0 = A_736
      | ~ v1_relat_1(A_736) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_7602,plain,(
    ! [A_12,B_13] :
      ( k2_relat_1(k7_relat_1(A_12,B_13)) != k1_xboole_0
      | k7_relat_1(A_12,B_13) = k1_xboole_0
      | ~ v1_relat_1(A_12) ) ),
    inference(resolution,[status(thm)],[c_14,c_7598])).

tff(c_75541,plain,(
    ! [A_12,B_13] :
      ( k2_relat_1(k7_relat_1(A_12,B_13)) != '#skF_5'
      | k7_relat_1(A_12,B_13) = '#skF_5'
      | ~ v1_relat_1(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73810,c_73810,c_7602])).

tff(c_76655,plain,(
    ! [A_4203] :
      ( k2_relat_1('#skF_5') != '#skF_5'
      | k7_relat_1(A_4203,k1_relat_1(A_4203)) = '#skF_5'
      | ~ v1_relat_1(A_4203)
      | k2_relat_1(A_4203) != '#skF_5'
      | ~ v1_relat_1(A_4203)
      | ~ v1_relat_1(A_4203) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76623,c_75541])).

tff(c_76798,plain,(
    ! [A_4204] :
      ( k7_relat_1(A_4204,k1_relat_1(A_4204)) = '#skF_5'
      | k2_relat_1(A_4204) != '#skF_5'
      | ~ v1_relat_1(A_4204) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73807,c_76655])).

tff(c_78019,plain,(
    ! [A_4320,B_4321] :
      ( k9_relat_1(A_4320,B_4321) = k9_relat_1('#skF_5',B_4321)
      | ~ r1_tarski(B_4321,k1_relat_1(A_4320))
      | ~ v1_relat_1(A_4320)
      | k2_relat_1(A_4320) != '#skF_5'
      | ~ v1_relat_1(A_4320) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76798,c_22])).

tff(c_78026,plain,(
    ! [A_4320] :
      ( k9_relat_1(A_4320,'#skF_5') = k9_relat_1('#skF_5','#skF_5')
      | k2_relat_1(A_4320) != '#skF_5'
      | ~ v1_relat_1(A_4320) ) ),
    inference(resolution,[status(thm)],[c_73808,c_78019])).

tff(c_78050,plain,(
    ! [A_4324] :
      ( k9_relat_1(A_4324,'#skF_5') = '#skF_5'
      | k2_relat_1(A_4324) != '#skF_5'
      | ~ v1_relat_1(A_4324) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73803,c_78026])).

tff(c_78086,plain,(
    ! [A_4325,B_4326] :
      ( k9_relat_1(k7_relat_1(A_4325,B_4326),'#skF_5') = '#skF_5'
      | k2_relat_1(k7_relat_1(A_4325,B_4326)) != '#skF_5'
      | ~ v1_relat_1(A_4325) ) ),
    inference(resolution,[status(thm)],[c_14,c_78050])).

tff(c_78097,plain,(
    ! [A_4325,B_4326] :
      ( k9_relat_1(A_4325,'#skF_5') = '#skF_5'
      | ~ r1_tarski('#skF_5',B_4326)
      | ~ v1_relat_1(A_4325)
      | k2_relat_1(k7_relat_1(A_4325,B_4326)) != '#skF_5'
      | ~ v1_relat_1(A_4325) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78086,c_22])).

tff(c_78186,plain,(
    ! [A_4327,B_4328] :
      ( k9_relat_1(A_4327,'#skF_5') = '#skF_5'
      | k2_relat_1(k7_relat_1(A_4327,B_4328)) != '#skF_5'
      | ~ v1_relat_1(A_4327) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73808,c_78097])).

tff(c_78204,plain,(
    ! [A_4080] :
      ( k9_relat_1(A_4080,'#skF_5') = '#skF_5'
      | k2_relat_1('#skF_5') != '#skF_5'
      | ~ v1_relat_1(A_4080)
      | ~ v1_relat_1(A_4080)
      | k1_relat_1(A_4080) = '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74781,c_78186])).

tff(c_78257,plain,(
    ! [A_4329] :
      ( k9_relat_1(A_4329,'#skF_5') = '#skF_5'
      | ~ v1_relat_1(A_4329)
      | k1_relat_1(A_4329) = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73807,c_78204])).

tff(c_78435,plain,(
    ! [A_4340,B_4341] :
      ( k9_relat_1(k7_relat_1(A_4340,B_4341),'#skF_5') = '#skF_5'
      | k1_relat_1(k7_relat_1(A_4340,B_4341)) = '#skF_5'
      | ~ v1_relat_1(A_4340) ) ),
    inference(resolution,[status(thm)],[c_14,c_78257])).

tff(c_78449,plain,(
    ! [A_4340,B_4341] :
      ( k9_relat_1(A_4340,'#skF_5') = '#skF_5'
      | ~ r1_tarski('#skF_5',B_4341)
      | ~ v1_relat_1(A_4340)
      | k1_relat_1(k7_relat_1(A_4340,B_4341)) = '#skF_5'
      | ~ v1_relat_1(A_4340) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78435,c_22])).

tff(c_78553,plain,(
    ! [A_4342,B_4343] :
      ( k9_relat_1(A_4342,'#skF_5') = '#skF_5'
      | k1_relat_1(k7_relat_1(A_4342,B_4343)) = '#skF_5'
      | ~ v1_relat_1(A_4342) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73808,c_78449])).

tff(c_7593,plain,(
    ! [A_735] :
      ( k1_relat_1(A_735) != k1_xboole_0
      | k1_xboole_0 = A_735
      | ~ v1_relat_1(A_735) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_7597,plain,(
    ! [A_12,B_13] :
      ( k1_relat_1(k7_relat_1(A_12,B_13)) != k1_xboole_0
      | k7_relat_1(A_12,B_13) = k1_xboole_0
      | ~ v1_relat_1(A_12) ) ),
    inference(resolution,[status(thm)],[c_14,c_7593])).

tff(c_75413,plain,(
    ! [A_12,B_13] :
      ( k1_relat_1(k7_relat_1(A_12,B_13)) != '#skF_5'
      | k7_relat_1(A_12,B_13) = '#skF_5'
      | ~ v1_relat_1(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73810,c_73810,c_7597])).

tff(c_78787,plain,(
    ! [A_4344,B_4345] :
      ( k7_relat_1(A_4344,B_4345) = '#skF_5'
      | k9_relat_1(A_4344,'#skF_5') = '#skF_5'
      | ~ v1_relat_1(A_4344) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78553,c_75413])).

tff(c_78832,plain,(
    ! [A_4352,B_4353,B_4354] :
      ( k7_relat_1(k7_relat_1(A_4352,B_4353),B_4354) = '#skF_5'
      | k9_relat_1(k7_relat_1(A_4352,B_4353),'#skF_5') = '#skF_5'
      | ~ v1_relat_1(A_4352) ) ),
    inference(resolution,[status(thm)],[c_14,c_78787])).

tff(c_78155,plain,(
    ! [A_4325,B_4326] :
      ( k9_relat_1(A_4325,'#skF_5') = '#skF_5'
      | k2_relat_1(k7_relat_1(A_4325,B_4326)) != '#skF_5'
      | ~ v1_relat_1(A_4325) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73808,c_78097])).

tff(c_78850,plain,(
    ! [A_4352,B_4353] :
      ( k9_relat_1(k7_relat_1(A_4352,B_4353),'#skF_5') = '#skF_5'
      | k2_relat_1('#skF_5') != '#skF_5'
      | ~ v1_relat_1(k7_relat_1(A_4352,B_4353))
      | k9_relat_1(k7_relat_1(A_4352,B_4353),'#skF_5') = '#skF_5'
      | ~ v1_relat_1(A_4352) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78832,c_78155])).

tff(c_79180,plain,(
    ! [A_4355,B_4356] :
      ( ~ v1_relat_1(k7_relat_1(A_4355,B_4356))
      | k9_relat_1(k7_relat_1(A_4355,B_4356),'#skF_5') = '#skF_5'
      | ~ v1_relat_1(A_4355) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73807,c_78850])).

tff(c_79270,plain,(
    ! [A_4357,B_4358] :
      ( k9_relat_1(k7_relat_1(A_4357,B_4358),'#skF_5') = '#skF_5'
      | ~ v1_relat_1(A_4357) ) ),
    inference(resolution,[status(thm)],[c_14,c_79180])).

tff(c_79281,plain,(
    ! [A_4357,B_4358] :
      ( k9_relat_1(A_4357,'#skF_5') = '#skF_5'
      | ~ r1_tarski('#skF_5',B_4358)
      | ~ v1_relat_1(A_4357)
      | ~ v1_relat_1(A_4357) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79270,c_22])).

tff(c_79395,plain,(
    ! [A_4361] :
      ( k9_relat_1(A_4361,'#skF_5') = '#skF_5'
      | ~ v1_relat_1(A_4361) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73808,c_79281])).

tff(c_79420,plain,(
    k9_relat_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_5'),'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_77261,c_79395])).

tff(c_73765,plain,(
    ! [B_16,A_15] :
      ( k7_relat_1(B_16,A_15) = '#skF_5'
      | k9_relat_1(B_16,A_15) != '#skF_5'
      | ~ v1_relat_1(B_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73763,c_73763,c_72529])).

tff(c_79824,plain,
    ( k7_relat_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_5'),'#skF_5') = '#skF_5'
    | ~ v1_relat_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_79420,c_73765])).

tff(c_79829,plain,(
    k7_relat_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_5'),'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77261,c_79824])).

tff(c_79893,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79847,c_79829])).

tff(c_79894,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_7591])).

tff(c_81891,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_5'),'#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81876,c_79894])).

tff(c_89440,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_5'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_89431,c_81891])).

tff(c_89451,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_90,c_82820,c_82840,c_81887,c_82840,c_81566,c_81566,c_83932,c_89440])).

tff(c_89453,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_89451])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:31:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.61/11.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.11/11.35  
% 21.11/11.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.11/11.35  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 21.11/11.35  
% 21.11/11.35  %Foreground sorts:
% 21.11/11.35  
% 21.11/11.35  
% 21.11/11.35  %Background operators:
% 21.11/11.35  
% 21.11/11.35  
% 21.11/11.35  %Foreground operators:
% 21.11/11.35  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 21.11/11.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 21.11/11.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 21.11/11.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 21.11/11.35  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 21.11/11.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 21.11/11.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 21.11/11.35  tff('#skF_7', type, '#skF_7': $i).
% 21.11/11.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 21.11/11.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 21.11/11.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 21.11/11.35  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 21.11/11.35  tff('#skF_5', type, '#skF_5': $i).
% 21.11/11.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 21.11/11.35  tff('#skF_6', type, '#skF_6': $i).
% 21.11/11.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 21.11/11.35  tff('#skF_2', type, '#skF_2': $i).
% 21.11/11.35  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 21.11/11.35  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 21.11/11.35  tff('#skF_3', type, '#skF_3': $i).
% 21.11/11.35  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 21.11/11.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 21.11/11.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 21.11/11.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 21.11/11.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 21.11/11.35  tff('#skF_4', type, '#skF_4': $i).
% 21.11/11.35  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 21.11/11.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 21.11/11.35  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 21.11/11.35  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 21.11/11.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 21.11/11.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 21.11/11.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 21.11/11.35  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 21.11/11.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 21.11/11.35  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 21.11/11.35  
% 21.41/11.42  tff(f_271, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 21.41/11.42  tff(f_99, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 21.41/11.42  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 21.41/11.42  tff(f_229, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 21.41/11.42  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 21.41/11.42  tff(f_141, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 21.41/11.42  tff(f_133, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 21.41/11.42  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 21.41/11.42  tff(f_83, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 21.41/11.42  tff(f_75, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 21.41/11.42  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 21.41/11.42  tff(f_119, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_mcart_1)).
% 21.41/11.42  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 21.41/11.42  tff(f_48, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 21.41/11.42  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 21.41/11.42  tff(f_89, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 21.41/11.42  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 21.41/11.42  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 21.41/11.42  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 21.41/11.42  tff(f_147, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 21.41/11.42  tff(f_195, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 21.41/11.42  tff(c_100, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_271])).
% 21.41/11.42  tff(c_94, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_271])).
% 21.41/11.42  tff(c_90, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_271])).
% 21.41/11.42  tff(c_96, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_271])).
% 21.41/11.42  tff(c_88, plain, (r1_subset_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_271])).
% 21.41/11.42  tff(c_92, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_271])).
% 21.41/11.42  tff(c_40, plain, (![A_28, B_29]: (r1_xboole_0(A_28, B_29) | ~r1_subset_1(A_28, B_29) | v1_xboole_0(B_29) | v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_99])).
% 21.41/11.42  tff(c_98, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_271])).
% 21.41/11.42  tff(c_76, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_271])).
% 21.41/11.42  tff(c_7636, plain, (![C_744, A_745, B_746]: (v1_relat_1(C_744) | ~m1_subset_1(C_744, k1_zfmisc_1(k2_zfmisc_1(A_745, B_746))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 21.41/11.42  tff(c_7643, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_76, c_7636])).
% 21.41/11.42  tff(c_82, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_271])).
% 21.41/11.42  tff(c_7644, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_7636])).
% 21.41/11.42  tff(c_86, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_271])).
% 21.41/11.42  tff(c_84, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_271])).
% 21.41/11.42  tff(c_80, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_271])).
% 21.41/11.42  tff(c_78, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_271])).
% 21.41/11.42  tff(c_70, plain, (![C_177, F_180, A_175, D_178, B_176, E_179]: (v1_funct_2(k1_tmap_1(A_175, B_176, C_177, D_178, E_179, F_180), k4_subset_1(A_175, C_177, D_178), B_176) | ~m1_subset_1(F_180, k1_zfmisc_1(k2_zfmisc_1(D_178, B_176))) | ~v1_funct_2(F_180, D_178, B_176) | ~v1_funct_1(F_180) | ~m1_subset_1(E_179, k1_zfmisc_1(k2_zfmisc_1(C_177, B_176))) | ~v1_funct_2(E_179, C_177, B_176) | ~v1_funct_1(E_179) | ~m1_subset_1(D_178, k1_zfmisc_1(A_175)) | v1_xboole_0(D_178) | ~m1_subset_1(C_177, k1_zfmisc_1(A_175)) | v1_xboole_0(C_177) | v1_xboole_0(B_176) | v1_xboole_0(A_175))), inference(cnfTransformation, [status(thm)], [f_229])).
% 21.41/11.42  tff(c_8069, plain, (![C_796, A_797, B_798]: (v4_relat_1(C_796, A_797) | ~m1_subset_1(C_796, k1_zfmisc_1(k2_zfmisc_1(A_797, B_798))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 21.41/11.42  tff(c_8076, plain, (v4_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_76, c_8069])).
% 21.41/11.42  tff(c_8510, plain, (![B_826, A_827]: (k1_relat_1(B_826)=A_827 | ~v1_partfun1(B_826, A_827) | ~v4_relat_1(B_826, A_827) | ~v1_relat_1(B_826))), inference(cnfTransformation, [status(thm)], [f_141])).
% 21.41/11.42  tff(c_8516, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_8076, c_8510])).
% 21.41/11.42  tff(c_8522, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7643, c_8516])).
% 21.41/11.42  tff(c_9547, plain, (~v1_partfun1('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_8522])).
% 21.41/11.42  tff(c_10032, plain, (![C_936, A_937, B_938]: (v1_partfun1(C_936, A_937) | ~v1_funct_2(C_936, A_937, B_938) | ~v1_funct_1(C_936) | ~m1_subset_1(C_936, k1_zfmisc_1(k2_zfmisc_1(A_937, B_938))) | v1_xboole_0(B_938))), inference(cnfTransformation, [status(thm)], [f_133])).
% 21.41/11.42  tff(c_10035, plain, (v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_76, c_10032])).
% 21.41/11.42  tff(c_10041, plain, (v1_partfun1('#skF_7', '#skF_5') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_10035])).
% 21.41/11.42  tff(c_10043, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_9547, c_10041])).
% 21.41/11.42  tff(c_10044, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitRight, [status(thm)], [c_8522])).
% 21.41/11.42  tff(c_20, plain, (![B_16, A_15]: (r1_xboole_0(k1_relat_1(B_16), A_15) | k9_relat_1(B_16, A_15)!=k1_xboole_0 | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 21.41/11.42  tff(c_10059, plain, (![A_15]: (r1_xboole_0('#skF_5', A_15) | k9_relat_1('#skF_7', A_15)!=k1_xboole_0 | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_10044, c_20])).
% 21.41/11.42  tff(c_10096, plain, (![A_939]: (r1_xboole_0('#skF_5', A_939) | k9_relat_1('#skF_7', A_939)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7643, c_10059])).
% 21.41/11.42  tff(c_32, plain, (![A_25]: (k1_relat_1(A_25)!=k1_xboole_0 | k1_xboole_0=A_25 | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_83])).
% 21.41/11.42  tff(c_7679, plain, (k1_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_7644, c_32])).
% 21.41/11.42  tff(c_7683, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7679])).
% 21.41/11.42  tff(c_26, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 21.41/11.42  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 21.41/11.42  tff(c_7684, plain, (![A_749]: (k9_relat_1(A_749, k1_relat_1(A_749))=k2_relat_1(A_749) | ~v1_relat_1(A_749))), inference(cnfTransformation, [status(thm)], [f_52])).
% 21.41/11.42  tff(c_7693, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_7684])).
% 21.41/11.42  tff(c_7696, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_7693])).
% 21.41/11.42  tff(c_7700, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_7696])).
% 21.41/11.42  tff(c_48, plain, (![A_36]: (r1_xboole_0('#skF_1'(A_36), A_36) | k1_xboole_0=A_36)), inference(cnfTransformation, [status(thm)], [f_119])).
% 21.41/11.42  tff(c_7719, plain, (![A_756, B_757]: (k7_relat_1(A_756, B_757)=k1_xboole_0 | ~r1_xboole_0(B_757, k1_relat_1(A_756)) | ~v1_relat_1(A_756))), inference(cnfTransformation, [status(thm)], [f_72])).
% 21.41/11.42  tff(c_8004, plain, (![A_791]: (k7_relat_1(A_791, '#skF_1'(k1_relat_1(A_791)))=k1_xboole_0 | ~v1_relat_1(A_791) | k1_relat_1(A_791)=k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_7719])).
% 21.41/11.42  tff(c_14, plain, (![A_12, B_13]: (v1_relat_1(k7_relat_1(A_12, B_13)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 21.41/11.42  tff(c_8013, plain, (![A_791]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_791) | ~v1_relat_1(A_791) | k1_relat_1(A_791)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8004, c_14])).
% 21.41/11.42  tff(c_8028, plain, (![A_792]: (~v1_relat_1(A_792) | ~v1_relat_1(A_792) | k1_relat_1(A_792)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_7700, c_8013])).
% 21.41/11.42  tff(c_8030, plain, (~v1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_7644, c_8028])).
% 21.41/11.42  tff(c_8037, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7644, c_8030])).
% 21.41/11.42  tff(c_8039, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7683, c_8037])).
% 21.41/11.42  tff(c_8041, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_7696])).
% 21.41/11.42  tff(c_8078, plain, (![A_799, B_800]: (k7_relat_1(A_799, B_800)=k1_xboole_0 | ~r1_xboole_0(B_800, k1_relat_1(A_799)) | ~v1_relat_1(A_799))), inference(cnfTransformation, [status(thm)], [f_72])).
% 21.41/11.42  tff(c_8089, plain, (![B_800]: (k7_relat_1(k1_xboole_0, B_800)=k1_xboole_0 | ~r1_xboole_0(B_800, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_8078])).
% 21.41/11.42  tff(c_8093, plain, (![B_800]: (k7_relat_1(k1_xboole_0, B_800)=k1_xboole_0 | ~r1_xboole_0(B_800, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8041, c_8089])).
% 21.41/11.42  tff(c_10114, plain, (k7_relat_1(k1_xboole_0, '#skF_5')=k1_xboole_0 | k9_relat_1('#skF_7', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_10096, c_8093])).
% 21.41/11.42  tff(c_11752, plain, (k9_relat_1('#skF_7', k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_10114])).
% 21.41/11.42  tff(c_8040, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_7696])).
% 21.41/11.42  tff(c_6, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 21.41/11.42  tff(c_8077, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_82, c_8069])).
% 21.41/11.42  tff(c_8513, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_8077, c_8510])).
% 21.41/11.42  tff(c_8519, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7644, c_8513])).
% 21.41/11.42  tff(c_8523, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_8519])).
% 21.41/11.42  tff(c_9489, plain, (![C_904, A_905, B_906]: (v1_partfun1(C_904, A_905) | ~v1_funct_2(C_904, A_905, B_906) | ~v1_funct_1(C_904) | ~m1_subset_1(C_904, k1_zfmisc_1(k2_zfmisc_1(A_905, B_906))) | v1_xboole_0(B_906))), inference(cnfTransformation, [status(thm)], [f_133])).
% 21.41/11.42  tff(c_9495, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_82, c_9489])).
% 21.41/11.42  tff(c_9502, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_9495])).
% 21.41/11.42  tff(c_9504, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_8523, c_9502])).
% 21.41/11.42  tff(c_9505, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_8519])).
% 21.41/11.42  tff(c_34, plain, (![B_27, A_26]: (k7_relat_1(B_27, A_26)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_27), A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_89])).
% 21.41/11.42  tff(c_9523, plain, (![A_26]: (k7_relat_1('#skF_6', A_26)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_26) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_9505, c_34])).
% 21.41/11.42  tff(c_10413, plain, (![A_955]: (k7_relat_1('#skF_6', A_955)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_955))), inference(demodulation, [status(thm), theory('equality')], [c_7644, c_9523])).
% 21.41/11.42  tff(c_10420, plain, (![B_29]: (k7_relat_1('#skF_6', B_29)=k1_xboole_0 | ~r1_subset_1('#skF_4', B_29) | v1_xboole_0(B_29) | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_10413])).
% 21.41/11.42  tff(c_10559, plain, (![B_968]: (k7_relat_1('#skF_6', B_968)=k1_xboole_0 | ~r1_subset_1('#skF_4', B_968) | v1_xboole_0(B_968))), inference(negUnitSimplification, [status(thm)], [c_96, c_10420])).
% 21.41/11.42  tff(c_10562, plain, (k7_relat_1('#skF_6', '#skF_5')=k1_xboole_0 | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_88, c_10559])).
% 21.41/11.42  tff(c_10565, plain, (k7_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_92, c_10562])).
% 21.41/11.42  tff(c_36, plain, (![B_27, A_26]: (r1_xboole_0(k1_relat_1(B_27), A_26) | k7_relat_1(B_27, A_26)!=k1_xboole_0 | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_89])).
% 21.41/11.42  tff(c_9511, plain, (![A_26]: (r1_xboole_0('#skF_4', A_26) | k7_relat_1('#skF_6', A_26)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_9505, c_36])).
% 21.41/11.42  tff(c_10430, plain, (![A_956]: (r1_xboole_0('#skF_4', A_956) | k7_relat_1('#skF_6', A_956)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7644, c_9511])).
% 21.41/11.42  tff(c_18, plain, (![B_16, A_15]: (k9_relat_1(B_16, A_15)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_16), A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 21.41/11.42  tff(c_9514, plain, (![A_15]: (k9_relat_1('#skF_6', A_15)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_15) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_9505, c_18])).
% 21.41/11.42  tff(c_9535, plain, (![A_15]: (k9_relat_1('#skF_6', A_15)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_15))), inference(demodulation, [status(thm), theory('equality')], [c_7644, c_9514])).
% 21.41/11.42  tff(c_10460, plain, (![A_956]: (k9_relat_1('#skF_6', A_956)=k1_xboole_0 | k7_relat_1('#skF_6', A_956)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10430, c_9535])).
% 21.41/11.42  tff(c_9520, plain, (![A_15]: (r1_xboole_0('#skF_4', A_15) | k9_relat_1('#skF_6', A_15)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_9505, c_20])).
% 21.41/11.42  tff(c_9539, plain, (![A_15]: (r1_xboole_0('#skF_4', A_15) | k9_relat_1('#skF_6', A_15)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7644, c_9520])).
% 21.41/11.42  tff(c_24, plain, (![A_22, B_24]: (k7_relat_1(A_22, B_24)=k1_xboole_0 | ~r1_xboole_0(B_24, k1_relat_1(A_22)) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_72])).
% 21.41/11.42  tff(c_10065, plain, (![B_24]: (k7_relat_1('#skF_7', B_24)=k1_xboole_0 | ~r1_xboole_0(B_24, '#skF_5') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_10044, c_24])).
% 21.41/11.42  tff(c_10196, plain, (![B_948]: (k7_relat_1('#skF_7', B_948)=k1_xboole_0 | ~r1_xboole_0(B_948, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_7643, c_10065])).
% 21.41/11.42  tff(c_10233, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0 | k9_relat_1('#skF_6', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_9539, c_10196])).
% 21.41/11.42  tff(c_10626, plain, (k9_relat_1('#skF_6', '#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_10233])).
% 21.41/11.42  tff(c_10630, plain, (k7_relat_1('#skF_6', '#skF_5')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_10460, c_10626])).
% 21.41/11.42  tff(c_10634, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10565, c_10630])).
% 21.41/11.42  tff(c_10635, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_10233])).
% 21.41/11.42  tff(c_10050, plain, (![A_26]: (r1_xboole_0('#skF_5', A_26) | k7_relat_1('#skF_7', A_26)!=k1_xboole_0 | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_10044, c_36])).
% 21.41/11.42  tff(c_10378, plain, (![A_954]: (r1_xboole_0('#skF_5', A_954) | k7_relat_1('#skF_7', A_954)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7643, c_10050])).
% 21.41/11.42  tff(c_10053, plain, (![A_15]: (k9_relat_1('#skF_7', A_15)=k1_xboole_0 | ~r1_xboole_0('#skF_5', A_15) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_10044, c_18])).
% 21.41/11.42  tff(c_10074, plain, (![A_15]: (k9_relat_1('#skF_7', A_15)=k1_xboole_0 | ~r1_xboole_0('#skF_5', A_15))), inference(demodulation, [status(thm), theory('equality')], [c_7643, c_10053])).
% 21.41/11.42  tff(c_10744, plain, (![A_984]: (k9_relat_1('#skF_7', A_984)=k1_xboole_0 | k7_relat_1('#skF_7', A_984)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10378, c_10074])).
% 21.41/11.42  tff(c_10078, plain, (![A_15]: (r1_xboole_0('#skF_5', A_15) | k9_relat_1('#skF_7', A_15)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7643, c_10059])).
% 21.41/11.42  tff(c_9526, plain, (![B_24]: (k7_relat_1('#skF_6', B_24)=k1_xboole_0 | ~r1_xboole_0(B_24, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_9505, c_24])).
% 21.41/11.42  tff(c_10256, plain, (![B_949]: (k7_relat_1('#skF_6', B_949)=k1_xboole_0 | ~r1_xboole_0(B_949, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7644, c_9526])).
% 21.41/11.42  tff(c_10295, plain, (k7_relat_1('#skF_6', '#skF_5')=k1_xboole_0 | k9_relat_1('#skF_7', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_10078, c_10256])).
% 21.41/11.42  tff(c_10558, plain, (k9_relat_1('#skF_7', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_10295])).
% 21.41/11.42  tff(c_10750, plain, (k7_relat_1('#skF_7', '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_10744, c_10558])).
% 21.41/11.42  tff(c_10778, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10635, c_10750])).
% 21.41/11.42  tff(c_10780, plain, (k9_relat_1('#skF_7', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_10295])).
% 21.41/11.42  tff(c_10062, plain, (![A_26]: (k7_relat_1('#skF_7', A_26)=k1_xboole_0 | ~r1_xboole_0('#skF_5', A_26) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_10044, c_34])).
% 21.41/11.42  tff(c_10478, plain, (![A_958]: (k7_relat_1('#skF_7', A_958)=k1_xboole_0 | ~r1_xboole_0('#skF_5', A_958))), inference(demodulation, [status(thm), theory('equality')], [c_7643, c_10062])).
% 21.41/11.42  tff(c_10494, plain, (![A_15]: (k7_relat_1('#skF_7', A_15)=k1_xboole_0 | k9_relat_1('#skF_7', A_15)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10078, c_10478])).
% 21.41/11.42  tff(c_10804, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_10780, c_10494])).
% 21.41/11.42  tff(c_22, plain, (![A_17, C_21, B_20]: (k9_relat_1(k7_relat_1(A_17, C_21), B_20)=k9_relat_1(A_17, B_20) | ~r1_tarski(B_20, C_21) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 21.41/11.42  tff(c_10810, plain, (![B_20]: (k9_relat_1(k1_xboole_0, B_20)=k9_relat_1('#skF_7', B_20) | ~r1_tarski(B_20, '#skF_4') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_10804, c_22])).
% 21.41/11.42  tff(c_12061, plain, (![B_1074]: (k9_relat_1(k1_xboole_0, B_1074)=k9_relat_1('#skF_7', B_1074) | ~r1_tarski(B_1074, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7643, c_10810])).
% 21.41/11.42  tff(c_12065, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k9_relat_1('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_12061])).
% 21.41/11.42  tff(c_12067, plain, (k9_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8040, c_12065])).
% 21.41/11.42  tff(c_12069, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11752, c_12067])).
% 21.41/11.42  tff(c_12071, plain, (k9_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_10114])).
% 21.41/11.42  tff(c_12130, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_12071, c_10494])).
% 21.41/11.42  tff(c_8386, plain, (![B_821, A_822]: (r1_xboole_0(k1_relat_1(B_821), A_822) | k7_relat_1(B_821, A_822)!=k1_xboole_0 | ~v1_relat_1(B_821))), inference(cnfTransformation, [status(thm)], [f_89])).
% 21.41/11.42  tff(c_8409, plain, (![A_822]: (r1_xboole_0(k1_xboole_0, A_822) | k7_relat_1(k1_xboole_0, A_822)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_8386])).
% 21.41/11.42  tff(c_8418, plain, (![A_823]: (r1_xboole_0(k1_xboole_0, A_823) | k7_relat_1(k1_xboole_0, A_823)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8041, c_8409])).
% 21.41/11.42  tff(c_8252, plain, (![B_812, A_813]: (k9_relat_1(B_812, A_813)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_812), A_813) | ~v1_relat_1(B_812))), inference(cnfTransformation, [status(thm)], [f_58])).
% 21.41/11.42  tff(c_8262, plain, (![A_813]: (k9_relat_1(k1_xboole_0, A_813)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_813) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_8252])).
% 21.41/11.42  tff(c_8266, plain, (![A_813]: (k9_relat_1(k1_xboole_0, A_813)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_813))), inference(demodulation, [status(thm), theory('equality')], [c_8041, c_8262])).
% 21.41/11.42  tff(c_8440, plain, (![A_823]: (k9_relat_1(k1_xboole_0, A_823)=k1_xboole_0 | k7_relat_1(k1_xboole_0, A_823)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8418, c_8266])).
% 21.41/11.42  tff(c_10466, plain, (k7_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0 | k7_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_10430, c_8093])).
% 21.41/11.42  tff(c_11381, plain, (k7_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_10466])).
% 21.41/11.42  tff(c_8137, plain, (![B_806, A_807]: (r1_xboole_0(k1_relat_1(B_806), A_807) | k9_relat_1(B_806, A_807)!=k1_xboole_0 | ~v1_relat_1(B_806))), inference(cnfTransformation, [status(thm)], [f_58])).
% 21.41/11.42  tff(c_8154, plain, (![A_807]: (r1_xboole_0(k1_xboole_0, A_807) | k9_relat_1(k1_xboole_0, A_807)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_8137])).
% 21.41/11.42  tff(c_8160, plain, (![A_807]: (r1_xboole_0(k1_xboole_0, A_807) | k9_relat_1(k1_xboole_0, A_807)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8041, c_8154])).
% 21.41/11.42  tff(c_10301, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0 | k9_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_8160, c_10256])).
% 21.41/11.42  tff(c_11416, plain, (k9_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_11381, c_10301])).
% 21.41/11.42  tff(c_11423, plain, (k7_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_8440, c_11416])).
% 21.41/11.42  tff(c_10166, plain, (![A_946]: (r1_xboole_0('#skF_4', A_946) | k9_relat_1('#skF_6', A_946)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7644, c_9520])).
% 21.41/11.42  tff(c_10184, plain, (k7_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0 | k9_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_10166, c_8093])).
% 21.41/11.42  tff(c_11433, plain, (k9_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_11423, c_10184])).
% 21.41/11.42  tff(c_10779, plain, (k7_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_10295])).
% 21.41/11.42  tff(c_10784, plain, (![B_20]: (k9_relat_1(k1_xboole_0, B_20)=k9_relat_1('#skF_6', B_20) | ~r1_tarski(B_20, '#skF_5') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_10779, c_22])).
% 21.41/11.42  tff(c_11654, plain, (![B_1049]: (k9_relat_1(k1_xboole_0, B_1049)=k9_relat_1('#skF_6', B_1049) | ~r1_tarski(B_1049, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_7644, c_10784])).
% 21.41/11.42  tff(c_11658, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k9_relat_1('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_11654])).
% 21.41/11.42  tff(c_11660, plain, (k9_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8040, c_11658])).
% 21.41/11.42  tff(c_11662, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11433, c_11660])).
% 21.41/11.42  tff(c_11664, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_10466])).
% 21.41/11.42  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 21.41/11.42  tff(c_11344, plain, (![A_1027]: (k3_xboole_0('#skF_4', A_1027)=k1_xboole_0 | k7_relat_1('#skF_6', A_1027)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10430, c_2])).
% 21.41/11.42  tff(c_11359, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_10779, c_11344])).
% 21.41/11.42  tff(c_10134, plain, (![A_941, B_942, C_943]: (k9_subset_1(A_941, B_942, C_943)=k3_xboole_0(B_942, C_943) | ~m1_subset_1(C_943, k1_zfmisc_1(A_941)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 21.41/11.42  tff(c_10146, plain, (![B_942]: (k9_subset_1('#skF_2', B_942, '#skF_5')=k3_xboole_0(B_942, '#skF_5'))), inference(resolution, [status(thm)], [c_90, c_10134])).
% 21.41/11.42  tff(c_10929, plain, (![F_994, D_992, B_996, C_991, E_995, A_993]: (v1_funct_1(k1_tmap_1(A_993, B_996, C_991, D_992, E_995, F_994)) | ~m1_subset_1(F_994, k1_zfmisc_1(k2_zfmisc_1(D_992, B_996))) | ~v1_funct_2(F_994, D_992, B_996) | ~v1_funct_1(F_994) | ~m1_subset_1(E_995, k1_zfmisc_1(k2_zfmisc_1(C_991, B_996))) | ~v1_funct_2(E_995, C_991, B_996) | ~v1_funct_1(E_995) | ~m1_subset_1(D_992, k1_zfmisc_1(A_993)) | v1_xboole_0(D_992) | ~m1_subset_1(C_991, k1_zfmisc_1(A_993)) | v1_xboole_0(C_991) | v1_xboole_0(B_996) | v1_xboole_0(A_993))), inference(cnfTransformation, [status(thm)], [f_229])).
% 21.41/11.42  tff(c_10931, plain, (![A_993, C_991, E_995]: (v1_funct_1(k1_tmap_1(A_993, '#skF_3', C_991, '#skF_5', E_995, '#skF_7')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_995, k1_zfmisc_1(k2_zfmisc_1(C_991, '#skF_3'))) | ~v1_funct_2(E_995, C_991, '#skF_3') | ~v1_funct_1(E_995) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_993)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_991, k1_zfmisc_1(A_993)) | v1_xboole_0(C_991) | v1_xboole_0('#skF_3') | v1_xboole_0(A_993))), inference(resolution, [status(thm)], [c_76, c_10929])).
% 21.41/11.42  tff(c_10936, plain, (![A_993, C_991, E_995]: (v1_funct_1(k1_tmap_1(A_993, '#skF_3', C_991, '#skF_5', E_995, '#skF_7')) | ~m1_subset_1(E_995, k1_zfmisc_1(k2_zfmisc_1(C_991, '#skF_3'))) | ~v1_funct_2(E_995, C_991, '#skF_3') | ~v1_funct_1(E_995) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_993)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_991, k1_zfmisc_1(A_993)) | v1_xboole_0(C_991) | v1_xboole_0('#skF_3') | v1_xboole_0(A_993))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_10931])).
% 21.41/11.42  tff(c_12490, plain, (![A_1096, C_1097, E_1098]: (v1_funct_1(k1_tmap_1(A_1096, '#skF_3', C_1097, '#skF_5', E_1098, '#skF_7')) | ~m1_subset_1(E_1098, k1_zfmisc_1(k2_zfmisc_1(C_1097, '#skF_3'))) | ~v1_funct_2(E_1098, C_1097, '#skF_3') | ~v1_funct_1(E_1098) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1096)) | ~m1_subset_1(C_1097, k1_zfmisc_1(A_1096)) | v1_xboole_0(C_1097) | v1_xboole_0(A_1096))), inference(negUnitSimplification, [status(thm)], [c_98, c_92, c_10936])).
% 21.41/11.42  tff(c_12497, plain, (![A_1096]: (v1_funct_1(k1_tmap_1(A_1096, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1096)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1096)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1096))), inference(resolution, [status(thm)], [c_82, c_12490])).
% 21.41/11.42  tff(c_12507, plain, (![A_1096]: (v1_funct_1(k1_tmap_1(A_1096, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1096)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1096)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1096))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_12497])).
% 21.41/11.42  tff(c_13082, plain, (![A_1121]: (v1_funct_1(k1_tmap_1(A_1121, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1121)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1121)) | v1_xboole_0(A_1121))), inference(negUnitSimplification, [status(thm)], [c_96, c_12507])).
% 21.41/11.42  tff(c_13085, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_90, c_13082])).
% 21.41/11.42  tff(c_13088, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_13085])).
% 21.41/11.42  tff(c_13089, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_100, c_13088])).
% 21.41/11.42  tff(c_10529, plain, (![A_962, B_963, C_964, D_965]: (k2_partfun1(A_962, B_963, C_964, D_965)=k7_relat_1(C_964, D_965) | ~m1_subset_1(C_964, k1_zfmisc_1(k2_zfmisc_1(A_962, B_963))) | ~v1_funct_1(C_964))), inference(cnfTransformation, [status(thm)], [f_147])).
% 21.41/11.42  tff(c_10533, plain, (![D_965]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_965)=k7_relat_1('#skF_6', D_965) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_82, c_10529])).
% 21.41/11.42  tff(c_10539, plain, (![D_965]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_965)=k7_relat_1('#skF_6', D_965))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_10533])).
% 21.41/11.42  tff(c_10531, plain, (![D_965]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_965)=k7_relat_1('#skF_7', D_965) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_76, c_10529])).
% 21.41/11.42  tff(c_10536, plain, (![D_965]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_965)=k7_relat_1('#skF_7', D_965))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_10531])).
% 21.41/11.42  tff(c_68, plain, (![C_177, F_180, A_175, D_178, B_176, E_179]: (m1_subset_1(k1_tmap_1(A_175, B_176, C_177, D_178, E_179, F_180), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_175, C_177, D_178), B_176))) | ~m1_subset_1(F_180, k1_zfmisc_1(k2_zfmisc_1(D_178, B_176))) | ~v1_funct_2(F_180, D_178, B_176) | ~v1_funct_1(F_180) | ~m1_subset_1(E_179, k1_zfmisc_1(k2_zfmisc_1(C_177, B_176))) | ~v1_funct_2(E_179, C_177, B_176) | ~v1_funct_1(E_179) | ~m1_subset_1(D_178, k1_zfmisc_1(A_175)) | v1_xboole_0(D_178) | ~m1_subset_1(C_177, k1_zfmisc_1(A_175)) | v1_xboole_0(C_177) | v1_xboole_0(B_176) | v1_xboole_0(A_175))), inference(cnfTransformation, [status(thm)], [f_229])).
% 21.41/11.42  tff(c_11340, plain, (![D_1024, F_1025, B_1026, C_1023, A_1022, E_1021]: (k2_partfun1(k4_subset_1(A_1022, C_1023, D_1024), B_1026, k1_tmap_1(A_1022, B_1026, C_1023, D_1024, E_1021, F_1025), D_1024)=F_1025 | ~m1_subset_1(k1_tmap_1(A_1022, B_1026, C_1023, D_1024, E_1021, F_1025), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1022, C_1023, D_1024), B_1026))) | ~v1_funct_2(k1_tmap_1(A_1022, B_1026, C_1023, D_1024, E_1021, F_1025), k4_subset_1(A_1022, C_1023, D_1024), B_1026) | ~v1_funct_1(k1_tmap_1(A_1022, B_1026, C_1023, D_1024, E_1021, F_1025)) | k2_partfun1(D_1024, B_1026, F_1025, k9_subset_1(A_1022, C_1023, D_1024))!=k2_partfun1(C_1023, B_1026, E_1021, k9_subset_1(A_1022, C_1023, D_1024)) | ~m1_subset_1(F_1025, k1_zfmisc_1(k2_zfmisc_1(D_1024, B_1026))) | ~v1_funct_2(F_1025, D_1024, B_1026) | ~v1_funct_1(F_1025) | ~m1_subset_1(E_1021, k1_zfmisc_1(k2_zfmisc_1(C_1023, B_1026))) | ~v1_funct_2(E_1021, C_1023, B_1026) | ~v1_funct_1(E_1021) | ~m1_subset_1(D_1024, k1_zfmisc_1(A_1022)) | v1_xboole_0(D_1024) | ~m1_subset_1(C_1023, k1_zfmisc_1(A_1022)) | v1_xboole_0(C_1023) | v1_xboole_0(B_1026) | v1_xboole_0(A_1022))), inference(cnfTransformation, [status(thm)], [f_195])).
% 21.41/11.42  tff(c_21002, plain, (![D_1349, F_1351, E_1352, A_1350, C_1348, B_1353]: (k2_partfun1(k4_subset_1(A_1350, C_1348, D_1349), B_1353, k1_tmap_1(A_1350, B_1353, C_1348, D_1349, E_1352, F_1351), D_1349)=F_1351 | ~v1_funct_2(k1_tmap_1(A_1350, B_1353, C_1348, D_1349, E_1352, F_1351), k4_subset_1(A_1350, C_1348, D_1349), B_1353) | ~v1_funct_1(k1_tmap_1(A_1350, B_1353, C_1348, D_1349, E_1352, F_1351)) | k2_partfun1(D_1349, B_1353, F_1351, k9_subset_1(A_1350, C_1348, D_1349))!=k2_partfun1(C_1348, B_1353, E_1352, k9_subset_1(A_1350, C_1348, D_1349)) | ~m1_subset_1(F_1351, k1_zfmisc_1(k2_zfmisc_1(D_1349, B_1353))) | ~v1_funct_2(F_1351, D_1349, B_1353) | ~v1_funct_1(F_1351) | ~m1_subset_1(E_1352, k1_zfmisc_1(k2_zfmisc_1(C_1348, B_1353))) | ~v1_funct_2(E_1352, C_1348, B_1353) | ~v1_funct_1(E_1352) | ~m1_subset_1(D_1349, k1_zfmisc_1(A_1350)) | v1_xboole_0(D_1349) | ~m1_subset_1(C_1348, k1_zfmisc_1(A_1350)) | v1_xboole_0(C_1348) | v1_xboole_0(B_1353) | v1_xboole_0(A_1350))), inference(resolution, [status(thm)], [c_68, c_11340])).
% 21.41/11.42  tff(c_25044, plain, (![F_1474, A_1473, C_1471, E_1475, D_1472, B_1476]: (k2_partfun1(k4_subset_1(A_1473, C_1471, D_1472), B_1476, k1_tmap_1(A_1473, B_1476, C_1471, D_1472, E_1475, F_1474), D_1472)=F_1474 | ~v1_funct_1(k1_tmap_1(A_1473, B_1476, C_1471, D_1472, E_1475, F_1474)) | k2_partfun1(D_1472, B_1476, F_1474, k9_subset_1(A_1473, C_1471, D_1472))!=k2_partfun1(C_1471, B_1476, E_1475, k9_subset_1(A_1473, C_1471, D_1472)) | ~m1_subset_1(F_1474, k1_zfmisc_1(k2_zfmisc_1(D_1472, B_1476))) | ~v1_funct_2(F_1474, D_1472, B_1476) | ~v1_funct_1(F_1474) | ~m1_subset_1(E_1475, k1_zfmisc_1(k2_zfmisc_1(C_1471, B_1476))) | ~v1_funct_2(E_1475, C_1471, B_1476) | ~v1_funct_1(E_1475) | ~m1_subset_1(D_1472, k1_zfmisc_1(A_1473)) | v1_xboole_0(D_1472) | ~m1_subset_1(C_1471, k1_zfmisc_1(A_1473)) | v1_xboole_0(C_1471) | v1_xboole_0(B_1476) | v1_xboole_0(A_1473))), inference(resolution, [status(thm)], [c_70, c_21002])).
% 21.41/11.42  tff(c_25048, plain, (![A_1473, C_1471, E_1475]: (k2_partfun1(k4_subset_1(A_1473, C_1471, '#skF_5'), '#skF_3', k1_tmap_1(A_1473, '#skF_3', C_1471, '#skF_5', E_1475, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1473, '#skF_3', C_1471, '#skF_5', E_1475, '#skF_7')) | k2_partfun1(C_1471, '#skF_3', E_1475, k9_subset_1(A_1473, C_1471, '#skF_5'))!=k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1(A_1473, C_1471, '#skF_5')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_1475, k1_zfmisc_1(k2_zfmisc_1(C_1471, '#skF_3'))) | ~v1_funct_2(E_1475, C_1471, '#skF_3') | ~v1_funct_1(E_1475) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1473)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1471, k1_zfmisc_1(A_1473)) | v1_xboole_0(C_1471) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1473))), inference(resolution, [status(thm)], [c_76, c_25044])).
% 21.41/11.42  tff(c_25054, plain, (![A_1473, C_1471, E_1475]: (k2_partfun1(k4_subset_1(A_1473, C_1471, '#skF_5'), '#skF_3', k1_tmap_1(A_1473, '#skF_3', C_1471, '#skF_5', E_1475, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1473, '#skF_3', C_1471, '#skF_5', E_1475, '#skF_7')) | k2_partfun1(C_1471, '#skF_3', E_1475, k9_subset_1(A_1473, C_1471, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_1473, C_1471, '#skF_5')) | ~m1_subset_1(E_1475, k1_zfmisc_1(k2_zfmisc_1(C_1471, '#skF_3'))) | ~v1_funct_2(E_1475, C_1471, '#skF_3') | ~v1_funct_1(E_1475) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1473)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1471, k1_zfmisc_1(A_1473)) | v1_xboole_0(C_1471) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1473))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_10536, c_25048])).
% 21.41/11.42  tff(c_30151, plain, (![A_1583, C_1584, E_1585]: (k2_partfun1(k4_subset_1(A_1583, C_1584, '#skF_5'), '#skF_3', k1_tmap_1(A_1583, '#skF_3', C_1584, '#skF_5', E_1585, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1583, '#skF_3', C_1584, '#skF_5', E_1585, '#skF_7')) | k2_partfun1(C_1584, '#skF_3', E_1585, k9_subset_1(A_1583, C_1584, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_1583, C_1584, '#skF_5')) | ~m1_subset_1(E_1585, k1_zfmisc_1(k2_zfmisc_1(C_1584, '#skF_3'))) | ~v1_funct_2(E_1585, C_1584, '#skF_3') | ~v1_funct_1(E_1585) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1583)) | ~m1_subset_1(C_1584, k1_zfmisc_1(A_1583)) | v1_xboole_0(C_1584) | v1_xboole_0(A_1583))), inference(negUnitSimplification, [status(thm)], [c_98, c_92, c_25054])).
% 21.41/11.42  tff(c_30158, plain, (![A_1583]: (k2_partfun1(k4_subset_1(A_1583, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_1583, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1583, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1(A_1583, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_1583, '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1583)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1583)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1583))), inference(resolution, [status(thm)], [c_82, c_30151])).
% 21.41/11.42  tff(c_30168, plain, (![A_1583]: (k2_partfun1(k4_subset_1(A_1583, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_1583, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1583, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_1583, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_1583, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1583)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1583)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1583))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_10539, c_30158])).
% 21.41/11.42  tff(c_30865, plain, (![A_1601]: (k2_partfun1(k4_subset_1(A_1601, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_1601, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1601, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_1601, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_1601, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1601)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1601)) | v1_xboole_0(A_1601))), inference(negUnitSimplification, [status(thm)], [c_96, c_30168])).
% 21.41/11.42  tff(c_188, plain, (![C_255, A_256, B_257]: (v1_relat_1(C_255) | ~m1_subset_1(C_255, k1_zfmisc_1(k2_zfmisc_1(A_256, B_257))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 21.41/11.42  tff(c_196, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_188])).
% 21.41/11.42  tff(c_212, plain, (k1_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_196, c_32])).
% 21.41/11.42  tff(c_215, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_212])).
% 21.41/11.42  tff(c_174, plain, (![A_254]: (k9_relat_1(A_254, k1_relat_1(A_254))=k2_relat_1(A_254) | ~v1_relat_1(A_254))), inference(cnfTransformation, [status(thm)], [f_52])).
% 21.41/11.42  tff(c_183, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_174])).
% 21.41/11.42  tff(c_186, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_183])).
% 21.41/11.42  tff(c_187, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_186])).
% 21.41/11.42  tff(c_269, plain, (![A_270, B_271]: (k7_relat_1(A_270, B_271)=k1_xboole_0 | ~r1_xboole_0(B_271, k1_relat_1(A_270)) | ~v1_relat_1(A_270))), inference(cnfTransformation, [status(thm)], [f_72])).
% 21.41/11.42  tff(c_518, plain, (![A_305]: (k7_relat_1(A_305, '#skF_1'(k1_relat_1(A_305)))=k1_xboole_0 | ~v1_relat_1(A_305) | k1_relat_1(A_305)=k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_269])).
% 21.41/11.42  tff(c_530, plain, (![A_305]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_305) | ~v1_relat_1(A_305) | k1_relat_1(A_305)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_518, c_14])).
% 21.41/11.42  tff(c_554, plain, (![A_310]: (~v1_relat_1(A_310) | ~v1_relat_1(A_310) | k1_relat_1(A_310)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_187, c_530])).
% 21.41/11.42  tff(c_556, plain, (~v1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_196, c_554])).
% 21.41/11.42  tff(c_563, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_196, c_556])).
% 21.41/11.42  tff(c_565, plain, $false, inference(negUnitSimplification, [status(thm)], [c_215, c_563])).
% 21.41/11.42  tff(c_566, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_212])).
% 21.41/11.42  tff(c_570, plain, (~v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_566, c_187])).
% 21.41/11.42  tff(c_583, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_196, c_570])).
% 21.41/11.42  tff(c_585, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_186])).
% 21.41/11.42  tff(c_668, plain, (![B_323, A_324]: (r1_xboole_0(k1_relat_1(B_323), A_324) | k7_relat_1(B_323, A_324)!=k1_xboole_0 | ~v1_relat_1(B_323))), inference(cnfTransformation, [status(thm)], [f_89])).
% 21.41/11.42  tff(c_677, plain, (![A_324]: (r1_xboole_0(k1_xboole_0, A_324) | k7_relat_1(k1_xboole_0, A_324)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_668])).
% 21.41/11.42  tff(c_681, plain, (![A_324]: (r1_xboole_0(k1_xboole_0, A_324) | k7_relat_1(k1_xboole_0, A_324)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_585, c_677])).
% 21.41/11.42  tff(c_961, plain, (![B_343, A_344]: (k9_relat_1(B_343, A_344)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_343), A_344) | ~v1_relat_1(B_343))), inference(cnfTransformation, [status(thm)], [f_58])).
% 21.41/11.42  tff(c_978, plain, (![A_344]: (k9_relat_1(k1_xboole_0, A_344)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_344) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_961])).
% 21.41/11.42  tff(c_998, plain, (![A_348]: (k9_relat_1(k1_xboole_0, A_348)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_348))), inference(demodulation, [status(thm), theory('equality')], [c_585, c_978])).
% 21.41/11.42  tff(c_1015, plain, (![A_324]: (k9_relat_1(k1_xboole_0, A_324)=k1_xboole_0 | k7_relat_1(k1_xboole_0, A_324)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_681, c_998])).
% 21.41/11.42  tff(c_790, plain, (![B_334, A_335]: (r1_xboole_0(k1_relat_1(B_334), A_335) | k9_relat_1(B_334, A_335)!=k1_xboole_0 | ~v1_relat_1(B_334))), inference(cnfTransformation, [status(thm)], [f_58])).
% 21.41/11.42  tff(c_807, plain, (![A_335]: (r1_xboole_0(k1_xboole_0, A_335) | k9_relat_1(k1_xboole_0, A_335)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_790])).
% 21.41/11.42  tff(c_813, plain, (![A_335]: (r1_xboole_0(k1_xboole_0, A_335) | k9_relat_1(k1_xboole_0, A_335)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_585, c_807])).
% 21.41/11.42  tff(c_600, plain, (![C_311, A_312, B_313]: (v1_relat_1(C_311) | ~m1_subset_1(C_311, k1_zfmisc_1(k2_zfmisc_1(A_312, B_313))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 21.41/11.42  tff(c_608, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_600])).
% 21.41/11.42  tff(c_630, plain, (![C_314, A_315, B_316]: (v4_relat_1(C_314, A_315) | ~m1_subset_1(C_314, k1_zfmisc_1(k2_zfmisc_1(A_315, B_316))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 21.41/11.42  tff(c_638, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_82, c_630])).
% 21.41/11.42  tff(c_1126, plain, (![B_353, A_354]: (k1_relat_1(B_353)=A_354 | ~v1_partfun1(B_353, A_354) | ~v4_relat_1(B_353, A_354) | ~v1_relat_1(B_353))), inference(cnfTransformation, [status(thm)], [f_141])).
% 21.41/11.42  tff(c_1129, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_638, c_1126])).
% 21.41/11.42  tff(c_1135, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_608, c_1129])).
% 21.41/11.42  tff(c_1139, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_1135])).
% 21.41/11.42  tff(c_1812, plain, (![C_407, A_408, B_409]: (v1_partfun1(C_407, A_408) | ~v1_funct_2(C_407, A_408, B_409) | ~v1_funct_1(C_407) | ~m1_subset_1(C_407, k1_zfmisc_1(k2_zfmisc_1(A_408, B_409))) | v1_xboole_0(B_409))), inference(cnfTransformation, [status(thm)], [f_133])).
% 21.41/11.42  tff(c_1818, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_82, c_1812])).
% 21.41/11.42  tff(c_1825, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_1818])).
% 21.41/11.42  tff(c_1827, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_1139, c_1825])).
% 21.41/11.42  tff(c_1828, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_1135])).
% 21.41/11.42  tff(c_1840, plain, (![B_24]: (k7_relat_1('#skF_6', B_24)=k1_xboole_0 | ~r1_xboole_0(B_24, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1828, c_24])).
% 21.41/11.42  tff(c_2492, plain, (![B_445]: (k7_relat_1('#skF_6', B_445)=k1_xboole_0 | ~r1_xboole_0(B_445, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_608, c_1840])).
% 21.41/11.42  tff(c_2537, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0 | k9_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_813, c_2492])).
% 21.41/11.42  tff(c_4500, plain, (k9_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2537])).
% 21.41/11.42  tff(c_4508, plain, (k7_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1015, c_4500])).
% 21.41/11.42  tff(c_1837, plain, (![A_15]: (r1_xboole_0('#skF_4', A_15) | k9_relat_1('#skF_6', A_15)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1828, c_20])).
% 21.41/11.42  tff(c_2418, plain, (![A_441]: (r1_xboole_0('#skF_4', A_441) | k9_relat_1('#skF_6', A_441)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_608, c_1837])).
% 21.41/11.42  tff(c_732, plain, (![A_331, B_332]: (k7_relat_1(A_331, B_332)=k1_xboole_0 | ~r1_xboole_0(B_332, k1_relat_1(A_331)) | ~v1_relat_1(A_331))), inference(cnfTransformation, [status(thm)], [f_72])).
% 21.41/11.42  tff(c_755, plain, (![B_332]: (k7_relat_1(k1_xboole_0, B_332)=k1_xboole_0 | ~r1_xboole_0(B_332, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_732])).
% 21.41/11.42  tff(c_762, plain, (![B_332]: (k7_relat_1(k1_xboole_0, B_332)=k1_xboole_0 | ~r1_xboole_0(B_332, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_585, c_755])).
% 21.41/11.42  tff(c_2441, plain, (k7_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0 | k9_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_2418, c_762])).
% 21.41/11.42  tff(c_4980, plain, (k9_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_4508, c_2441])).
% 21.41/11.42  tff(c_584, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_186])).
% 21.41/11.42  tff(c_607, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_76, c_600])).
% 21.41/11.42  tff(c_637, plain, (v4_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_76, c_630])).
% 21.41/11.42  tff(c_1132, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_637, c_1126])).
% 21.41/11.42  tff(c_1138, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_607, c_1132])).
% 21.41/11.42  tff(c_1884, plain, (~v1_partfun1('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_1138])).
% 21.41/11.42  tff(c_2201, plain, (![C_430, A_431, B_432]: (v1_partfun1(C_430, A_431) | ~v1_funct_2(C_430, A_431, B_432) | ~v1_funct_1(C_430) | ~m1_subset_1(C_430, k1_zfmisc_1(k2_zfmisc_1(A_431, B_432))) | v1_xboole_0(B_432))), inference(cnfTransformation, [status(thm)], [f_133])).
% 21.41/11.42  tff(c_2204, plain, (v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_76, c_2201])).
% 21.41/11.42  tff(c_2210, plain, (v1_partfun1('#skF_7', '#skF_5') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_2204])).
% 21.41/11.42  tff(c_2212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_1884, c_2210])).
% 21.41/11.42  tff(c_2213, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitRight, [status(thm)], [c_1138])).
% 21.41/11.42  tff(c_2225, plain, (![B_24]: (k7_relat_1('#skF_7', B_24)=k1_xboole_0 | ~r1_xboole_0(B_24, '#skF_5') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2213, c_24])).
% 21.41/11.42  tff(c_2359, plain, (![B_440]: (k7_relat_1('#skF_7', B_440)=k1_xboole_0 | ~r1_xboole_0(B_440, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_607, c_2225])).
% 21.41/11.42  tff(c_2375, plain, (![A_28]: (k7_relat_1('#skF_7', A_28)=k1_xboole_0 | ~r1_subset_1(A_28, '#skF_5') | v1_xboole_0('#skF_5') | v1_xboole_0(A_28))), inference(resolution, [status(thm)], [c_40, c_2359])).
% 21.41/11.42  tff(c_4283, plain, (![A_565]: (k7_relat_1('#skF_7', A_565)=k1_xboole_0 | ~r1_subset_1(A_565, '#skF_5') | v1_xboole_0(A_565))), inference(negUnitSimplification, [status(thm)], [c_92, c_2375])).
% 21.41/11.42  tff(c_4290, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_88, c_4283])).
% 21.41/11.42  tff(c_4296, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_96, c_4290])).
% 21.41/11.42  tff(c_2231, plain, (![A_26]: (r1_xboole_0('#skF_5', A_26) | k7_relat_1('#skF_7', A_26)!=k1_xboole_0 | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2213, c_36])).
% 21.41/11.42  tff(c_2269, plain, (![A_434]: (r1_xboole_0('#skF_5', A_434) | k7_relat_1('#skF_7', A_434)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_607, c_2231])).
% 21.41/11.42  tff(c_4454, plain, (![A_573]: (k3_xboole_0('#skF_5', A_573)=k1_xboole_0 | k7_relat_1('#skF_7', A_573)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2269, c_2])).
% 21.41/11.42  tff(c_4468, plain, (k3_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4296, c_4454])).
% 21.41/11.42  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 21.41/11.42  tff(c_2219, plain, (![A_15]: (k9_relat_1('#skF_7', A_15)=k1_xboole_0 | ~r1_xboole_0('#skF_5', A_15) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2213, c_18])).
% 21.41/11.42  tff(c_2307, plain, (![A_436]: (k9_relat_1('#skF_7', A_436)=k1_xboole_0 | ~r1_xboole_0('#skF_5', A_436))), inference(demodulation, [status(thm), theory('equality')], [c_607, c_2219])).
% 21.41/11.42  tff(c_4716, plain, (![B_599]: (k9_relat_1('#skF_7', B_599)=k1_xboole_0 | k3_xboole_0('#skF_5', B_599)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_2307])).
% 21.41/11.42  tff(c_2222, plain, (![A_15]: (r1_xboole_0('#skF_5', A_15) | k9_relat_1('#skF_7', A_15)!=k1_xboole_0 | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2213, c_20])).
% 21.41/11.42  tff(c_2594, plain, (![A_451]: (r1_xboole_0('#skF_5', A_451) | k9_relat_1('#skF_7', A_451)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_607, c_2222])).
% 21.41/11.42  tff(c_1860, plain, (![B_24]: (k7_relat_1('#skF_6', B_24)=k1_xboole_0 | ~r1_xboole_0(B_24, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_608, c_1840])).
% 21.41/11.42  tff(c_2623, plain, (k7_relat_1('#skF_6', '#skF_5')=k1_xboole_0 | k9_relat_1('#skF_7', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_2594, c_1860])).
% 21.41/11.42  tff(c_4666, plain, (k9_relat_1('#skF_7', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2623])).
% 21.41/11.42  tff(c_4722, plain, (k3_xboole_0('#skF_5', '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4716, c_4666])).
% 21.41/11.42  tff(c_4750, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4468, c_4722])).
% 21.41/11.42  tff(c_4751, plain, (k7_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2623])).
% 21.41/11.42  tff(c_4759, plain, (![B_20]: (k9_relat_1(k1_xboole_0, B_20)=k9_relat_1('#skF_6', B_20) | ~r1_tarski(B_20, '#skF_5') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_4751, c_22])).
% 21.41/11.42  tff(c_5276, plain, (![B_632]: (k9_relat_1(k1_xboole_0, B_632)=k9_relat_1('#skF_6', B_632) | ~r1_tarski(B_632, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_608, c_4759])).
% 21.41/11.42  tff(c_5280, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k9_relat_1('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_5276])).
% 21.41/11.42  tff(c_5282, plain, (k9_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_584, c_5280])).
% 21.41/11.42  tff(c_5284, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4980, c_5282])).
% 21.41/11.42  tff(c_5285, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_2537])).
% 21.41/11.42  tff(c_1834, plain, (![A_15]: (k9_relat_1('#skF_6', A_15)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_15) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1828, c_18])).
% 21.41/11.42  tff(c_2562, plain, (![A_446]: (k9_relat_1('#skF_6', A_446)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_446))), inference(demodulation, [status(thm), theory('equality')], [c_608, c_1834])).
% 21.41/11.42  tff(c_2572, plain, (![B_29]: (k9_relat_1('#skF_6', B_29)=k1_xboole_0 | ~r1_subset_1('#skF_4', B_29) | v1_xboole_0(B_29) | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_2562])).
% 21.41/11.42  tff(c_5732, plain, (![B_665]: (k9_relat_1('#skF_6', B_665)=k1_xboole_0 | ~r1_subset_1('#skF_4', B_665) | v1_xboole_0(B_665))), inference(negUnitSimplification, [status(thm)], [c_96, c_2572])).
% 21.41/11.42  tff(c_5735, plain, (k9_relat_1('#skF_6', '#skF_5')=k1_xboole_0 | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_88, c_5732])).
% 21.41/11.42  tff(c_5738, plain, (k9_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_92, c_5735])).
% 21.41/11.42  tff(c_2443, plain, (![A_441]: (k3_xboole_0('#skF_4', A_441)=k1_xboole_0 | k9_relat_1('#skF_6', A_441)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2418, c_2])).
% 21.41/11.42  tff(c_5754, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5738, c_2443])).
% 21.41/11.42  tff(c_2287, plain, (k7_relat_1(k1_xboole_0, '#skF_5')=k1_xboole_0 | k7_relat_1('#skF_7', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_2269, c_762])).
% 21.41/11.42  tff(c_2657, plain, (k7_relat_1('#skF_7', k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2287])).
% 21.41/11.42  tff(c_2393, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0 | k9_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_813, c_2359])).
% 21.41/11.42  tff(c_2704, plain, (k9_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_2657, c_2393])).
% 21.41/11.42  tff(c_2712, plain, (k7_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1015, c_2704])).
% 21.41/11.42  tff(c_2631, plain, (k7_relat_1(k1_xboole_0, '#skF_5')=k1_xboole_0 | k9_relat_1('#skF_7', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_2594, c_762])).
% 21.41/11.42  tff(c_3860, plain, (k9_relat_1('#skF_7', k1_xboole_0)!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_2712, c_2631])).
% 21.41/11.42  tff(c_2245, plain, (![B_24]: (k7_relat_1('#skF_7', B_24)=k1_xboole_0 | ~r1_xboole_0(B_24, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_607, c_2225])).
% 21.41/11.42  tff(c_2437, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0 | k9_relat_1('#skF_6', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_2418, c_2245])).
% 21.41/11.42  tff(c_2817, plain, (k9_relat_1('#skF_6', '#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2437])).
% 21.41/11.42  tff(c_2818, plain, (![B_469]: (k9_relat_1('#skF_6', B_469)=k1_xboole_0 | ~r1_subset_1('#skF_4', B_469) | v1_xboole_0(B_469))), inference(negUnitSimplification, [status(thm)], [c_96, c_2572])).
% 21.41/11.42  tff(c_2821, plain, (k9_relat_1('#skF_6', '#skF_5')=k1_xboole_0 | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_88, c_2818])).
% 21.41/11.42  tff(c_2824, plain, (k9_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_92, c_2821])).
% 21.41/11.42  tff(c_2825, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2817, c_2824])).
% 21.41/11.42  tff(c_2826, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2437])).
% 21.41/11.42  tff(c_2834, plain, (![B_20]: (k9_relat_1(k1_xboole_0, B_20)=k9_relat_1('#skF_7', B_20) | ~r1_tarski(B_20, '#skF_4') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2826, c_22])).
% 21.41/11.42  tff(c_4272, plain, (![B_564]: (k9_relat_1(k1_xboole_0, B_564)=k9_relat_1('#skF_7', B_564) | ~r1_tarski(B_564, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_607, c_2834])).
% 21.41/11.42  tff(c_4276, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k9_relat_1('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_4272])).
% 21.41/11.42  tff(c_4278, plain, (k9_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_584, c_4276])).
% 21.41/11.42  tff(c_4280, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3860, c_4278])).
% 21.41/11.42  tff(c_4282, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_2287])).
% 21.41/11.42  tff(c_2583, plain, (![A_447, B_448, C_449, D_450]: (k2_partfun1(A_447, B_448, C_449, D_450)=k7_relat_1(C_449, D_450) | ~m1_subset_1(C_449, k1_zfmisc_1(k2_zfmisc_1(A_447, B_448))) | ~v1_funct_1(C_449))), inference(cnfTransformation, [status(thm)], [f_147])).
% 21.41/11.42  tff(c_2585, plain, (![D_450]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_450)=k7_relat_1('#skF_7', D_450) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_76, c_2583])).
% 21.41/11.42  tff(c_2590, plain, (![D_450]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_450)=k7_relat_1('#skF_7', D_450))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2585])).
% 21.41/11.42  tff(c_2587, plain, (![D_450]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_450)=k7_relat_1('#skF_6', D_450) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_82, c_2583])).
% 21.41/11.42  tff(c_2593, plain, (![D_450]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_450)=k7_relat_1('#skF_6', D_450))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_2587])).
% 21.41/11.42  tff(c_985, plain, (![A_345, B_346, C_347]: (k9_subset_1(A_345, B_346, C_347)=k3_xboole_0(B_346, C_347) | ~m1_subset_1(C_347, k1_zfmisc_1(A_345)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 21.41/11.42  tff(c_997, plain, (![B_346]: (k9_subset_1('#skF_2', B_346, '#skF_5')=k3_xboole_0(B_346, '#skF_5'))), inference(resolution, [status(thm)], [c_90, c_985])).
% 21.41/11.42  tff(c_74, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')!='#skF_7' | k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')!='#skF_6' | k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_271])).
% 21.41/11.42  tff(c_113, plain, (k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_74])).
% 21.41/11.42  tff(c_1026, plain, (k2_partfun1('#skF_5', '#skF_3', '#skF_7', k3_xboole_0('#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_997, c_997, c_113])).
% 21.41/11.42  tff(c_7590, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5285, c_5754, c_4282, c_5754, c_2590, c_2593, c_1026])).
% 21.41/11.42  tff(c_7591, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_74])).
% 21.41/11.42  tff(c_7699, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')!='#skF_7'), inference(splitLeft, [status(thm)], [c_7591])).
% 21.41/11.42  tff(c_30876, plain, (~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_30865, c_7699])).
% 21.41/11.42  tff(c_30890, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_90, c_12130, c_11664, c_11359, c_10146, c_11359, c_10146, c_13089, c_30876])).
% 21.41/11.42  tff(c_30892, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_30890])).
% 21.41/11.42  tff(c_30893, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_7591])).
% 21.41/11.42  tff(c_31560, plain, (![C_1672, A_1673, B_1674]: (v4_relat_1(C_1672, A_1673) | ~m1_subset_1(C_1672, k1_zfmisc_1(k2_zfmisc_1(A_1673, B_1674))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 21.41/11.42  tff(c_31568, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_82, c_31560])).
% 21.41/11.42  tff(c_32055, plain, (![B_1706, A_1707]: (k1_relat_1(B_1706)=A_1707 | ~v1_partfun1(B_1706, A_1707) | ~v4_relat_1(B_1706, A_1707) | ~v1_relat_1(B_1706))), inference(cnfTransformation, [status(thm)], [f_141])).
% 21.41/11.42  tff(c_32058, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_31568, c_32055])).
% 21.41/11.42  tff(c_32064, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7644, c_32058])).
% 21.41/11.42  tff(c_32068, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_32064])).
% 21.41/11.42  tff(c_32971, plain, (![C_1774, A_1775, B_1776]: (v1_partfun1(C_1774, A_1775) | ~v1_funct_2(C_1774, A_1775, B_1776) | ~v1_funct_1(C_1774) | ~m1_subset_1(C_1774, k1_zfmisc_1(k2_zfmisc_1(A_1775, B_1776))) | v1_xboole_0(B_1776))), inference(cnfTransformation, [status(thm)], [f_133])).
% 21.41/11.42  tff(c_32977, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_82, c_32971])).
% 21.41/11.42  tff(c_32984, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_32977])).
% 21.41/11.42  tff(c_32986, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_32068, c_32984])).
% 21.41/11.42  tff(c_32987, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_32064])).
% 21.41/11.42  tff(c_33000, plain, (![B_24]: (k7_relat_1('#skF_6', B_24)=k1_xboole_0 | ~r1_xboole_0(B_24, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_32987, c_24])).
% 21.41/11.42  tff(c_33873, plain, (![B_1826]: (k7_relat_1('#skF_6', B_1826)=k1_xboole_0 | ~r1_xboole_0(B_1826, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7644, c_33000])).
% 21.41/11.42  tff(c_33925, plain, (![A_1]: (k7_relat_1('#skF_6', A_1)=k1_xboole_0 | k3_xboole_0(A_1, '#skF_4')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_33873])).
% 21.41/11.42  tff(c_32997, plain, (![A_26]: (r1_xboole_0('#skF_4', A_26) | k7_relat_1('#skF_6', A_26)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_32987, c_36])).
% 21.41/11.42  tff(c_33727, plain, (![A_1818]: (r1_xboole_0('#skF_4', A_1818) | k7_relat_1('#skF_6', A_1818)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7644, c_32997])).
% 21.41/11.42  tff(c_30895, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_7696])).
% 21.41/11.42  tff(c_30905, plain, (![C_1605, A_1606, B_1607]: (v4_relat_1(C_1605, A_1606) | ~m1_subset_1(C_1605, k1_zfmisc_1(k2_zfmisc_1(A_1606, B_1607))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 21.41/11.42  tff(c_30912, plain, (v4_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_76, c_30905])).
% 21.41/11.42  tff(c_31094, plain, (![B_1627, A_1628]: (k1_relat_1(B_1627)=A_1628 | ~v1_partfun1(B_1627, A_1628) | ~v4_relat_1(B_1627, A_1628) | ~v1_relat_1(B_1627))), inference(cnfTransformation, [status(thm)], [f_141])).
% 21.41/11.42  tff(c_31100, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_30912, c_31094])).
% 21.41/11.42  tff(c_31106, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7643, c_31100])).
% 21.41/11.42  tff(c_31108, plain, (~v1_partfun1('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_31106])).
% 21.41/11.42  tff(c_31295, plain, (![C_1655, A_1656, B_1657]: (v1_partfun1(C_1655, A_1656) | ~v1_funct_2(C_1655, A_1656, B_1657) | ~v1_funct_1(C_1655) | ~m1_subset_1(C_1655, k1_zfmisc_1(k2_zfmisc_1(A_1656, B_1657))) | v1_xboole_0(B_1657))), inference(cnfTransformation, [status(thm)], [f_133])).
% 21.41/11.42  tff(c_31298, plain, (v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_76, c_31295])).
% 21.41/11.42  tff(c_31304, plain, (v1_partfun1('#skF_7', '#skF_5') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_31298])).
% 21.41/11.42  tff(c_31306, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_31108, c_31304])).
% 21.41/11.42  tff(c_31307, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitRight, [status(thm)], [c_31106])).
% 21.41/11.42  tff(c_7652, plain, (k1_relat_1('#skF_7')!=k1_xboole_0 | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_7643, c_32])).
% 21.41/11.42  tff(c_7680, plain, (k1_relat_1('#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7652])).
% 21.41/11.42  tff(c_31310, plain, (k1_xboole_0!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_31307, c_7680])).
% 21.41/11.42  tff(c_31326, plain, (![B_24]: (k7_relat_1('#skF_7', B_24)=k1_xboole_0 | ~r1_xboole_0(B_24, '#skF_5') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_31307, c_24])).
% 21.41/11.42  tff(c_31478, plain, (![B_1668]: (k7_relat_1('#skF_7', B_1668)=k1_xboole_0 | ~r1_xboole_0(B_1668, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_7643, c_31326])).
% 21.41/11.42  tff(c_31506, plain, (k7_relat_1('#skF_7', '#skF_1'('#skF_5'))=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_48, c_31478])).
% 21.41/11.42  tff(c_31520, plain, (k7_relat_1('#skF_7', '#skF_1'('#skF_5'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_31310, c_31506])).
% 21.41/11.42  tff(c_31524, plain, (v1_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_31520, c_14])).
% 21.41/11.42  tff(c_31528, plain, (v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7643, c_31524])).
% 21.41/11.42  tff(c_31530, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30895, c_31528])).
% 21.41/11.42  tff(c_31532, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_7696])).
% 21.41/11.42  tff(c_31669, plain, (![A_1684, B_1685]: (k7_relat_1(A_1684, B_1685)=k1_xboole_0 | ~r1_xboole_0(B_1685, k1_relat_1(A_1684)) | ~v1_relat_1(A_1684))), inference(cnfTransformation, [status(thm)], [f_72])).
% 21.41/11.42  tff(c_31688, plain, (![B_1685]: (k7_relat_1(k1_xboole_0, B_1685)=k1_xboole_0 | ~r1_xboole_0(B_1685, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_31669])).
% 21.41/11.42  tff(c_31694, plain, (![B_1685]: (k7_relat_1(k1_xboole_0, B_1685)=k1_xboole_0 | ~r1_xboole_0(B_1685, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_31532, c_31688])).
% 21.41/11.42  tff(c_33749, plain, (k7_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0 | k7_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_33727, c_31694])).
% 21.41/11.42  tff(c_34831, plain, (k7_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_33749])).
% 21.41/11.42  tff(c_34838, plain, (k3_xboole_0(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_33925, c_34831])).
% 21.41/11.42  tff(c_33003, plain, (![A_15]: (r1_xboole_0('#skF_4', A_15) | k9_relat_1('#skF_6', A_15)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_32987, c_20])).
% 21.41/11.42  tff(c_33943, plain, (![A_1827]: (r1_xboole_0('#skF_4', A_1827) | k9_relat_1('#skF_6', A_1827)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7644, c_33003])).
% 21.41/11.42  tff(c_33981, plain, (k7_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0 | k9_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_33943, c_31694])).
% 21.41/11.42  tff(c_34928, plain, (k9_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_33981])).
% 21.41/11.42  tff(c_31531, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_7696])).
% 21.41/11.42  tff(c_33018, plain, (![A_26]: (r1_xboole_0('#skF_4', A_26) | k7_relat_1('#skF_6', A_26)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7644, c_32997])).
% 21.41/11.42  tff(c_31567, plain, (v4_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_76, c_31560])).
% 21.41/11.42  tff(c_32061, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_31567, c_32055])).
% 21.41/11.42  tff(c_32067, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7643, c_32061])).
% 21.41/11.42  tff(c_33079, plain, (~v1_partfun1('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_32067])).
% 21.41/11.42  tff(c_33520, plain, (![C_1805, A_1806, B_1807]: (v1_partfun1(C_1805, A_1806) | ~v1_funct_2(C_1805, A_1806, B_1807) | ~v1_funct_1(C_1805) | ~m1_subset_1(C_1805, k1_zfmisc_1(k2_zfmisc_1(A_1806, B_1807))) | v1_xboole_0(B_1807))), inference(cnfTransformation, [status(thm)], [f_133])).
% 21.41/11.42  tff(c_33523, plain, (v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_76, c_33520])).
% 21.41/11.42  tff(c_33529, plain, (v1_partfun1('#skF_7', '#skF_5') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_33523])).
% 21.41/11.42  tff(c_33531, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_33079, c_33529])).
% 21.41/11.42  tff(c_33532, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitRight, [status(thm)], [c_32067])).
% 21.41/11.42  tff(c_33545, plain, (![B_24]: (k7_relat_1('#skF_7', B_24)=k1_xboole_0 | ~r1_xboole_0(B_24, '#skF_5') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_33532, c_24])).
% 21.41/11.42  tff(c_33769, plain, (![B_1820]: (k7_relat_1('#skF_7', B_1820)=k1_xboole_0 | ~r1_xboole_0(B_1820, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_7643, c_33545])).
% 21.41/11.42  tff(c_33810, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0 | k7_relat_1('#skF_6', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_33018, c_33769])).
% 21.41/11.42  tff(c_34145, plain, (k7_relat_1('#skF_6', '#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_33810])).
% 21.41/11.42  tff(c_33542, plain, (![A_26]: (r1_xboole_0('#skF_5', A_26) | k7_relat_1('#skF_7', A_26)!=k1_xboole_0 | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_33532, c_36])).
% 21.41/11.42  tff(c_33563, plain, (![A_26]: (r1_xboole_0('#skF_5', A_26) | k7_relat_1('#skF_7', A_26)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7643, c_33542])).
% 21.41/11.42  tff(c_33916, plain, (k7_relat_1('#skF_6', '#skF_5')=k1_xboole_0 | k7_relat_1('#skF_7', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_33563, c_33873])).
% 21.41/11.42  tff(c_34397, plain, (k7_relat_1('#skF_7', '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_34145, c_33916])).
% 21.41/11.42  tff(c_33785, plain, (![A_28]: (k7_relat_1('#skF_7', A_28)=k1_xboole_0 | ~r1_subset_1(A_28, '#skF_5') | v1_xboole_0('#skF_5') | v1_xboole_0(A_28))), inference(resolution, [status(thm)], [c_40, c_33769])).
% 21.41/11.42  tff(c_34471, plain, (![A_1867]: (k7_relat_1('#skF_7', A_1867)=k1_xboole_0 | ~r1_subset_1(A_1867, '#skF_5') | v1_xboole_0(A_1867))), inference(negUnitSimplification, [status(thm)], [c_92, c_33785])).
% 21.41/11.42  tff(c_34486, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_88, c_34471])).
% 21.41/11.42  tff(c_34496, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_34397, c_34486])).
% 21.41/11.42  tff(c_34498, plain, (k7_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_33810])).
% 21.41/11.42  tff(c_34531, plain, (![B_20]: (k9_relat_1(k1_xboole_0, B_20)=k9_relat_1('#skF_6', B_20) | ~r1_tarski(B_20, '#skF_5') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_34498, c_22])).
% 21.41/11.42  tff(c_35105, plain, (![B_1917]: (k9_relat_1(k1_xboole_0, B_1917)=k9_relat_1('#skF_6', B_1917) | ~r1_tarski(B_1917, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_7644, c_34531])).
% 21.41/11.42  tff(c_35109, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k9_relat_1('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_35105])).
% 21.41/11.42  tff(c_35111, plain, (k9_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_31531, c_35109])).
% 21.41/11.42  tff(c_35113, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34928, c_35111])).
% 21.41/11.42  tff(c_35114, plain, (k7_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_33981])).
% 21.41/11.42  tff(c_31771, plain, (![B_1690, A_1691]: (r1_xboole_0(k1_relat_1(B_1690), A_1691) | k7_relat_1(B_1690, A_1691)!=k1_xboole_0 | ~v1_relat_1(B_1690))), inference(cnfTransformation, [status(thm)], [f_89])).
% 21.41/11.42  tff(c_31791, plain, (![A_1691]: (r1_xboole_0(k1_xboole_0, A_1691) | k7_relat_1(k1_xboole_0, A_1691)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_31771])).
% 21.41/11.42  tff(c_31799, plain, (![A_1692]: (r1_xboole_0(k1_xboole_0, A_1692) | k7_relat_1(k1_xboole_0, A_1692)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_31532, c_31791])).
% 21.41/11.42  tff(c_31823, plain, (![A_1692]: (k3_xboole_0(k1_xboole_0, A_1692)=k1_xboole_0 | k7_relat_1(k1_xboole_0, A_1692)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_31799, c_2])).
% 21.41/11.42  tff(c_35125, plain, (k3_xboole_0(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_35114, c_31823])).
% 21.41/11.42  tff(c_35146, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34838, c_35125])).
% 21.41/11.42  tff(c_35148, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_33749])).
% 21.41/11.42  tff(c_34719, plain, (![A_1880]: (k3_xboole_0('#skF_4', A_1880)=k1_xboole_0 | k7_relat_1('#skF_6', A_1880)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_33727, c_2])).
% 21.41/11.42  tff(c_34733, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_34498, c_34719])).
% 21.41/11.42  tff(c_33066, plain, (![A_1778, B_1779, C_1780]: (k9_subset_1(A_1778, B_1779, C_1780)=k3_xboole_0(B_1779, C_1780) | ~m1_subset_1(C_1780, k1_zfmisc_1(A_1778)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 21.41/11.42  tff(c_33078, plain, (![B_1779]: (k9_subset_1('#skF_2', B_1779, '#skF_5')=k3_xboole_0(B_1779, '#skF_5'))), inference(resolution, [status(thm)], [c_90, c_33066])).
% 21.41/11.42  tff(c_31798, plain, (![A_1691]: (r1_xboole_0(k1_xboole_0, A_1691) | k7_relat_1(k1_xboole_0, A_1691)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_31532, c_31791])).
% 21.41/11.42  tff(c_33819, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0 | k7_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_31798, c_33769])).
% 21.41/11.42  tff(c_35261, plain, (k7_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_33819])).
% 21.41/11.42  tff(c_33548, plain, (![A_15]: (r1_xboole_0('#skF_5', A_15) | k9_relat_1('#skF_7', A_15)!=k1_xboole_0 | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_33532, c_20])).
% 21.41/11.42  tff(c_33607, plain, (![A_1810]: (r1_xboole_0('#skF_5', A_1810) | k9_relat_1('#skF_7', A_1810)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7643, c_33548])).
% 21.41/11.42  tff(c_33625, plain, (k7_relat_1(k1_xboole_0, '#skF_5')=k1_xboole_0 | k9_relat_1('#skF_7', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_33607, c_31694])).
% 21.41/11.42  tff(c_35315, plain, (k9_relat_1('#skF_7', k1_xboole_0)!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_35261, c_33625])).
% 21.41/11.42  tff(c_34497, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_33810])).
% 21.41/11.42  tff(c_34508, plain, (![B_20]: (k9_relat_1(k1_xboole_0, B_20)=k9_relat_1('#skF_7', B_20) | ~r1_tarski(B_20, '#skF_4') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_34497, c_22])).
% 21.41/11.42  tff(c_35476, plain, (![B_1945]: (k9_relat_1(k1_xboole_0, B_1945)=k9_relat_1('#skF_7', B_1945) | ~r1_tarski(B_1945, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7643, c_34508])).
% 21.41/11.42  tff(c_35480, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k9_relat_1('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_35476])).
% 21.41/11.42  tff(c_35482, plain, (k9_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_31531, c_35480])).
% 21.41/11.42  tff(c_35484, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35315, c_35482])).
% 21.41/11.42  tff(c_35485, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_33819])).
% 21.41/11.42  tff(c_33862, plain, (![A_1822, B_1823, C_1824, D_1825]: (k2_partfun1(A_1822, B_1823, C_1824, D_1825)=k7_relat_1(C_1824, D_1825) | ~m1_subset_1(C_1824, k1_zfmisc_1(k2_zfmisc_1(A_1822, B_1823))) | ~v1_funct_1(C_1824))), inference(cnfTransformation, [status(thm)], [f_147])).
% 21.41/11.42  tff(c_33866, plain, (![D_1825]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_1825)=k7_relat_1('#skF_6', D_1825) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_82, c_33862])).
% 21.41/11.42  tff(c_33872, plain, (![D_1825]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_1825)=k7_relat_1('#skF_6', D_1825))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_33866])).
% 21.41/11.42  tff(c_33864, plain, (![D_1825]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_1825)=k7_relat_1('#skF_7', D_1825) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_76, c_33862])).
% 21.41/11.42  tff(c_33869, plain, (![D_1825]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_1825)=k7_relat_1('#skF_7', D_1825))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_33864])).
% 21.41/11.42  tff(c_34568, plain, (![D_1870, A_1871, B_1874, E_1873, F_1872, C_1869]: (v1_funct_1(k1_tmap_1(A_1871, B_1874, C_1869, D_1870, E_1873, F_1872)) | ~m1_subset_1(F_1872, k1_zfmisc_1(k2_zfmisc_1(D_1870, B_1874))) | ~v1_funct_2(F_1872, D_1870, B_1874) | ~v1_funct_1(F_1872) | ~m1_subset_1(E_1873, k1_zfmisc_1(k2_zfmisc_1(C_1869, B_1874))) | ~v1_funct_2(E_1873, C_1869, B_1874) | ~v1_funct_1(E_1873) | ~m1_subset_1(D_1870, k1_zfmisc_1(A_1871)) | v1_xboole_0(D_1870) | ~m1_subset_1(C_1869, k1_zfmisc_1(A_1871)) | v1_xboole_0(C_1869) | v1_xboole_0(B_1874) | v1_xboole_0(A_1871))), inference(cnfTransformation, [status(thm)], [f_229])).
% 21.41/11.42  tff(c_34570, plain, (![A_1871, C_1869, E_1873]: (v1_funct_1(k1_tmap_1(A_1871, '#skF_3', C_1869, '#skF_5', E_1873, '#skF_7')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_1873, k1_zfmisc_1(k2_zfmisc_1(C_1869, '#skF_3'))) | ~v1_funct_2(E_1873, C_1869, '#skF_3') | ~v1_funct_1(E_1873) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1871)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1869, k1_zfmisc_1(A_1871)) | v1_xboole_0(C_1869) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1871))), inference(resolution, [status(thm)], [c_76, c_34568])).
% 21.41/11.42  tff(c_34575, plain, (![A_1871, C_1869, E_1873]: (v1_funct_1(k1_tmap_1(A_1871, '#skF_3', C_1869, '#skF_5', E_1873, '#skF_7')) | ~m1_subset_1(E_1873, k1_zfmisc_1(k2_zfmisc_1(C_1869, '#skF_3'))) | ~v1_funct_2(E_1873, C_1869, '#skF_3') | ~v1_funct_1(E_1873) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1871)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1869, k1_zfmisc_1(A_1871)) | v1_xboole_0(C_1869) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1871))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_34570])).
% 21.41/11.42  tff(c_35812, plain, (![A_1974, C_1975, E_1976]: (v1_funct_1(k1_tmap_1(A_1974, '#skF_3', C_1975, '#skF_5', E_1976, '#skF_7')) | ~m1_subset_1(E_1976, k1_zfmisc_1(k2_zfmisc_1(C_1975, '#skF_3'))) | ~v1_funct_2(E_1976, C_1975, '#skF_3') | ~v1_funct_1(E_1976) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1974)) | ~m1_subset_1(C_1975, k1_zfmisc_1(A_1974)) | v1_xboole_0(C_1975) | v1_xboole_0(A_1974))), inference(negUnitSimplification, [status(thm)], [c_98, c_92, c_34575])).
% 21.41/11.42  tff(c_35819, plain, (![A_1974]: (v1_funct_1(k1_tmap_1(A_1974, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1974)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1974)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1974))), inference(resolution, [status(thm)], [c_82, c_35812])).
% 21.41/11.42  tff(c_35829, plain, (![A_1974]: (v1_funct_1(k1_tmap_1(A_1974, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1974)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1974)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1974))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_35819])).
% 21.41/11.42  tff(c_36525, plain, (![A_2004]: (v1_funct_1(k1_tmap_1(A_2004, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2004)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2004)) | v1_xboole_0(A_2004))), inference(negUnitSimplification, [status(thm)], [c_96, c_35829])).
% 21.41/11.42  tff(c_36528, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_90, c_36525])).
% 21.41/11.42  tff(c_36531, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_36528])).
% 21.41/11.42  tff(c_36532, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_100, c_36531])).
% 21.41/11.42  tff(c_35563, plain, (![B_1951, C_1948, D_1949, A_1947, E_1946, F_1950]: (k2_partfun1(k4_subset_1(A_1947, C_1948, D_1949), B_1951, k1_tmap_1(A_1947, B_1951, C_1948, D_1949, E_1946, F_1950), C_1948)=E_1946 | ~m1_subset_1(k1_tmap_1(A_1947, B_1951, C_1948, D_1949, E_1946, F_1950), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1947, C_1948, D_1949), B_1951))) | ~v1_funct_2(k1_tmap_1(A_1947, B_1951, C_1948, D_1949, E_1946, F_1950), k4_subset_1(A_1947, C_1948, D_1949), B_1951) | ~v1_funct_1(k1_tmap_1(A_1947, B_1951, C_1948, D_1949, E_1946, F_1950)) | k2_partfun1(D_1949, B_1951, F_1950, k9_subset_1(A_1947, C_1948, D_1949))!=k2_partfun1(C_1948, B_1951, E_1946, k9_subset_1(A_1947, C_1948, D_1949)) | ~m1_subset_1(F_1950, k1_zfmisc_1(k2_zfmisc_1(D_1949, B_1951))) | ~v1_funct_2(F_1950, D_1949, B_1951) | ~v1_funct_1(F_1950) | ~m1_subset_1(E_1946, k1_zfmisc_1(k2_zfmisc_1(C_1948, B_1951))) | ~v1_funct_2(E_1946, C_1948, B_1951) | ~v1_funct_1(E_1946) | ~m1_subset_1(D_1949, k1_zfmisc_1(A_1947)) | v1_xboole_0(D_1949) | ~m1_subset_1(C_1948, k1_zfmisc_1(A_1947)) | v1_xboole_0(C_1948) | v1_xboole_0(B_1951) | v1_xboole_0(A_1947))), inference(cnfTransformation, [status(thm)], [f_195])).
% 21.41/11.42  tff(c_44541, plain, (![C_2233, B_2238, A_2235, D_2234, E_2237, F_2236]: (k2_partfun1(k4_subset_1(A_2235, C_2233, D_2234), B_2238, k1_tmap_1(A_2235, B_2238, C_2233, D_2234, E_2237, F_2236), C_2233)=E_2237 | ~v1_funct_2(k1_tmap_1(A_2235, B_2238, C_2233, D_2234, E_2237, F_2236), k4_subset_1(A_2235, C_2233, D_2234), B_2238) | ~v1_funct_1(k1_tmap_1(A_2235, B_2238, C_2233, D_2234, E_2237, F_2236)) | k2_partfun1(D_2234, B_2238, F_2236, k9_subset_1(A_2235, C_2233, D_2234))!=k2_partfun1(C_2233, B_2238, E_2237, k9_subset_1(A_2235, C_2233, D_2234)) | ~m1_subset_1(F_2236, k1_zfmisc_1(k2_zfmisc_1(D_2234, B_2238))) | ~v1_funct_2(F_2236, D_2234, B_2238) | ~v1_funct_1(F_2236) | ~m1_subset_1(E_2237, k1_zfmisc_1(k2_zfmisc_1(C_2233, B_2238))) | ~v1_funct_2(E_2237, C_2233, B_2238) | ~v1_funct_1(E_2237) | ~m1_subset_1(D_2234, k1_zfmisc_1(A_2235)) | v1_xboole_0(D_2234) | ~m1_subset_1(C_2233, k1_zfmisc_1(A_2235)) | v1_xboole_0(C_2233) | v1_xboole_0(B_2238) | v1_xboole_0(A_2235))), inference(resolution, [status(thm)], [c_68, c_35563])).
% 21.41/11.42  tff(c_47637, plain, (![F_2341, E_2342, D_2339, C_2338, A_2340, B_2343]: (k2_partfun1(k4_subset_1(A_2340, C_2338, D_2339), B_2343, k1_tmap_1(A_2340, B_2343, C_2338, D_2339, E_2342, F_2341), C_2338)=E_2342 | ~v1_funct_1(k1_tmap_1(A_2340, B_2343, C_2338, D_2339, E_2342, F_2341)) | k2_partfun1(D_2339, B_2343, F_2341, k9_subset_1(A_2340, C_2338, D_2339))!=k2_partfun1(C_2338, B_2343, E_2342, k9_subset_1(A_2340, C_2338, D_2339)) | ~m1_subset_1(F_2341, k1_zfmisc_1(k2_zfmisc_1(D_2339, B_2343))) | ~v1_funct_2(F_2341, D_2339, B_2343) | ~v1_funct_1(F_2341) | ~m1_subset_1(E_2342, k1_zfmisc_1(k2_zfmisc_1(C_2338, B_2343))) | ~v1_funct_2(E_2342, C_2338, B_2343) | ~v1_funct_1(E_2342) | ~m1_subset_1(D_2339, k1_zfmisc_1(A_2340)) | v1_xboole_0(D_2339) | ~m1_subset_1(C_2338, k1_zfmisc_1(A_2340)) | v1_xboole_0(C_2338) | v1_xboole_0(B_2343) | v1_xboole_0(A_2340))), inference(resolution, [status(thm)], [c_70, c_44541])).
% 21.41/11.42  tff(c_47641, plain, (![A_2340, C_2338, E_2342]: (k2_partfun1(k4_subset_1(A_2340, C_2338, '#skF_5'), '#skF_3', k1_tmap_1(A_2340, '#skF_3', C_2338, '#skF_5', E_2342, '#skF_7'), C_2338)=E_2342 | ~v1_funct_1(k1_tmap_1(A_2340, '#skF_3', C_2338, '#skF_5', E_2342, '#skF_7')) | k2_partfun1(C_2338, '#skF_3', E_2342, k9_subset_1(A_2340, C_2338, '#skF_5'))!=k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1(A_2340, C_2338, '#skF_5')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_2342, k1_zfmisc_1(k2_zfmisc_1(C_2338, '#skF_3'))) | ~v1_funct_2(E_2342, C_2338, '#skF_3') | ~v1_funct_1(E_2342) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2340)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_2338, k1_zfmisc_1(A_2340)) | v1_xboole_0(C_2338) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2340))), inference(resolution, [status(thm)], [c_76, c_47637])).
% 21.41/11.42  tff(c_47647, plain, (![A_2340, C_2338, E_2342]: (k2_partfun1(k4_subset_1(A_2340, C_2338, '#skF_5'), '#skF_3', k1_tmap_1(A_2340, '#skF_3', C_2338, '#skF_5', E_2342, '#skF_7'), C_2338)=E_2342 | ~v1_funct_1(k1_tmap_1(A_2340, '#skF_3', C_2338, '#skF_5', E_2342, '#skF_7')) | k2_partfun1(C_2338, '#skF_3', E_2342, k9_subset_1(A_2340, C_2338, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_2340, C_2338, '#skF_5')) | ~m1_subset_1(E_2342, k1_zfmisc_1(k2_zfmisc_1(C_2338, '#skF_3'))) | ~v1_funct_2(E_2342, C_2338, '#skF_3') | ~v1_funct_1(E_2342) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2340)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_2338, k1_zfmisc_1(A_2340)) | v1_xboole_0(C_2338) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2340))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_33869, c_47641])).
% 21.41/11.42  tff(c_47655, plain, (![A_2344, C_2345, E_2346]: (k2_partfun1(k4_subset_1(A_2344, C_2345, '#skF_5'), '#skF_3', k1_tmap_1(A_2344, '#skF_3', C_2345, '#skF_5', E_2346, '#skF_7'), C_2345)=E_2346 | ~v1_funct_1(k1_tmap_1(A_2344, '#skF_3', C_2345, '#skF_5', E_2346, '#skF_7')) | k2_partfun1(C_2345, '#skF_3', E_2346, k9_subset_1(A_2344, C_2345, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_2344, C_2345, '#skF_5')) | ~m1_subset_1(E_2346, k1_zfmisc_1(k2_zfmisc_1(C_2345, '#skF_3'))) | ~v1_funct_2(E_2346, C_2345, '#skF_3') | ~v1_funct_1(E_2346) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2344)) | ~m1_subset_1(C_2345, k1_zfmisc_1(A_2344)) | v1_xboole_0(C_2345) | v1_xboole_0(A_2344))), inference(negUnitSimplification, [status(thm)], [c_98, c_92, c_47647])).
% 21.41/11.42  tff(c_47662, plain, (![A_2344]: (k2_partfun1(k4_subset_1(A_2344, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_2344, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_2344, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1(A_2344, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_2344, '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2344)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2344)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_2344))), inference(resolution, [status(thm)], [c_82, c_47655])).
% 21.41/11.42  tff(c_47672, plain, (![A_2344]: (k2_partfun1(k4_subset_1(A_2344, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_2344, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_2344, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_2344, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_2344, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2344)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2344)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_2344))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_33872, c_47662])).
% 21.41/11.42  tff(c_49132, plain, (![A_2377]: (k2_partfun1(k4_subset_1(A_2377, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_2377, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_2377, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_2377, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_2377, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2377)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2377)) | v1_xboole_0(A_2377))), inference(negUnitSimplification, [status(thm)], [c_96, c_47672])).
% 21.41/11.42  tff(c_30894, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')='#skF_7'), inference(splitRight, [status(thm)], [c_7591])).
% 21.41/11.42  tff(c_35754, plain, (![D_1969, C_1968, B_1971, G_1970, A_1967]: (k1_tmap_1(A_1967, B_1971, C_1968, D_1969, k2_partfun1(k4_subset_1(A_1967, C_1968, D_1969), B_1971, G_1970, C_1968), k2_partfun1(k4_subset_1(A_1967, C_1968, D_1969), B_1971, G_1970, D_1969))=G_1970 | ~m1_subset_1(G_1970, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1967, C_1968, D_1969), B_1971))) | ~v1_funct_2(G_1970, k4_subset_1(A_1967, C_1968, D_1969), B_1971) | ~v1_funct_1(G_1970) | k2_partfun1(D_1969, B_1971, k2_partfun1(k4_subset_1(A_1967, C_1968, D_1969), B_1971, G_1970, D_1969), k9_subset_1(A_1967, C_1968, D_1969))!=k2_partfun1(C_1968, B_1971, k2_partfun1(k4_subset_1(A_1967, C_1968, D_1969), B_1971, G_1970, C_1968), k9_subset_1(A_1967, C_1968, D_1969)) | ~m1_subset_1(k2_partfun1(k4_subset_1(A_1967, C_1968, D_1969), B_1971, G_1970, D_1969), k1_zfmisc_1(k2_zfmisc_1(D_1969, B_1971))) | ~v1_funct_2(k2_partfun1(k4_subset_1(A_1967, C_1968, D_1969), B_1971, G_1970, D_1969), D_1969, B_1971) | ~v1_funct_1(k2_partfun1(k4_subset_1(A_1967, C_1968, D_1969), B_1971, G_1970, D_1969)) | ~m1_subset_1(k2_partfun1(k4_subset_1(A_1967, C_1968, D_1969), B_1971, G_1970, C_1968), k1_zfmisc_1(k2_zfmisc_1(C_1968, B_1971))) | ~v1_funct_2(k2_partfun1(k4_subset_1(A_1967, C_1968, D_1969), B_1971, G_1970, C_1968), C_1968, B_1971) | ~v1_funct_1(k2_partfun1(k4_subset_1(A_1967, C_1968, D_1969), B_1971, G_1970, C_1968)) | ~m1_subset_1(D_1969, k1_zfmisc_1(A_1967)) | v1_xboole_0(D_1969) | ~m1_subset_1(C_1968, k1_zfmisc_1(A_1967)) | v1_xboole_0(C_1968) | v1_xboole_0(B_1971) | v1_xboole_0(A_1967))), inference(cnfTransformation, [status(thm)], [f_195])).
% 21.41/11.42  tff(c_35756, plain, (k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5'))=k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7') | ~m1_subset_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3'))) | ~v1_funct_2(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3') | ~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k2_partfun1('#skF_5', '#skF_3', k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5'), k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), k9_subset_1('#skF_2', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3'))) | ~v1_funct_2(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5'), '#skF_5', '#skF_3') | ~v1_funct_1(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')) | ~m1_subset_1(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_30894, c_35754])).
% 21.41/11.42  tff(c_35758, plain, (k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), '#skF_7')=k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7') | ~m1_subset_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3'))) | ~v1_funct_2(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3') | ~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k2_partfun1('#skF_4', '#skF_3', k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), k1_xboole_0)!=k1_xboole_0 | ~m1_subset_1(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')) | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_90, c_80, c_30894, c_78, c_30894, c_76, c_35485, c_33869, c_30894, c_34733, c_33078, c_34733, c_33078, c_30894, c_35756])).
% 21.41/11.42  tff(c_35759, plain, (k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), '#skF_7')=k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7') | ~m1_subset_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3'))) | ~v1_funct_2(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3') | ~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k2_partfun1('#skF_4', '#skF_3', k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), k1_xboole_0)!=k1_xboole_0 | ~m1_subset_1(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_100, c_98, c_96, c_92, c_35758])).
% 21.41/11.42  tff(c_38471, plain, (k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), '#skF_7')=k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7') | ~m1_subset_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3'))) | ~v1_funct_2(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3') | k2_partfun1('#skF_4', '#skF_3', k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), k1_xboole_0)!=k1_xboole_0 | ~m1_subset_1(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36532, c_35759])).
% 21.41/11.42  tff(c_38472, plain, (~v1_funct_1(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'))), inference(splitLeft, [status(thm)], [c_38471])).
% 21.41/11.42  tff(c_49141, plain, (~v1_funct_1('#skF_6') | ~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_49132, c_38472])).
% 21.41/11.42  tff(c_49154, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_90, c_35485, c_35148, c_34733, c_33078, c_34733, c_33078, c_36532, c_86, c_49141])).
% 21.41/11.42  tff(c_49156, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_49154])).
% 21.41/11.42  tff(c_49157, plain, (~v1_funct_2(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), '#skF_4', '#skF_3') | ~m1_subset_1(k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | k2_partfun1('#skF_4', '#skF_3', k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), k1_xboole_0)!=k1_xboole_0 | ~v1_funct_2(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3') | ~m1_subset_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3'))) | k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4'), '#skF_7')=k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_38471])).
% 21.41/11.43  tff(c_49516, plain, (~m1_subset_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3')))), inference(splitLeft, [status(thm)], [c_49157])).
% 21.41/11.43  tff(c_49519, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3'))) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_49516])).
% 21.41/11.43  tff(c_49522, plain, (v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_90, c_86, c_84, c_82, c_80, c_78, c_76, c_49519])).
% 21.41/11.43  tff(c_49524, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_98, c_96, c_92, c_49522])).
% 21.41/11.43  tff(c_49526, plain, (m1_subset_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3')))), inference(splitRight, [status(thm)], [c_49157])).
% 21.41/11.43  tff(c_66, plain, (![C_144, A_48, D_160, E_168, F_172, B_112]: (k2_partfun1(k4_subset_1(A_48, C_144, D_160), B_112, k1_tmap_1(A_48, B_112, C_144, D_160, E_168, F_172), C_144)=E_168 | ~m1_subset_1(k1_tmap_1(A_48, B_112, C_144, D_160, E_168, F_172), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_48, C_144, D_160), B_112))) | ~v1_funct_2(k1_tmap_1(A_48, B_112, C_144, D_160, E_168, F_172), k4_subset_1(A_48, C_144, D_160), B_112) | ~v1_funct_1(k1_tmap_1(A_48, B_112, C_144, D_160, E_168, F_172)) | k2_partfun1(D_160, B_112, F_172, k9_subset_1(A_48, C_144, D_160))!=k2_partfun1(C_144, B_112, E_168, k9_subset_1(A_48, C_144, D_160)) | ~m1_subset_1(F_172, k1_zfmisc_1(k2_zfmisc_1(D_160, B_112))) | ~v1_funct_2(F_172, D_160, B_112) | ~v1_funct_1(F_172) | ~m1_subset_1(E_168, k1_zfmisc_1(k2_zfmisc_1(C_144, B_112))) | ~v1_funct_2(E_168, C_144, B_112) | ~v1_funct_1(E_168) | ~m1_subset_1(D_160, k1_zfmisc_1(A_48)) | v1_xboole_0(D_160) | ~m1_subset_1(C_144, k1_zfmisc_1(A_48)) | v1_xboole_0(C_144) | v1_xboole_0(B_112) | v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_195])).
% 21.41/11.43  tff(c_49534, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | ~v1_funct_2(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3') | ~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3'))) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_49526, c_66])).
% 21.41/11.43  tff(c_49568, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | ~v1_funct_2(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3') | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_90, c_86, c_84, c_82, c_80, c_78, c_76, c_35148, c_34733, c_33078, c_35485, c_34733, c_33078, c_33872, c_33869, c_36532, c_49534])).
% 21.41/11.43  tff(c_49569, plain, (~v1_funct_2(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_100, c_98, c_96, c_92, c_30893, c_49568])).
% 21.41/11.43  tff(c_49605, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3'))) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_70, c_49569])).
% 21.41/11.43  tff(c_49608, plain, (v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_90, c_86, c_84, c_82, c_80, c_78, c_76, c_49605])).
% 21.41/11.43  tff(c_49610, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_98, c_96, c_92, c_49608])).
% 21.41/11.43  tff(c_49611, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_7679])).
% 21.41/11.43  tff(c_49612, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_7679])).
% 21.41/11.43  tff(c_49629, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_49611, c_49612])).
% 21.41/11.43  tff(c_61924, plain, (![C_3113, A_3114, B_3115]: (v4_relat_1(C_3113, A_3114) | ~m1_subset_1(C_3113, k1_zfmisc_1(k2_zfmisc_1(A_3114, B_3115))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 21.41/11.43  tff(c_61932, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_82, c_61924])).
% 21.41/11.43  tff(c_64925, plain, (![B_3315, A_3316]: (k1_relat_1(B_3315)=A_3316 | ~v1_partfun1(B_3315, A_3316) | ~v4_relat_1(B_3315, A_3316) | ~v1_relat_1(B_3315))), inference(cnfTransformation, [status(thm)], [f_141])).
% 21.41/11.43  tff(c_64931, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_61932, c_64925])).
% 21.41/11.43  tff(c_64940, plain, ('#skF_6'='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7644, c_49629, c_64931])).
% 21.41/11.43  tff(c_64944, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_64940])).
% 21.41/11.43  tff(c_65991, plain, (![C_3384, A_3385, B_3386]: (v1_partfun1(C_3384, A_3385) | ~v1_funct_2(C_3384, A_3385, B_3386) | ~v1_funct_1(C_3384) | ~m1_subset_1(C_3384, k1_zfmisc_1(k2_zfmisc_1(A_3385, B_3386))) | v1_xboole_0(B_3386))), inference(cnfTransformation, [status(thm)], [f_133])).
% 21.41/11.43  tff(c_65997, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_82, c_65991])).
% 21.41/11.43  tff(c_66004, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_65997])).
% 21.41/11.43  tff(c_66006, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_64944, c_66004])).
% 21.41/11.43  tff(c_66007, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_64940])).
% 21.41/11.43  tff(c_49624, plain, (![A_3]: (r1_tarski('#skF_6', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_49611, c_6])).
% 21.41/11.43  tff(c_66046, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_66007, c_49624])).
% 21.41/11.43  tff(c_49623, plain, (k2_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_49611, c_49611, c_26])).
% 21.41/11.43  tff(c_49641, plain, (![A_2395]: (k9_relat_1(A_2395, k1_relat_1(A_2395))=k2_relat_1(A_2395) | ~v1_relat_1(A_2395))), inference(cnfTransformation, [status(thm)], [f_52])).
% 21.41/11.43  tff(c_49650, plain, (k9_relat_1('#skF_6', '#skF_6')=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_49629, c_49641])).
% 21.41/11.43  tff(c_49654, plain, (k9_relat_1('#skF_6', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_7644, c_49623, c_49650])).
% 21.41/11.43  tff(c_66043, plain, (k9_relat_1('#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_66007, c_66007, c_66007, c_49654])).
% 21.41/11.43  tff(c_62028, plain, (![B_3124, A_3125]: (k7_relat_1(B_3124, A_3125)='#skF_6' | ~r1_xboole_0(k1_relat_1(B_3124), A_3125) | ~v1_relat_1(B_3124))), inference(demodulation, [status(thm), theory('equality')], [c_49611, c_34])).
% 21.41/11.43  tff(c_62035, plain, (![A_3125]: (k7_relat_1('#skF_6', A_3125)='#skF_6' | ~r1_xboole_0('#skF_6', A_3125) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_49629, c_62028])).
% 21.41/11.43  tff(c_62038, plain, (![A_3125]: (k7_relat_1('#skF_6', A_3125)='#skF_6' | ~r1_xboole_0('#skF_6', A_3125))), inference(demodulation, [status(thm), theory('equality')], [c_7644, c_62035])).
% 21.41/11.43  tff(c_66535, plain, (![A_3437]: (k7_relat_1('#skF_4', A_3437)='#skF_4' | ~r1_xboole_0('#skF_4', A_3437))), inference(demodulation, [status(thm), theory('equality')], [c_66007, c_66007, c_66007, c_62038])).
% 21.41/11.43  tff(c_66546, plain, (![B_29]: (k7_relat_1('#skF_4', B_29)='#skF_4' | ~r1_subset_1('#skF_4', B_29) | v1_xboole_0(B_29) | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_66535])).
% 21.41/11.43  tff(c_66593, plain, (![B_3439]: (k7_relat_1('#skF_4', B_3439)='#skF_4' | ~r1_subset_1('#skF_4', B_3439) | v1_xboole_0(B_3439))), inference(negUnitSimplification, [status(thm)], [c_96, c_66546])).
% 21.41/11.43  tff(c_66596, plain, (k7_relat_1('#skF_4', '#skF_5')='#skF_4' | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_88, c_66593])).
% 21.41/11.43  tff(c_66599, plain, (k7_relat_1('#skF_4', '#skF_5')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_92, c_66596])).
% 21.41/11.43  tff(c_62074, plain, (![B_3129, A_3130]: (r1_xboole_0(k1_relat_1(B_3129), A_3130) | k7_relat_1(B_3129, A_3130)!='#skF_6' | ~v1_relat_1(B_3129))), inference(demodulation, [status(thm), theory('equality')], [c_49611, c_36])).
% 21.41/11.43  tff(c_62094, plain, (![A_3130]: (r1_xboole_0('#skF_6', A_3130) | k7_relat_1('#skF_6', A_3130)!='#skF_6' | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_49629, c_62074])).
% 21.41/11.43  tff(c_62101, plain, (![A_3130]: (r1_xboole_0('#skF_6', A_3130) | k7_relat_1('#skF_6', A_3130)!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_7644, c_62094])).
% 21.41/11.43  tff(c_66019, plain, (![A_3130]: (r1_xboole_0('#skF_4', A_3130) | k7_relat_1('#skF_4', A_3130)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66007, c_66007, c_66007, c_62101])).
% 21.41/11.43  tff(c_61931, plain, (v4_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_76, c_61924])).
% 21.41/11.43  tff(c_64934, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_61931, c_64925])).
% 21.41/11.43  tff(c_64943, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7643, c_64934])).
% 21.41/11.43  tff(c_66124, plain, (~v1_partfun1('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_64943])).
% 21.41/11.43  tff(c_66342, plain, (![C_3414, A_3415, B_3416]: (v1_partfun1(C_3414, A_3415) | ~v1_funct_2(C_3414, A_3415, B_3416) | ~v1_funct_1(C_3414) | ~m1_subset_1(C_3414, k1_zfmisc_1(k2_zfmisc_1(A_3415, B_3416))) | v1_xboole_0(B_3416))), inference(cnfTransformation, [status(thm)], [f_133])).
% 21.41/11.43  tff(c_66348, plain, (v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_76, c_66342])).
% 21.41/11.43  tff(c_66355, plain, (v1_partfun1('#skF_7', '#skF_5') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_66348])).
% 21.41/11.43  tff(c_66357, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_66124, c_66355])).
% 21.41/11.43  tff(c_66358, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitRight, [status(thm)], [c_64943])).
% 21.41/11.43  tff(c_61933, plain, (![A_22, B_24]: (k7_relat_1(A_22, B_24)='#skF_6' | ~r1_xboole_0(B_24, k1_relat_1(A_22)) | ~v1_relat_1(A_22))), inference(demodulation, [status(thm), theory('equality')], [c_49611, c_24])).
% 21.41/11.43  tff(c_67311, plain, (![A_3511, B_3512]: (k7_relat_1(A_3511, B_3512)='#skF_4' | ~r1_xboole_0(B_3512, k1_relat_1(A_3511)) | ~v1_relat_1(A_3511))), inference(demodulation, [status(thm), theory('equality')], [c_66007, c_61933])).
% 21.41/11.43  tff(c_67338, plain, (![B_3512]: (k7_relat_1('#skF_7', B_3512)='#skF_4' | ~r1_xboole_0(B_3512, '#skF_5') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_66358, c_67311])).
% 21.41/11.43  tff(c_67357, plain, (![B_3513]: (k7_relat_1('#skF_7', B_3513)='#skF_4' | ~r1_xboole_0(B_3513, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_7643, c_67338])).
% 21.41/11.43  tff(c_67369, plain, (k7_relat_1('#skF_7', '#skF_4')='#skF_4' | k7_relat_1('#skF_4', '#skF_5')!='#skF_4'), inference(resolution, [status(thm)], [c_66019, c_67357])).
% 21.41/11.43  tff(c_67391, plain, (k7_relat_1('#skF_7', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_66599, c_67369])).
% 21.41/11.43  tff(c_67411, plain, (![B_20]: (k9_relat_1('#skF_7', B_20)=k9_relat_1('#skF_4', B_20) | ~r1_tarski(B_20, '#skF_4') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_67391, c_22])).
% 21.41/11.43  tff(c_67604, plain, (![B_3519]: (k9_relat_1('#skF_7', B_3519)=k9_relat_1('#skF_4', B_3519) | ~r1_tarski(B_3519, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7643, c_67411])).
% 21.41/11.43  tff(c_67608, plain, (k9_relat_1('#skF_7', '#skF_4')=k9_relat_1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_66046, c_67604])).
% 21.41/11.43  tff(c_67610, plain, (k9_relat_1('#skF_7', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_66043, c_67608])).
% 21.41/11.43  tff(c_66054, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66007, c_86])).
% 21.41/11.43  tff(c_66053, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66007, c_84])).
% 21.41/11.43  tff(c_66052, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_66007, c_82])).
% 21.41/11.43  tff(c_66937, plain, (![A_3468, D_3467, B_3471, E_3470, F_3469, C_3466]: (m1_subset_1(k1_tmap_1(A_3468, B_3471, C_3466, D_3467, E_3470, F_3469), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_3468, C_3466, D_3467), B_3471))) | ~m1_subset_1(F_3469, k1_zfmisc_1(k2_zfmisc_1(D_3467, B_3471))) | ~v1_funct_2(F_3469, D_3467, B_3471) | ~v1_funct_1(F_3469) | ~m1_subset_1(E_3470, k1_zfmisc_1(k2_zfmisc_1(C_3466, B_3471))) | ~v1_funct_2(E_3470, C_3466, B_3471) | ~v1_funct_1(E_3470) | ~m1_subset_1(D_3467, k1_zfmisc_1(A_3468)) | v1_xboole_0(D_3467) | ~m1_subset_1(C_3466, k1_zfmisc_1(A_3468)) | v1_xboole_0(C_3466) | v1_xboole_0(B_3471) | v1_xboole_0(A_3468))), inference(cnfTransformation, [status(thm)], [f_229])).
% 21.41/11.43  tff(c_42, plain, (![C_32, A_30, B_31]: (v1_relat_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 21.41/11.43  tff(c_68297, plain, (![F_3556, E_3555, A_3559, B_3560, C_3557, D_3558]: (v1_relat_1(k1_tmap_1(A_3559, B_3560, C_3557, D_3558, E_3555, F_3556)) | ~m1_subset_1(F_3556, k1_zfmisc_1(k2_zfmisc_1(D_3558, B_3560))) | ~v1_funct_2(F_3556, D_3558, B_3560) | ~v1_funct_1(F_3556) | ~m1_subset_1(E_3555, k1_zfmisc_1(k2_zfmisc_1(C_3557, B_3560))) | ~v1_funct_2(E_3555, C_3557, B_3560) | ~v1_funct_1(E_3555) | ~m1_subset_1(D_3558, k1_zfmisc_1(A_3559)) | v1_xboole_0(D_3558) | ~m1_subset_1(C_3557, k1_zfmisc_1(A_3559)) | v1_xboole_0(C_3557) | v1_xboole_0(B_3560) | v1_xboole_0(A_3559))), inference(resolution, [status(thm)], [c_66937, c_42])).
% 21.41/11.43  tff(c_68303, plain, (![A_3559, C_3557, E_3555]: (v1_relat_1(k1_tmap_1(A_3559, '#skF_3', C_3557, '#skF_5', E_3555, '#skF_7')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_3555, k1_zfmisc_1(k2_zfmisc_1(C_3557, '#skF_3'))) | ~v1_funct_2(E_3555, C_3557, '#skF_3') | ~v1_funct_1(E_3555) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3559)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_3557, k1_zfmisc_1(A_3559)) | v1_xboole_0(C_3557) | v1_xboole_0('#skF_3') | v1_xboole_0(A_3559))), inference(resolution, [status(thm)], [c_76, c_68297])).
% 21.41/11.43  tff(c_68311, plain, (![A_3559, C_3557, E_3555]: (v1_relat_1(k1_tmap_1(A_3559, '#skF_3', C_3557, '#skF_5', E_3555, '#skF_7')) | ~m1_subset_1(E_3555, k1_zfmisc_1(k2_zfmisc_1(C_3557, '#skF_3'))) | ~v1_funct_2(E_3555, C_3557, '#skF_3') | ~v1_funct_1(E_3555) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3559)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_3557, k1_zfmisc_1(A_3559)) | v1_xboole_0(C_3557) | v1_xboole_0('#skF_3') | v1_xboole_0(A_3559))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_68303])).
% 21.41/11.43  tff(c_68448, plain, (![A_3572, C_3573, E_3574]: (v1_relat_1(k1_tmap_1(A_3572, '#skF_3', C_3573, '#skF_5', E_3574, '#skF_7')) | ~m1_subset_1(E_3574, k1_zfmisc_1(k2_zfmisc_1(C_3573, '#skF_3'))) | ~v1_funct_2(E_3574, C_3573, '#skF_3') | ~v1_funct_1(E_3574) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3572)) | ~m1_subset_1(C_3573, k1_zfmisc_1(A_3572)) | v1_xboole_0(C_3573) | v1_xboole_0(A_3572))), inference(negUnitSimplification, [status(thm)], [c_98, c_92, c_68311])).
% 21.41/11.43  tff(c_68453, plain, (![A_3572]: (v1_relat_1(k1_tmap_1(A_3572, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~v1_funct_2('#skF_4', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3572)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3572)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_3572))), inference(resolution, [status(thm)], [c_66052, c_68448])).
% 21.41/11.43  tff(c_68461, plain, (![A_3572]: (v1_relat_1(k1_tmap_1(A_3572, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3572)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3572)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_3572))), inference(demodulation, [status(thm), theory('equality')], [c_66054, c_66053, c_68453])).
% 21.41/11.43  tff(c_68895, plain, (![A_3598]: (v1_relat_1(k1_tmap_1(A_3598, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3598)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3598)) | v1_xboole_0(A_3598))), inference(negUnitSimplification, [status(thm)], [c_96, c_68461])).
% 21.41/11.43  tff(c_68898, plain, (v1_relat_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_90, c_68895])).
% 21.41/11.43  tff(c_68901, plain, (v1_relat_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_68898])).
% 21.41/11.43  tff(c_68902, plain, (v1_relat_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_100, c_68901])).
% 21.41/11.43  tff(c_66676, plain, (![A_3446, B_3449, D_3445, E_3448, F_3447, C_3444]: (v1_funct_1(k1_tmap_1(A_3446, B_3449, C_3444, D_3445, E_3448, F_3447)) | ~m1_subset_1(F_3447, k1_zfmisc_1(k2_zfmisc_1(D_3445, B_3449))) | ~v1_funct_2(F_3447, D_3445, B_3449) | ~v1_funct_1(F_3447) | ~m1_subset_1(E_3448, k1_zfmisc_1(k2_zfmisc_1(C_3444, B_3449))) | ~v1_funct_2(E_3448, C_3444, B_3449) | ~v1_funct_1(E_3448) | ~m1_subset_1(D_3445, k1_zfmisc_1(A_3446)) | v1_xboole_0(D_3445) | ~m1_subset_1(C_3444, k1_zfmisc_1(A_3446)) | v1_xboole_0(C_3444) | v1_xboole_0(B_3449) | v1_xboole_0(A_3446))), inference(cnfTransformation, [status(thm)], [f_229])).
% 21.41/11.43  tff(c_66680, plain, (![A_3446, C_3444, E_3448]: (v1_funct_1(k1_tmap_1(A_3446, '#skF_3', C_3444, '#skF_5', E_3448, '#skF_7')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_3448, k1_zfmisc_1(k2_zfmisc_1(C_3444, '#skF_3'))) | ~v1_funct_2(E_3448, C_3444, '#skF_3') | ~v1_funct_1(E_3448) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3446)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_3444, k1_zfmisc_1(A_3446)) | v1_xboole_0(C_3444) | v1_xboole_0('#skF_3') | v1_xboole_0(A_3446))), inference(resolution, [status(thm)], [c_76, c_66676])).
% 21.41/11.43  tff(c_66687, plain, (![A_3446, C_3444, E_3448]: (v1_funct_1(k1_tmap_1(A_3446, '#skF_3', C_3444, '#skF_5', E_3448, '#skF_7')) | ~m1_subset_1(E_3448, k1_zfmisc_1(k2_zfmisc_1(C_3444, '#skF_3'))) | ~v1_funct_2(E_3448, C_3444, '#skF_3') | ~v1_funct_1(E_3448) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3446)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_3444, k1_zfmisc_1(A_3446)) | v1_xboole_0(C_3444) | v1_xboole_0('#skF_3') | v1_xboole_0(A_3446))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_66680])).
% 21.41/11.43  tff(c_67096, plain, (![A_3486, C_3487, E_3488]: (v1_funct_1(k1_tmap_1(A_3486, '#skF_3', C_3487, '#skF_5', E_3488, '#skF_7')) | ~m1_subset_1(E_3488, k1_zfmisc_1(k2_zfmisc_1(C_3487, '#skF_3'))) | ~v1_funct_2(E_3488, C_3487, '#skF_3') | ~v1_funct_1(E_3488) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3486)) | ~m1_subset_1(C_3487, k1_zfmisc_1(A_3486)) | v1_xboole_0(C_3487) | v1_xboole_0(A_3486))), inference(negUnitSimplification, [status(thm)], [c_98, c_92, c_66687])).
% 21.41/11.43  tff(c_67101, plain, (![A_3486]: (v1_funct_1(k1_tmap_1(A_3486, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~v1_funct_2('#skF_4', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3486)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3486)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_3486))), inference(resolution, [status(thm)], [c_66052, c_67096])).
% 21.41/11.43  tff(c_67109, plain, (![A_3486]: (v1_funct_1(k1_tmap_1(A_3486, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3486)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3486)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_3486))), inference(demodulation, [status(thm), theory('equality')], [c_66054, c_66053, c_67101])).
% 21.41/11.43  tff(c_67897, plain, (![A_3533]: (v1_funct_1(k1_tmap_1(A_3533, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3533)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3533)) | v1_xboole_0(A_3533))), inference(negUnitSimplification, [status(thm)], [c_96, c_67109])).
% 21.41/11.43  tff(c_67900, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_90, c_67897])).
% 21.41/11.43  tff(c_67903, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_67900])).
% 21.41/11.43  tff(c_67904, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_100, c_67903])).
% 21.41/11.43  tff(c_60, plain, (![A_44, B_45, C_46, D_47]: (k2_partfun1(A_44, B_45, C_46, D_47)=k7_relat_1(C_46, D_47) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))) | ~v1_funct_1(C_46))), inference(cnfTransformation, [status(thm)], [f_147])).
% 21.41/11.43  tff(c_69408, plain, (![F_3620, D_3622, E_3619, D_3623, B_3625, C_3621, A_3624]: (k2_partfun1(k4_subset_1(A_3624, C_3621, D_3623), B_3625, k1_tmap_1(A_3624, B_3625, C_3621, D_3623, E_3619, F_3620), D_3622)=k7_relat_1(k1_tmap_1(A_3624, B_3625, C_3621, D_3623, E_3619, F_3620), D_3622) | ~v1_funct_1(k1_tmap_1(A_3624, B_3625, C_3621, D_3623, E_3619, F_3620)) | ~m1_subset_1(F_3620, k1_zfmisc_1(k2_zfmisc_1(D_3623, B_3625))) | ~v1_funct_2(F_3620, D_3623, B_3625) | ~v1_funct_1(F_3620) | ~m1_subset_1(E_3619, k1_zfmisc_1(k2_zfmisc_1(C_3621, B_3625))) | ~v1_funct_2(E_3619, C_3621, B_3625) | ~v1_funct_1(E_3619) | ~m1_subset_1(D_3623, k1_zfmisc_1(A_3624)) | v1_xboole_0(D_3623) | ~m1_subset_1(C_3621, k1_zfmisc_1(A_3624)) | v1_xboole_0(C_3621) | v1_xboole_0(B_3625) | v1_xboole_0(A_3624))), inference(resolution, [status(thm)], [c_66937, c_60])).
% 21.41/11.43  tff(c_69414, plain, (![A_3624, C_3621, E_3619, D_3622]: (k2_partfun1(k4_subset_1(A_3624, C_3621, '#skF_5'), '#skF_3', k1_tmap_1(A_3624, '#skF_3', C_3621, '#skF_5', E_3619, '#skF_7'), D_3622)=k7_relat_1(k1_tmap_1(A_3624, '#skF_3', C_3621, '#skF_5', E_3619, '#skF_7'), D_3622) | ~v1_funct_1(k1_tmap_1(A_3624, '#skF_3', C_3621, '#skF_5', E_3619, '#skF_7')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_3619, k1_zfmisc_1(k2_zfmisc_1(C_3621, '#skF_3'))) | ~v1_funct_2(E_3619, C_3621, '#skF_3') | ~v1_funct_1(E_3619) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3624)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_3621, k1_zfmisc_1(A_3624)) | v1_xboole_0(C_3621) | v1_xboole_0('#skF_3') | v1_xboole_0(A_3624))), inference(resolution, [status(thm)], [c_76, c_69408])).
% 21.41/11.43  tff(c_69422, plain, (![A_3624, C_3621, E_3619, D_3622]: (k2_partfun1(k4_subset_1(A_3624, C_3621, '#skF_5'), '#skF_3', k1_tmap_1(A_3624, '#skF_3', C_3621, '#skF_5', E_3619, '#skF_7'), D_3622)=k7_relat_1(k1_tmap_1(A_3624, '#skF_3', C_3621, '#skF_5', E_3619, '#skF_7'), D_3622) | ~v1_funct_1(k1_tmap_1(A_3624, '#skF_3', C_3621, '#skF_5', E_3619, '#skF_7')) | ~m1_subset_1(E_3619, k1_zfmisc_1(k2_zfmisc_1(C_3621, '#skF_3'))) | ~v1_funct_2(E_3619, C_3621, '#skF_3') | ~v1_funct_1(E_3619) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3624)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_3621, k1_zfmisc_1(A_3624)) | v1_xboole_0(C_3621) | v1_xboole_0('#skF_3') | v1_xboole_0(A_3624))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_69414])).
% 21.41/11.43  tff(c_70176, plain, (![A_3701, C_3702, E_3703, D_3704]: (k2_partfun1(k4_subset_1(A_3701, C_3702, '#skF_5'), '#skF_3', k1_tmap_1(A_3701, '#skF_3', C_3702, '#skF_5', E_3703, '#skF_7'), D_3704)=k7_relat_1(k1_tmap_1(A_3701, '#skF_3', C_3702, '#skF_5', E_3703, '#skF_7'), D_3704) | ~v1_funct_1(k1_tmap_1(A_3701, '#skF_3', C_3702, '#skF_5', E_3703, '#skF_7')) | ~m1_subset_1(E_3703, k1_zfmisc_1(k2_zfmisc_1(C_3702, '#skF_3'))) | ~v1_funct_2(E_3703, C_3702, '#skF_3') | ~v1_funct_1(E_3703) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3701)) | ~m1_subset_1(C_3702, k1_zfmisc_1(A_3701)) | v1_xboole_0(C_3702) | v1_xboole_0(A_3701))), inference(negUnitSimplification, [status(thm)], [c_98, c_92, c_69422])).
% 21.41/11.43  tff(c_70181, plain, (![A_3701, D_3704]: (k2_partfun1(k4_subset_1(A_3701, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_3701, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), D_3704)=k7_relat_1(k1_tmap_1(A_3701, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), D_3704) | ~v1_funct_1(k1_tmap_1(A_3701, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~v1_funct_2('#skF_4', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3701)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3701)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_3701))), inference(resolution, [status(thm)], [c_66052, c_70176])).
% 21.41/11.43  tff(c_70189, plain, (![A_3701, D_3704]: (k2_partfun1(k4_subset_1(A_3701, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_3701, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), D_3704)=k7_relat_1(k1_tmap_1(A_3701, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), D_3704) | ~v1_funct_1(k1_tmap_1(A_3701, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3701)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3701)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_3701))), inference(demodulation, [status(thm), theory('equality')], [c_66054, c_66053, c_70181])).
% 21.41/11.43  tff(c_70332, plain, (![A_3719, D_3720]: (k2_partfun1(k4_subset_1(A_3719, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_3719, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), D_3720)=k7_relat_1(k1_tmap_1(A_3719, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), D_3720) | ~v1_funct_1(k1_tmap_1(A_3719, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3719)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3719)) | v1_xboole_0(A_3719))), inference(negUnitSimplification, [status(thm)], [c_96, c_70189])).
% 21.41/11.43  tff(c_49725, plain, (![C_2408, A_2409, B_2410]: (v4_relat_1(C_2408, A_2409) | ~m1_subset_1(C_2408, k1_zfmisc_1(k2_zfmisc_1(A_2409, B_2410))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 21.41/11.43  tff(c_49733, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_82, c_49725])).
% 21.41/11.43  tff(c_53185, plain, (![B_2645, A_2646]: (k1_relat_1(B_2645)=A_2646 | ~v1_partfun1(B_2645, A_2646) | ~v4_relat_1(B_2645, A_2646) | ~v1_relat_1(B_2645))), inference(cnfTransformation, [status(thm)], [f_141])).
% 21.41/11.43  tff(c_53191, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_49733, c_53185])).
% 21.41/11.43  tff(c_53200, plain, ('#skF_6'='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7644, c_49629, c_53191])).
% 21.41/11.43  tff(c_53204, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_53200])).
% 21.41/11.43  tff(c_53918, plain, (![C_2690, A_2691, B_2692]: (v1_partfun1(C_2690, A_2691) | ~v1_funct_2(C_2690, A_2691, B_2692) | ~v1_funct_1(C_2690) | ~m1_subset_1(C_2690, k1_zfmisc_1(k2_zfmisc_1(A_2691, B_2692))) | v1_xboole_0(B_2692))), inference(cnfTransformation, [status(thm)], [f_133])).
% 21.41/11.43  tff(c_53924, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_82, c_53918])).
% 21.41/11.43  tff(c_53931, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_53924])).
% 21.41/11.43  tff(c_53933, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_53204, c_53931])).
% 21.41/11.43  tff(c_53934, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_53200])).
% 21.41/11.43  tff(c_51297, plain, (![B_2520, A_2521]: (k7_relat_1(B_2520, A_2521)='#skF_6' | ~r1_xboole_0(k1_relat_1(B_2520), A_2521) | ~v1_relat_1(B_2520))), inference(demodulation, [status(thm), theory('equality')], [c_49611, c_34])).
% 21.41/11.43  tff(c_51308, plain, (![A_2521]: (k7_relat_1('#skF_6', A_2521)='#skF_6' | ~r1_xboole_0('#skF_6', A_2521) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_49629, c_51297])).
% 21.41/11.43  tff(c_51312, plain, (![A_2521]: (k7_relat_1('#skF_6', A_2521)='#skF_6' | ~r1_xboole_0('#skF_6', A_2521))), inference(demodulation, [status(thm), theory('equality')], [c_7644, c_51308])).
% 21.41/11.43  tff(c_54347, plain, (![A_2731]: (k7_relat_1('#skF_4', A_2731)='#skF_4' | ~r1_xboole_0('#skF_4', A_2731))), inference(demodulation, [status(thm), theory('equality')], [c_53934, c_53934, c_53934, c_51312])).
% 21.41/11.43  tff(c_54361, plain, (![B_29]: (k7_relat_1('#skF_4', B_29)='#skF_4' | ~r1_subset_1('#skF_4', B_29) | v1_xboole_0(B_29) | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_54347])).
% 21.41/11.43  tff(c_54368, plain, (![B_2732]: (k7_relat_1('#skF_4', B_2732)='#skF_4' | ~r1_subset_1('#skF_4', B_2732) | v1_xboole_0(B_2732))), inference(negUnitSimplification, [status(thm)], [c_96, c_54361])).
% 21.41/11.43  tff(c_54371, plain, (k7_relat_1('#skF_4', '#skF_5')='#skF_4' | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_88, c_54368])).
% 21.41/11.43  tff(c_54374, plain, (k7_relat_1('#skF_4', '#skF_5')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_92, c_54371])).
% 21.41/11.43  tff(c_51415, plain, (![B_2529, A_2530]: (r1_xboole_0(k1_relat_1(B_2529), A_2530) | k7_relat_1(B_2529, A_2530)!='#skF_6' | ~v1_relat_1(B_2529))), inference(demodulation, [status(thm), theory('equality')], [c_49611, c_36])).
% 21.41/11.43  tff(c_51427, plain, (![A_2530]: (r1_xboole_0('#skF_6', A_2530) | k7_relat_1('#skF_6', A_2530)!='#skF_6' | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_49629, c_51415])).
% 21.41/11.43  tff(c_51432, plain, (![A_2530]: (r1_xboole_0('#skF_6', A_2530) | k7_relat_1('#skF_6', A_2530)!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_7644, c_51427])).
% 21.41/11.43  tff(c_53956, plain, (![A_2530]: (r1_xboole_0('#skF_4', A_2530) | k7_relat_1('#skF_4', A_2530)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_53934, c_53934, c_53934, c_51432])).
% 21.41/11.43  tff(c_49732, plain, (v4_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_76, c_49725])).
% 21.41/11.43  tff(c_53194, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_49732, c_53185])).
% 21.41/11.43  tff(c_53203, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7643, c_53194])).
% 21.41/11.43  tff(c_54102, plain, (~v1_partfun1('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_53203])).
% 21.41/11.43  tff(c_54119, plain, (![C_2704, A_2705, B_2706]: (v1_partfun1(C_2704, A_2705) | ~v1_funct_2(C_2704, A_2705, B_2706) | ~v1_funct_1(C_2704) | ~m1_subset_1(C_2704, k1_zfmisc_1(k2_zfmisc_1(A_2705, B_2706))) | v1_xboole_0(B_2706))), inference(cnfTransformation, [status(thm)], [f_133])).
% 21.41/11.43  tff(c_54125, plain, (v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_76, c_54119])).
% 21.41/11.43  tff(c_54132, plain, (v1_partfun1('#skF_7', '#skF_5') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_54125])).
% 21.41/11.43  tff(c_54134, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_54102, c_54132])).
% 21.41/11.43  tff(c_54135, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitRight, [status(thm)], [c_53203])).
% 21.41/11.43  tff(c_52778, plain, (![A_22, B_24]: (k7_relat_1(A_22, B_24)='#skF_6' | ~r1_xboole_0(B_24, k1_relat_1(A_22)) | ~v1_relat_1(A_22))), inference(demodulation, [status(thm), theory('equality')], [c_49611, c_24])).
% 21.41/11.43  tff(c_54846, plain, (![A_2776, B_2777]: (k7_relat_1(A_2776, B_2777)='#skF_4' | ~r1_xboole_0(B_2777, k1_relat_1(A_2776)) | ~v1_relat_1(A_2776))), inference(demodulation, [status(thm), theory('equality')], [c_53934, c_52778])).
% 21.41/11.43  tff(c_54865, plain, (![B_2777]: (k7_relat_1('#skF_7', B_2777)='#skF_4' | ~r1_xboole_0(B_2777, '#skF_5') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_54135, c_54846])).
% 21.41/11.43  tff(c_54882, plain, (![B_2778]: (k7_relat_1('#skF_7', B_2778)='#skF_4' | ~r1_xboole_0(B_2778, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_7643, c_54865])).
% 21.41/11.43  tff(c_54886, plain, (k7_relat_1('#skF_7', '#skF_4')='#skF_4' | k7_relat_1('#skF_4', '#skF_5')!='#skF_4'), inference(resolution, [status(thm)], [c_53956, c_54882])).
% 21.41/11.43  tff(c_54905, plain, (k7_relat_1('#skF_7', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_54374, c_54886])).
% 21.41/11.43  tff(c_51339, plain, (![B_2524, A_2525]: (r1_xboole_0(k1_relat_1(B_2524), A_2525) | k9_relat_1(B_2524, A_2525)!='#skF_6' | ~v1_relat_1(B_2524))), inference(demodulation, [status(thm), theory('equality')], [c_49611, c_20])).
% 21.41/11.43  tff(c_51351, plain, (![A_2525]: (r1_xboole_0('#skF_6', A_2525) | k9_relat_1('#skF_6', A_2525)!='#skF_6' | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_49629, c_51339])).
% 21.41/11.43  tff(c_51357, plain, (![A_2526]: (r1_xboole_0('#skF_6', A_2526) | k9_relat_1('#skF_6', A_2526)!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_7644, c_51351])).
% 21.41/11.43  tff(c_51370, plain, (![A_2527]: (k7_relat_1('#skF_6', A_2527)='#skF_6' | k9_relat_1('#skF_6', A_2527)!='#skF_6')), inference(resolution, [status(thm)], [c_51357, c_51312])).
% 21.41/11.43  tff(c_51378, plain, (k7_relat_1('#skF_6', '#skF_6')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_49654, c_51370])).
% 21.41/11.43  tff(c_53960, plain, (k7_relat_1('#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_53934, c_53934, c_53934, c_51378])).
% 21.41/11.43  tff(c_54295, plain, (![A_2723]: (r1_xboole_0('#skF_4', A_2723) | k7_relat_1('#skF_4', A_2723)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_53934, c_53934, c_53934, c_51432])).
% 21.41/11.43  tff(c_49617, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)='#skF_6' | ~r1_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_49611, c_2])).
% 21.41/11.43  tff(c_53975, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)='#skF_4' | ~r1_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_53934, c_49617])).
% 21.41/11.43  tff(c_54432, plain, (![A_2735]: (k3_xboole_0('#skF_4', A_2735)='#skF_4' | k7_relat_1('#skF_4', A_2735)!='#skF_4')), inference(resolution, [status(thm)], [c_54295, c_53975])).
% 21.41/11.43  tff(c_54439, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_54374, c_54432])).
% 21.41/11.43  tff(c_53135, plain, (![A_2638, B_2639, C_2640]: (k9_subset_1(A_2638, B_2639, C_2640)=k3_xboole_0(B_2639, C_2640) | ~m1_subset_1(C_2640, k1_zfmisc_1(A_2638)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 21.41/11.43  tff(c_53147, plain, (![B_2639]: (k9_subset_1('#skF_2', B_2639, '#skF_5')=k3_xboole_0(B_2639, '#skF_5'))), inference(resolution, [status(thm)], [c_90, c_53135])).
% 21.41/11.43  tff(c_53989, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_53934, c_86])).
% 21.41/11.43  tff(c_53988, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_53934, c_84])).
% 21.41/11.43  tff(c_53987, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_53934, c_82])).
% 21.41/11.43  tff(c_54313, plain, (![B_2729, A_2726, D_2725, C_2724, F_2727, E_2728]: (v1_funct_1(k1_tmap_1(A_2726, B_2729, C_2724, D_2725, E_2728, F_2727)) | ~m1_subset_1(F_2727, k1_zfmisc_1(k2_zfmisc_1(D_2725, B_2729))) | ~v1_funct_2(F_2727, D_2725, B_2729) | ~v1_funct_1(F_2727) | ~m1_subset_1(E_2728, k1_zfmisc_1(k2_zfmisc_1(C_2724, B_2729))) | ~v1_funct_2(E_2728, C_2724, B_2729) | ~v1_funct_1(E_2728) | ~m1_subset_1(D_2725, k1_zfmisc_1(A_2726)) | v1_xboole_0(D_2725) | ~m1_subset_1(C_2724, k1_zfmisc_1(A_2726)) | v1_xboole_0(C_2724) | v1_xboole_0(B_2729) | v1_xboole_0(A_2726))), inference(cnfTransformation, [status(thm)], [f_229])).
% 21.41/11.43  tff(c_54317, plain, (![A_2726, C_2724, E_2728]: (v1_funct_1(k1_tmap_1(A_2726, '#skF_3', C_2724, '#skF_5', E_2728, '#skF_7')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_2728, k1_zfmisc_1(k2_zfmisc_1(C_2724, '#skF_3'))) | ~v1_funct_2(E_2728, C_2724, '#skF_3') | ~v1_funct_1(E_2728) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2726)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_2724, k1_zfmisc_1(A_2726)) | v1_xboole_0(C_2724) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2726))), inference(resolution, [status(thm)], [c_76, c_54313])).
% 21.41/11.43  tff(c_54324, plain, (![A_2726, C_2724, E_2728]: (v1_funct_1(k1_tmap_1(A_2726, '#skF_3', C_2724, '#skF_5', E_2728, '#skF_7')) | ~m1_subset_1(E_2728, k1_zfmisc_1(k2_zfmisc_1(C_2724, '#skF_3'))) | ~v1_funct_2(E_2728, C_2724, '#skF_3') | ~v1_funct_1(E_2728) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2726)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_2724, k1_zfmisc_1(A_2726)) | v1_xboole_0(C_2724) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2726))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_54317])).
% 21.41/11.43  tff(c_55043, plain, (![A_2787, C_2788, E_2789]: (v1_funct_1(k1_tmap_1(A_2787, '#skF_3', C_2788, '#skF_5', E_2789, '#skF_7')) | ~m1_subset_1(E_2789, k1_zfmisc_1(k2_zfmisc_1(C_2788, '#skF_3'))) | ~v1_funct_2(E_2789, C_2788, '#skF_3') | ~v1_funct_1(E_2789) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2787)) | ~m1_subset_1(C_2788, k1_zfmisc_1(A_2787)) | v1_xboole_0(C_2788) | v1_xboole_0(A_2787))), inference(negUnitSimplification, [status(thm)], [c_98, c_92, c_54324])).
% 21.41/11.43  tff(c_55048, plain, (![A_2787]: (v1_funct_1(k1_tmap_1(A_2787, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~v1_funct_2('#skF_4', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2787)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2787)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_2787))), inference(resolution, [status(thm)], [c_53987, c_55043])).
% 21.41/11.43  tff(c_55056, plain, (![A_2787]: (v1_funct_1(k1_tmap_1(A_2787, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2787)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2787)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_2787))), inference(demodulation, [status(thm), theory('equality')], [c_53989, c_53988, c_55048])).
% 21.41/11.43  tff(c_55625, plain, (![A_2819]: (v1_funct_1(k1_tmap_1(A_2819, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2819)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2819)) | v1_xboole_0(A_2819))), inference(negUnitSimplification, [status(thm)], [c_96, c_55056])).
% 21.41/11.43  tff(c_55628, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_90, c_55625])).
% 21.41/11.43  tff(c_55631, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_55628])).
% 21.41/11.43  tff(c_55632, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_100, c_55631])).
% 21.41/11.43  tff(c_54075, plain, (![D_47]: (k2_partfun1('#skF_4', '#skF_3', '#skF_4', D_47)=k7_relat_1('#skF_4', D_47) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_53987, c_60])).
% 21.41/11.43  tff(c_54092, plain, (![D_47]: (k2_partfun1('#skF_4', '#skF_3', '#skF_4', D_47)=k7_relat_1('#skF_4', D_47))), inference(demodulation, [status(thm), theory('equality')], [c_53989, c_54075])).
% 21.41/11.43  tff(c_54052, plain, (![A_2697, B_2698, C_2699, D_2700]: (k2_partfun1(A_2697, B_2698, C_2699, D_2700)=k7_relat_1(C_2699, D_2700) | ~m1_subset_1(C_2699, k1_zfmisc_1(k2_zfmisc_1(A_2697, B_2698))) | ~v1_funct_1(C_2699))), inference(cnfTransformation, [status(thm)], [f_147])).
% 21.41/11.43  tff(c_54054, plain, (![D_2700]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_2700)=k7_relat_1('#skF_7', D_2700) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_76, c_54052])).
% 21.41/11.43  tff(c_54057, plain, (![D_2700]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_2700)=k7_relat_1('#skF_7', D_2700))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_54054])).
% 21.41/11.43  tff(c_54753, plain, (![F_2761, A_2758, C_2759, B_2762, E_2757, D_2760]: (k2_partfun1(k4_subset_1(A_2758, C_2759, D_2760), B_2762, k1_tmap_1(A_2758, B_2762, C_2759, D_2760, E_2757, F_2761), D_2760)=F_2761 | ~m1_subset_1(k1_tmap_1(A_2758, B_2762, C_2759, D_2760, E_2757, F_2761), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_2758, C_2759, D_2760), B_2762))) | ~v1_funct_2(k1_tmap_1(A_2758, B_2762, C_2759, D_2760, E_2757, F_2761), k4_subset_1(A_2758, C_2759, D_2760), B_2762) | ~v1_funct_1(k1_tmap_1(A_2758, B_2762, C_2759, D_2760, E_2757, F_2761)) | k2_partfun1(D_2760, B_2762, F_2761, k9_subset_1(A_2758, C_2759, D_2760))!=k2_partfun1(C_2759, B_2762, E_2757, k9_subset_1(A_2758, C_2759, D_2760)) | ~m1_subset_1(F_2761, k1_zfmisc_1(k2_zfmisc_1(D_2760, B_2762))) | ~v1_funct_2(F_2761, D_2760, B_2762) | ~v1_funct_1(F_2761) | ~m1_subset_1(E_2757, k1_zfmisc_1(k2_zfmisc_1(C_2759, B_2762))) | ~v1_funct_2(E_2757, C_2759, B_2762) | ~v1_funct_1(E_2757) | ~m1_subset_1(D_2760, k1_zfmisc_1(A_2758)) | v1_xboole_0(D_2760) | ~m1_subset_1(C_2759, k1_zfmisc_1(A_2758)) | v1_xboole_0(C_2759) | v1_xboole_0(B_2762) | v1_xboole_0(A_2758))), inference(cnfTransformation, [status(thm)], [f_195])).
% 21.41/11.43  tff(c_57702, plain, (![C_2953, F_2956, B_2958, A_2955, E_2957, D_2954]: (k2_partfun1(k4_subset_1(A_2955, C_2953, D_2954), B_2958, k1_tmap_1(A_2955, B_2958, C_2953, D_2954, E_2957, F_2956), D_2954)=F_2956 | ~v1_funct_2(k1_tmap_1(A_2955, B_2958, C_2953, D_2954, E_2957, F_2956), k4_subset_1(A_2955, C_2953, D_2954), B_2958) | ~v1_funct_1(k1_tmap_1(A_2955, B_2958, C_2953, D_2954, E_2957, F_2956)) | k2_partfun1(D_2954, B_2958, F_2956, k9_subset_1(A_2955, C_2953, D_2954))!=k2_partfun1(C_2953, B_2958, E_2957, k9_subset_1(A_2955, C_2953, D_2954)) | ~m1_subset_1(F_2956, k1_zfmisc_1(k2_zfmisc_1(D_2954, B_2958))) | ~v1_funct_2(F_2956, D_2954, B_2958) | ~v1_funct_1(F_2956) | ~m1_subset_1(E_2957, k1_zfmisc_1(k2_zfmisc_1(C_2953, B_2958))) | ~v1_funct_2(E_2957, C_2953, B_2958) | ~v1_funct_1(E_2957) | ~m1_subset_1(D_2954, k1_zfmisc_1(A_2955)) | v1_xboole_0(D_2954) | ~m1_subset_1(C_2953, k1_zfmisc_1(A_2955)) | v1_xboole_0(C_2953) | v1_xboole_0(B_2958) | v1_xboole_0(A_2955))), inference(resolution, [status(thm)], [c_68, c_54753])).
% 21.41/11.43  tff(c_59811, plain, (![A_3049, E_3051, F_3050, D_3048, B_3052, C_3047]: (k2_partfun1(k4_subset_1(A_3049, C_3047, D_3048), B_3052, k1_tmap_1(A_3049, B_3052, C_3047, D_3048, E_3051, F_3050), D_3048)=F_3050 | ~v1_funct_1(k1_tmap_1(A_3049, B_3052, C_3047, D_3048, E_3051, F_3050)) | k2_partfun1(D_3048, B_3052, F_3050, k9_subset_1(A_3049, C_3047, D_3048))!=k2_partfun1(C_3047, B_3052, E_3051, k9_subset_1(A_3049, C_3047, D_3048)) | ~m1_subset_1(F_3050, k1_zfmisc_1(k2_zfmisc_1(D_3048, B_3052))) | ~v1_funct_2(F_3050, D_3048, B_3052) | ~v1_funct_1(F_3050) | ~m1_subset_1(E_3051, k1_zfmisc_1(k2_zfmisc_1(C_3047, B_3052))) | ~v1_funct_2(E_3051, C_3047, B_3052) | ~v1_funct_1(E_3051) | ~m1_subset_1(D_3048, k1_zfmisc_1(A_3049)) | v1_xboole_0(D_3048) | ~m1_subset_1(C_3047, k1_zfmisc_1(A_3049)) | v1_xboole_0(C_3047) | v1_xboole_0(B_3052) | v1_xboole_0(A_3049))), inference(resolution, [status(thm)], [c_70, c_57702])).
% 21.41/11.43  tff(c_59817, plain, (![A_3049, C_3047, E_3051]: (k2_partfun1(k4_subset_1(A_3049, C_3047, '#skF_5'), '#skF_3', k1_tmap_1(A_3049, '#skF_3', C_3047, '#skF_5', E_3051, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_3049, '#skF_3', C_3047, '#skF_5', E_3051, '#skF_7')) | k2_partfun1(C_3047, '#skF_3', E_3051, k9_subset_1(A_3049, C_3047, '#skF_5'))!=k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1(A_3049, C_3047, '#skF_5')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_3051, k1_zfmisc_1(k2_zfmisc_1(C_3047, '#skF_3'))) | ~v1_funct_2(E_3051, C_3047, '#skF_3') | ~v1_funct_1(E_3051) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3049)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_3047, k1_zfmisc_1(A_3049)) | v1_xboole_0(C_3047) | v1_xboole_0('#skF_3') | v1_xboole_0(A_3049))), inference(resolution, [status(thm)], [c_76, c_59811])).
% 21.41/11.43  tff(c_59825, plain, (![A_3049, C_3047, E_3051]: (k2_partfun1(k4_subset_1(A_3049, C_3047, '#skF_5'), '#skF_3', k1_tmap_1(A_3049, '#skF_3', C_3047, '#skF_5', E_3051, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_3049, '#skF_3', C_3047, '#skF_5', E_3051, '#skF_7')) | k2_partfun1(C_3047, '#skF_3', E_3051, k9_subset_1(A_3049, C_3047, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_3049, C_3047, '#skF_5')) | ~m1_subset_1(E_3051, k1_zfmisc_1(k2_zfmisc_1(C_3047, '#skF_3'))) | ~v1_funct_2(E_3051, C_3047, '#skF_3') | ~v1_funct_1(E_3051) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3049)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_3047, k1_zfmisc_1(A_3049)) | v1_xboole_0(C_3047) | v1_xboole_0('#skF_3') | v1_xboole_0(A_3049))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_54057, c_59817])).
% 21.41/11.43  tff(c_60660, plain, (![A_3069, C_3070, E_3071]: (k2_partfun1(k4_subset_1(A_3069, C_3070, '#skF_5'), '#skF_3', k1_tmap_1(A_3069, '#skF_3', C_3070, '#skF_5', E_3071, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_3069, '#skF_3', C_3070, '#skF_5', E_3071, '#skF_7')) | k2_partfun1(C_3070, '#skF_3', E_3071, k9_subset_1(A_3069, C_3070, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_3069, C_3070, '#skF_5')) | ~m1_subset_1(E_3071, k1_zfmisc_1(k2_zfmisc_1(C_3070, '#skF_3'))) | ~v1_funct_2(E_3071, C_3070, '#skF_3') | ~v1_funct_1(E_3071) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3069)) | ~m1_subset_1(C_3070, k1_zfmisc_1(A_3069)) | v1_xboole_0(C_3070) | v1_xboole_0(A_3069))), inference(negUnitSimplification, [status(thm)], [c_98, c_92, c_59825])).
% 21.41/11.43  tff(c_60665, plain, (![A_3069]: (k2_partfun1(k4_subset_1(A_3069, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_3069, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_3069, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | k2_partfun1('#skF_4', '#skF_3', '#skF_4', k9_subset_1(A_3069, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_3069, '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_4', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3069)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3069)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_3069))), inference(resolution, [status(thm)], [c_53987, c_60660])).
% 21.41/11.43  tff(c_60673, plain, (![A_3069]: (k2_partfun1(k4_subset_1(A_3069, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_3069, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_3069, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_3069, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_4', k9_subset_1(A_3069, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3069)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3069)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_3069))), inference(demodulation, [status(thm), theory('equality')], [c_53989, c_53988, c_54092, c_60665])).
% 21.41/11.43  tff(c_61834, plain, (![A_3100]: (k2_partfun1(k4_subset_1(A_3100, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_3100, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_3100, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_3100, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_4', k9_subset_1(A_3100, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3100)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3100)) | v1_xboole_0(A_3100))), inference(negUnitSimplification, [status(thm)], [c_96, c_60673])).
% 21.41/11.43  tff(c_49661, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')!='#skF_7'), inference(splitLeft, [status(thm)], [c_7591])).
% 21.41/11.43  tff(c_53971, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), '#skF_5')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_53934, c_49661])).
% 21.41/11.43  tff(c_61843, plain, (~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k7_relat_1('#skF_4', k9_subset_1('#skF_2', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_61834, c_53971])).
% 21.41/11.43  tff(c_61856, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_90, c_54905, c_53960, c_54439, c_54439, c_53147, c_53147, c_55632, c_61843])).
% 21.41/11.43  tff(c_61858, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_61856])).
% 21.41/11.43  tff(c_61860, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')='#skF_7'), inference(splitRight, [status(thm)], [c_7591])).
% 21.41/11.43  tff(c_66027, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), '#skF_5')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_66007, c_61860])).
% 21.41/11.43  tff(c_70341, plain, (k7_relat_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_70332, c_66027])).
% 21.41/11.43  tff(c_70356, plain, (k7_relat_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), '#skF_5')='#skF_7' | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_90, c_67904, c_70341])).
% 21.41/11.43  tff(c_70357, plain, (k7_relat_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), '#skF_5')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_100, c_70356])).
% 21.41/11.43  tff(c_70380, plain, (![B_20]: (k9_relat_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), B_20)=k9_relat_1('#skF_7', B_20) | ~r1_tarski(B_20, '#skF_5') | ~v1_relat_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_70357, c_22])).
% 21.41/11.43  tff(c_70408, plain, (![B_3727]: (k9_relat_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), B_3727)=k9_relat_1('#skF_7', B_3727) | ~r1_tarski(B_3727, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_68902, c_70380])).
% 21.41/11.43  tff(c_64892, plain, (![B_16, A_15]: (r1_xboole_0(k1_relat_1(B_16), A_15) | k9_relat_1(B_16, A_15)!='#skF_6' | ~v1_relat_1(B_16))), inference(demodulation, [status(thm), theory('equality')], [c_49611, c_20])).
% 21.41/11.43  tff(c_67646, plain, (![B_3521, A_3522]: (r1_xboole_0(k1_relat_1(B_3521), A_3522) | k9_relat_1(B_3521, A_3522)!='#skF_4' | ~v1_relat_1(B_3521))), inference(demodulation, [status(thm), theory('equality')], [c_66007, c_64892])).
% 21.41/11.43  tff(c_62027, plain, (![B_27, A_26]: (k7_relat_1(B_27, A_26)='#skF_6' | ~r1_xboole_0(k1_relat_1(B_27), A_26) | ~v1_relat_1(B_27))), inference(demodulation, [status(thm), theory('equality')], [c_49611, c_34])).
% 21.41/11.43  tff(c_66025, plain, (![B_27, A_26]: (k7_relat_1(B_27, A_26)='#skF_4' | ~r1_xboole_0(k1_relat_1(B_27), A_26) | ~v1_relat_1(B_27))), inference(demodulation, [status(thm), theory('equality')], [c_66007, c_62027])).
% 21.41/11.43  tff(c_67680, plain, (![B_3521, A_3522]: (k7_relat_1(B_3521, A_3522)='#skF_4' | k9_relat_1(B_3521, A_3522)!='#skF_4' | ~v1_relat_1(B_3521))), inference(resolution, [status(thm)], [c_67646, c_66025])).
% 21.41/11.43  tff(c_70417, plain, (![B_3727]: (k7_relat_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), B_3727)='#skF_4' | k9_relat_1('#skF_7', B_3727)!='#skF_4' | ~v1_relat_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~r1_tarski(B_3727, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_70408, c_67680])).
% 21.41/11.43  tff(c_70500, plain, (![B_3733]: (k7_relat_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), B_3733)='#skF_4' | k9_relat_1('#skF_7', B_3733)!='#skF_4' | ~r1_tarski(B_3733, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_68902, c_70417])).
% 21.41/11.43  tff(c_61859, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_7591])).
% 21.41/11.43  tff(c_66035, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_66007, c_66007, c_61859])).
% 21.41/11.43  tff(c_70338, plain, (k7_relat_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), '#skF_4')!='#skF_4' | ~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_70332, c_66035])).
% 21.41/11.43  tff(c_70353, plain, (k7_relat_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), '#skF_4')!='#skF_4' | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_90, c_67904, c_70338])).
% 21.41/11.43  tff(c_70354, plain, (k7_relat_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), '#skF_4')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_100, c_70353])).
% 21.41/11.43  tff(c_70509, plain, (k9_relat_1('#skF_7', '#skF_4')!='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_70500, c_70354])).
% 21.41/11.43  tff(c_70560, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66046, c_67610, c_70509])).
% 21.41/11.43  tff(c_70561, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_7652])).
% 21.41/11.43  tff(c_70562, plain, (k1_relat_1('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_7652])).
% 21.41/11.43  tff(c_70577, plain, (k1_relat_1('#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_70561, c_70562])).
% 21.41/11.43  tff(c_70609, plain, (![C_3736, A_3737, B_3738]: (v4_relat_1(C_3736, A_3737) | ~m1_subset_1(C_3736, k1_zfmisc_1(k2_zfmisc_1(A_3737, B_3738))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 21.41/11.43  tff(c_70616, plain, (v4_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_76, c_70609])).
% 21.41/11.43  tff(c_81604, plain, (![B_4500, A_4501]: (k1_relat_1(B_4500)=A_4501 | ~v1_partfun1(B_4500, A_4501) | ~v4_relat_1(B_4500, A_4501) | ~v1_relat_1(B_4500))), inference(cnfTransformation, [status(thm)], [f_141])).
% 21.41/11.43  tff(c_81613, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_70616, c_81604])).
% 21.41/11.43  tff(c_81622, plain, ('#skF_7'='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7643, c_70577, c_81613])).
% 21.41/11.43  tff(c_81623, plain, (~v1_partfun1('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_81622])).
% 21.41/11.43  tff(c_81864, plain, (![C_4525, A_4526, B_4527]: (v1_partfun1(C_4525, A_4526) | ~v1_funct_2(C_4525, A_4526, B_4527) | ~v1_funct_1(C_4525) | ~m1_subset_1(C_4525, k1_zfmisc_1(k2_zfmisc_1(A_4526, B_4527))) | v1_xboole_0(B_4527))), inference(cnfTransformation, [status(thm)], [f_133])).
% 21.41/11.43  tff(c_81867, plain, (v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_76, c_81864])).
% 21.41/11.43  tff(c_81873, plain, (v1_partfun1('#skF_7', '#skF_5') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_81867])).
% 21.41/11.43  tff(c_81875, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_81623, c_81873])).
% 21.41/11.43  tff(c_81876, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_81622])).
% 21.41/11.43  tff(c_81368, plain, (![A_4483, B_4484]: (k7_relat_1(A_4483, B_4484)='#skF_7' | ~r1_xboole_0(B_4484, k1_relat_1(A_4483)) | ~v1_relat_1(A_4483))), inference(demodulation, [status(thm), theory('equality')], [c_70561, c_24])).
% 21.41/11.43  tff(c_81399, plain, (![B_4484]: (k7_relat_1('#skF_7', B_4484)='#skF_7' | ~r1_xboole_0(B_4484, '#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_70577, c_81368])).
% 21.41/11.43  tff(c_81408, plain, (![B_4484]: (k7_relat_1('#skF_7', B_4484)='#skF_7' | ~r1_xboole_0(B_4484, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_7643, c_81399])).
% 21.41/11.43  tff(c_82189, plain, (![B_4555]: (k7_relat_1('#skF_5', B_4555)='#skF_5' | ~r1_xboole_0(B_4555, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_81876, c_81876, c_81876, c_81408])).
% 21.41/11.43  tff(c_82201, plain, (![A_28]: (k7_relat_1('#skF_5', A_28)='#skF_5' | ~r1_subset_1(A_28, '#skF_5') | v1_xboole_0('#skF_5') | v1_xboole_0(A_28))), inference(resolution, [status(thm)], [c_40, c_82189])).
% 21.41/11.43  tff(c_82576, plain, (![A_4589]: (k7_relat_1('#skF_5', A_4589)='#skF_5' | ~r1_subset_1(A_4589, '#skF_5') | v1_xboole_0(A_4589))), inference(negUnitSimplification, [status(thm)], [c_92, c_82201])).
% 21.41/11.43  tff(c_82583, plain, (k7_relat_1('#skF_5', '#skF_4')='#skF_5' | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_88, c_82576])).
% 21.41/11.43  tff(c_82590, plain, (k7_relat_1('#skF_5', '#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_96, c_82583])).
% 21.41/11.43  tff(c_81183, plain, (![B_4473, A_4474]: (r1_xboole_0(k1_relat_1(B_4473), A_4474) | k7_relat_1(B_4473, A_4474)!='#skF_7' | ~v1_relat_1(B_4473))), inference(demodulation, [status(thm), theory('equality')], [c_70561, c_36])).
% 21.41/11.43  tff(c_81198, plain, (![A_4474]: (r1_xboole_0('#skF_7', A_4474) | k7_relat_1('#skF_7', A_4474)!='#skF_7' | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_70577, c_81183])).
% 21.41/11.43  tff(c_81204, plain, (![A_4474]: (r1_xboole_0('#skF_7', A_4474) | k7_relat_1('#skF_7', A_4474)!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_7643, c_81198])).
% 21.41/11.43  tff(c_81893, plain, (![A_4474]: (r1_xboole_0('#skF_5', A_4474) | k7_relat_1('#skF_5', A_4474)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_81876, c_81876, c_81876, c_81204])).
% 21.41/11.43  tff(c_70617, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_82, c_70609])).
% 21.41/11.43  tff(c_81610, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_70617, c_81604])).
% 21.41/11.43  tff(c_81619, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7644, c_81610])).
% 21.41/11.43  tff(c_82047, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_81619])).
% 21.41/11.43  tff(c_82056, plain, (![C_4539, A_4540, B_4541]: (v1_partfun1(C_4539, A_4540) | ~v1_funct_2(C_4539, A_4540, B_4541) | ~v1_funct_1(C_4539) | ~m1_subset_1(C_4539, k1_zfmisc_1(k2_zfmisc_1(A_4540, B_4541))) | v1_xboole_0(B_4541))), inference(cnfTransformation, [status(thm)], [f_133])).
% 21.41/11.43  tff(c_82062, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_82, c_82056])).
% 21.41/11.43  tff(c_82069, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82062])).
% 21.41/11.43  tff(c_82071, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_82047, c_82069])).
% 21.41/11.43  tff(c_82072, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_81619])).
% 21.41/11.43  tff(c_81367, plain, (![A_22, B_24]: (k7_relat_1(A_22, B_24)='#skF_7' | ~r1_xboole_0(B_24, k1_relat_1(A_22)) | ~v1_relat_1(A_22))), inference(demodulation, [status(thm), theory('equality')], [c_70561, c_24])).
% 21.41/11.43  tff(c_82735, plain, (![A_4607, B_4608]: (k7_relat_1(A_4607, B_4608)='#skF_5' | ~r1_xboole_0(B_4608, k1_relat_1(A_4607)) | ~v1_relat_1(A_4607))), inference(demodulation, [status(thm), theory('equality')], [c_81876, c_81367])).
% 21.41/11.43  tff(c_82762, plain, (![B_4608]: (k7_relat_1('#skF_6', B_4608)='#skF_5' | ~r1_xboole_0(B_4608, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_82072, c_82735])).
% 21.41/11.43  tff(c_82785, plain, (![B_4615]: (k7_relat_1('#skF_6', B_4615)='#skF_5' | ~r1_xboole_0(B_4615, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7644, c_82762])).
% 21.41/11.43  tff(c_82801, plain, (k7_relat_1('#skF_6', '#skF_5')='#skF_5' | k7_relat_1('#skF_5', '#skF_4')!='#skF_5'), inference(resolution, [status(thm)], [c_81893, c_82785])).
% 21.41/11.43  tff(c_82820, plain, (k7_relat_1('#skF_6', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_82590, c_82801])).
% 21.41/11.43  tff(c_81182, plain, (![B_27, A_26]: (r1_xboole_0(k1_relat_1(B_27), A_26) | k7_relat_1(B_27, A_26)!='#skF_7' | ~v1_relat_1(B_27))), inference(demodulation, [status(thm), theory('equality')], [c_70561, c_36])).
% 21.41/11.43  tff(c_82685, plain, (![B_4602, A_4603]: (r1_xboole_0(k1_relat_1(B_4602), A_4603) | k7_relat_1(B_4602, A_4603)!='#skF_5' | ~v1_relat_1(B_4602))), inference(demodulation, [status(thm), theory('equality')], [c_81876, c_81182])).
% 21.41/11.43  tff(c_82698, plain, (![A_4603]: (r1_xboole_0('#skF_4', A_4603) | k7_relat_1('#skF_6', A_4603)!='#skF_5' | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_82072, c_82685])).
% 21.41/11.43  tff(c_82709, plain, (![A_4604]: (r1_xboole_0('#skF_4', A_4604) | k7_relat_1('#skF_6', A_4604)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7644, c_82698])).
% 21.41/11.43  tff(c_70565, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)='#skF_7' | ~r1_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_70561, c_2])).
% 21.41/11.43  tff(c_81909, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)='#skF_5' | ~r1_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_81876, c_70565])).
% 21.41/11.43  tff(c_82722, plain, (![A_4604]: (k3_xboole_0('#skF_4', A_4604)='#skF_5' | k7_relat_1('#skF_6', A_4604)!='#skF_5')), inference(resolution, [status(thm)], [c_82709, c_81909])).
% 21.41/11.43  tff(c_82840, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_82820, c_82722])).
% 21.41/11.43  tff(c_70571, plain, (k2_relat_1('#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_70561, c_70561, c_26])).
% 21.41/11.43  tff(c_70582, plain, (![A_3734]: (k9_relat_1(A_3734, k1_relat_1(A_3734))=k2_relat_1(A_3734) | ~v1_relat_1(A_3734))), inference(cnfTransformation, [status(thm)], [f_52])).
% 21.41/11.43  tff(c_70591, plain, (k9_relat_1('#skF_7', '#skF_7')=k2_relat_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_70577, c_70582])).
% 21.41/11.43  tff(c_70595, plain, (k9_relat_1('#skF_7', '#skF_7')=k2_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_7643, c_70591])).
% 21.41/11.43  tff(c_70619, plain, (k9_relat_1('#skF_7', '#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_70571, c_70595])).
% 21.41/11.43  tff(c_81051, plain, (![B_4461, A_4462]: (r1_xboole_0(k1_relat_1(B_4461), A_4462) | k9_relat_1(B_4461, A_4462)!='#skF_7' | ~v1_relat_1(B_4461))), inference(demodulation, [status(thm), theory('equality')], [c_70561, c_20])).
% 21.41/11.43  tff(c_81057, plain, (![A_4462]: (r1_xboole_0('#skF_7', A_4462) | k9_relat_1('#skF_7', A_4462)!='#skF_7' | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_70577, c_81051])).
% 21.41/11.43  tff(c_81060, plain, (![A_4462]: (r1_xboole_0('#skF_7', A_4462) | k9_relat_1('#skF_7', A_4462)!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_7643, c_81057])).
% 21.41/11.43  tff(c_81167, plain, (![B_4471, A_4472]: (k7_relat_1(B_4471, A_4472)='#skF_7' | ~r1_xboole_0(k1_relat_1(B_4471), A_4472) | ~v1_relat_1(B_4471))), inference(demodulation, [status(thm), theory('equality')], [c_70561, c_34])).
% 21.41/11.43  tff(c_81177, plain, (![A_4472]: (k7_relat_1('#skF_7', A_4472)='#skF_7' | ~r1_xboole_0('#skF_7', A_4472) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_70577, c_81167])).
% 21.41/11.43  tff(c_81205, plain, (![A_4475]: (k7_relat_1('#skF_7', A_4475)='#skF_7' | ~r1_xboole_0('#skF_7', A_4475))), inference(demodulation, [status(thm), theory('equality')], [c_7643, c_81177])).
% 21.41/11.43  tff(c_81292, plain, (![A_4480]: (k7_relat_1('#skF_7', A_4480)='#skF_7' | k9_relat_1('#skF_7', A_4480)!='#skF_7')), inference(resolution, [status(thm)], [c_81060, c_81205])).
% 21.41/11.43  tff(c_81308, plain, (k7_relat_1('#skF_7', '#skF_7')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_70619, c_81292])).
% 21.41/11.43  tff(c_81887, plain, (k7_relat_1('#skF_5', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_81876, c_81876, c_81876, c_81308])).
% 21.41/11.43  tff(c_81554, plain, (![A_4493, B_4494, C_4495]: (k9_subset_1(A_4493, B_4494, C_4495)=k3_xboole_0(B_4494, C_4495) | ~m1_subset_1(C_4495, k1_zfmisc_1(A_4493)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 21.41/11.43  tff(c_81566, plain, (![B_4494]: (k9_subset_1('#skF_2', B_4494, '#skF_5')=k3_xboole_0(B_4494, '#skF_5'))), inference(resolution, [status(thm)], [c_90, c_81554])).
% 21.41/11.43  tff(c_81926, plain, (v1_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_81876, c_80])).
% 21.41/11.43  tff(c_81925, plain, (v1_funct_2('#skF_5', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_81876, c_78])).
% 21.41/11.43  tff(c_81924, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_81876, c_76])).
% 21.41/11.43  tff(c_82226, plain, (![F_4560, A_4559, B_4562, C_4557, D_4558, E_4561]: (v1_funct_1(k1_tmap_1(A_4559, B_4562, C_4557, D_4558, E_4561, F_4560)) | ~m1_subset_1(F_4560, k1_zfmisc_1(k2_zfmisc_1(D_4558, B_4562))) | ~v1_funct_2(F_4560, D_4558, B_4562) | ~v1_funct_1(F_4560) | ~m1_subset_1(E_4561, k1_zfmisc_1(k2_zfmisc_1(C_4557, B_4562))) | ~v1_funct_2(E_4561, C_4557, B_4562) | ~v1_funct_1(E_4561) | ~m1_subset_1(D_4558, k1_zfmisc_1(A_4559)) | v1_xboole_0(D_4558) | ~m1_subset_1(C_4557, k1_zfmisc_1(A_4559)) | v1_xboole_0(C_4557) | v1_xboole_0(B_4562) | v1_xboole_0(A_4559))), inference(cnfTransformation, [status(thm)], [f_229])).
% 21.41/11.43  tff(c_82228, plain, (![A_4559, C_4557, E_4561]: (v1_funct_1(k1_tmap_1(A_4559, '#skF_3', C_4557, '#skF_5', E_4561, '#skF_5')) | ~v1_funct_2('#skF_5', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_4561, k1_zfmisc_1(k2_zfmisc_1(C_4557, '#skF_3'))) | ~v1_funct_2(E_4561, C_4557, '#skF_3') | ~v1_funct_1(E_4561) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4559)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_4557, k1_zfmisc_1(A_4559)) | v1_xboole_0(C_4557) | v1_xboole_0('#skF_3') | v1_xboole_0(A_4559))), inference(resolution, [status(thm)], [c_81924, c_82226])).
% 21.41/11.43  tff(c_82233, plain, (![A_4559, C_4557, E_4561]: (v1_funct_1(k1_tmap_1(A_4559, '#skF_3', C_4557, '#skF_5', E_4561, '#skF_5')) | ~m1_subset_1(E_4561, k1_zfmisc_1(k2_zfmisc_1(C_4557, '#skF_3'))) | ~v1_funct_2(E_4561, C_4557, '#skF_3') | ~v1_funct_1(E_4561) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4559)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_4557, k1_zfmisc_1(A_4559)) | v1_xboole_0(C_4557) | v1_xboole_0('#skF_3') | v1_xboole_0(A_4559))), inference(demodulation, [status(thm), theory('equality')], [c_81926, c_81925, c_82228])).
% 21.41/11.43  tff(c_83692, plain, (![A_4659, C_4660, E_4661]: (v1_funct_1(k1_tmap_1(A_4659, '#skF_3', C_4660, '#skF_5', E_4661, '#skF_5')) | ~m1_subset_1(E_4661, k1_zfmisc_1(k2_zfmisc_1(C_4660, '#skF_3'))) | ~v1_funct_2(E_4661, C_4660, '#skF_3') | ~v1_funct_1(E_4661) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4659)) | ~m1_subset_1(C_4660, k1_zfmisc_1(A_4659)) | v1_xboole_0(C_4660) | v1_xboole_0(A_4659))), inference(negUnitSimplification, [status(thm)], [c_98, c_92, c_82233])).
% 21.41/11.43  tff(c_83699, plain, (![A_4659]: (v1_funct_1(k1_tmap_1(A_4659, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4659)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4659)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_4659))), inference(resolution, [status(thm)], [c_82, c_83692])).
% 21.41/11.43  tff(c_83709, plain, (![A_4659]: (v1_funct_1(k1_tmap_1(A_4659, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4659)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4659)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_4659))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_83699])).
% 21.41/11.43  tff(c_83919, plain, (![A_4674]: (v1_funct_1(k1_tmap_1(A_4674, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4674)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4674)) | v1_xboole_0(A_4674))), inference(negUnitSimplification, [status(thm)], [c_96, c_83709])).
% 21.41/11.43  tff(c_83925, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_90, c_83919])).
% 21.41/11.43  tff(c_83931, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_83925])).
% 21.41/11.43  tff(c_83932, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_100, c_83931])).
% 21.41/11.43  tff(c_82003, plain, (![A_4532, B_4533, C_4534, D_4535]: (k2_partfun1(A_4532, B_4533, C_4534, D_4535)=k7_relat_1(C_4534, D_4535) | ~m1_subset_1(C_4534, k1_zfmisc_1(k2_zfmisc_1(A_4532, B_4533))) | ~v1_funct_1(C_4534))), inference(cnfTransformation, [status(thm)], [f_147])).
% 21.41/11.43  tff(c_82005, plain, (![D_4535]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_4535)=k7_relat_1('#skF_6', D_4535) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_82, c_82003])).
% 21.41/11.43  tff(c_82008, plain, (![D_4535]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_4535)=k7_relat_1('#skF_6', D_4535))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82005])).
% 21.41/11.43  tff(c_82011, plain, (![D_47]: (k2_partfun1('#skF_5', '#skF_3', '#skF_5', D_47)=k7_relat_1('#skF_5', D_47) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_81924, c_60])).
% 21.41/11.43  tff(c_82028, plain, (![D_47]: (k2_partfun1('#skF_5', '#skF_3', '#skF_5', D_47)=k7_relat_1('#skF_5', D_47))), inference(demodulation, [status(thm), theory('equality')], [c_81926, c_82011])).
% 21.41/11.43  tff(c_82781, plain, (![F_4613, C_4611, B_4614, A_4610, E_4609, D_4612]: (k2_partfun1(k4_subset_1(A_4610, C_4611, D_4612), B_4614, k1_tmap_1(A_4610, B_4614, C_4611, D_4612, E_4609, F_4613), C_4611)=E_4609 | ~m1_subset_1(k1_tmap_1(A_4610, B_4614, C_4611, D_4612, E_4609, F_4613), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_4610, C_4611, D_4612), B_4614))) | ~v1_funct_2(k1_tmap_1(A_4610, B_4614, C_4611, D_4612, E_4609, F_4613), k4_subset_1(A_4610, C_4611, D_4612), B_4614) | ~v1_funct_1(k1_tmap_1(A_4610, B_4614, C_4611, D_4612, E_4609, F_4613)) | k2_partfun1(D_4612, B_4614, F_4613, k9_subset_1(A_4610, C_4611, D_4612))!=k2_partfun1(C_4611, B_4614, E_4609, k9_subset_1(A_4610, C_4611, D_4612)) | ~m1_subset_1(F_4613, k1_zfmisc_1(k2_zfmisc_1(D_4612, B_4614))) | ~v1_funct_2(F_4613, D_4612, B_4614) | ~v1_funct_1(F_4613) | ~m1_subset_1(E_4609, k1_zfmisc_1(k2_zfmisc_1(C_4611, B_4614))) | ~v1_funct_2(E_4609, C_4611, B_4614) | ~v1_funct_1(E_4609) | ~m1_subset_1(D_4612, k1_zfmisc_1(A_4610)) | v1_xboole_0(D_4612) | ~m1_subset_1(C_4611, k1_zfmisc_1(A_4610)) | v1_xboole_0(C_4611) | v1_xboole_0(B_4614) | v1_xboole_0(A_4610))), inference(cnfTransformation, [status(thm)], [f_195])).
% 21.41/11.43  tff(c_85598, plain, (![A_4785, D_4784, C_4783, F_4786, E_4787, B_4788]: (k2_partfun1(k4_subset_1(A_4785, C_4783, D_4784), B_4788, k1_tmap_1(A_4785, B_4788, C_4783, D_4784, E_4787, F_4786), C_4783)=E_4787 | ~v1_funct_2(k1_tmap_1(A_4785, B_4788, C_4783, D_4784, E_4787, F_4786), k4_subset_1(A_4785, C_4783, D_4784), B_4788) | ~v1_funct_1(k1_tmap_1(A_4785, B_4788, C_4783, D_4784, E_4787, F_4786)) | k2_partfun1(D_4784, B_4788, F_4786, k9_subset_1(A_4785, C_4783, D_4784))!=k2_partfun1(C_4783, B_4788, E_4787, k9_subset_1(A_4785, C_4783, D_4784)) | ~m1_subset_1(F_4786, k1_zfmisc_1(k2_zfmisc_1(D_4784, B_4788))) | ~v1_funct_2(F_4786, D_4784, B_4788) | ~v1_funct_1(F_4786) | ~m1_subset_1(E_4787, k1_zfmisc_1(k2_zfmisc_1(C_4783, B_4788))) | ~v1_funct_2(E_4787, C_4783, B_4788) | ~v1_funct_1(E_4787) | ~m1_subset_1(D_4784, k1_zfmisc_1(A_4785)) | v1_xboole_0(D_4784) | ~m1_subset_1(C_4783, k1_zfmisc_1(A_4785)) | v1_xboole_0(C_4783) | v1_xboole_0(B_4788) | v1_xboole_0(A_4785))), inference(resolution, [status(thm)], [c_68, c_82781])).
% 21.41/11.43  tff(c_86297, plain, (![D_4857, A_4858, C_4856, F_4859, E_4860, B_4861]: (k2_partfun1(k4_subset_1(A_4858, C_4856, D_4857), B_4861, k1_tmap_1(A_4858, B_4861, C_4856, D_4857, E_4860, F_4859), C_4856)=E_4860 | ~v1_funct_1(k1_tmap_1(A_4858, B_4861, C_4856, D_4857, E_4860, F_4859)) | k2_partfun1(D_4857, B_4861, F_4859, k9_subset_1(A_4858, C_4856, D_4857))!=k2_partfun1(C_4856, B_4861, E_4860, k9_subset_1(A_4858, C_4856, D_4857)) | ~m1_subset_1(F_4859, k1_zfmisc_1(k2_zfmisc_1(D_4857, B_4861))) | ~v1_funct_2(F_4859, D_4857, B_4861) | ~v1_funct_1(F_4859) | ~m1_subset_1(E_4860, k1_zfmisc_1(k2_zfmisc_1(C_4856, B_4861))) | ~v1_funct_2(E_4860, C_4856, B_4861) | ~v1_funct_1(E_4860) | ~m1_subset_1(D_4857, k1_zfmisc_1(A_4858)) | v1_xboole_0(D_4857) | ~m1_subset_1(C_4856, k1_zfmisc_1(A_4858)) | v1_xboole_0(C_4856) | v1_xboole_0(B_4861) | v1_xboole_0(A_4858))), inference(resolution, [status(thm)], [c_70, c_85598])).
% 21.41/11.43  tff(c_86301, plain, (![A_4858, C_4856, E_4860]: (k2_partfun1(k4_subset_1(A_4858, C_4856, '#skF_5'), '#skF_3', k1_tmap_1(A_4858, '#skF_3', C_4856, '#skF_5', E_4860, '#skF_5'), C_4856)=E_4860 | ~v1_funct_1(k1_tmap_1(A_4858, '#skF_3', C_4856, '#skF_5', E_4860, '#skF_5')) | k2_partfun1(C_4856, '#skF_3', E_4860, k9_subset_1(A_4858, C_4856, '#skF_5'))!=k2_partfun1('#skF_5', '#skF_3', '#skF_5', k9_subset_1(A_4858, C_4856, '#skF_5')) | ~v1_funct_2('#skF_5', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_4860, k1_zfmisc_1(k2_zfmisc_1(C_4856, '#skF_3'))) | ~v1_funct_2(E_4860, C_4856, '#skF_3') | ~v1_funct_1(E_4860) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4858)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_4856, k1_zfmisc_1(A_4858)) | v1_xboole_0(C_4856) | v1_xboole_0('#skF_3') | v1_xboole_0(A_4858))), inference(resolution, [status(thm)], [c_81924, c_86297])).
% 21.41/11.43  tff(c_86307, plain, (![A_4858, C_4856, E_4860]: (k2_partfun1(k4_subset_1(A_4858, C_4856, '#skF_5'), '#skF_3', k1_tmap_1(A_4858, '#skF_3', C_4856, '#skF_5', E_4860, '#skF_5'), C_4856)=E_4860 | ~v1_funct_1(k1_tmap_1(A_4858, '#skF_3', C_4856, '#skF_5', E_4860, '#skF_5')) | k2_partfun1(C_4856, '#skF_3', E_4860, k9_subset_1(A_4858, C_4856, '#skF_5'))!=k7_relat_1('#skF_5', k9_subset_1(A_4858, C_4856, '#skF_5')) | ~m1_subset_1(E_4860, k1_zfmisc_1(k2_zfmisc_1(C_4856, '#skF_3'))) | ~v1_funct_2(E_4860, C_4856, '#skF_3') | ~v1_funct_1(E_4860) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4858)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_4856, k1_zfmisc_1(A_4858)) | v1_xboole_0(C_4856) | v1_xboole_0('#skF_3') | v1_xboole_0(A_4858))), inference(demodulation, [status(thm), theory('equality')], [c_81926, c_81925, c_82028, c_86301])).
% 21.41/11.43  tff(c_87946, plain, (![A_4896, C_4897, E_4898]: (k2_partfun1(k4_subset_1(A_4896, C_4897, '#skF_5'), '#skF_3', k1_tmap_1(A_4896, '#skF_3', C_4897, '#skF_5', E_4898, '#skF_5'), C_4897)=E_4898 | ~v1_funct_1(k1_tmap_1(A_4896, '#skF_3', C_4897, '#skF_5', E_4898, '#skF_5')) | k2_partfun1(C_4897, '#skF_3', E_4898, k9_subset_1(A_4896, C_4897, '#skF_5'))!=k7_relat_1('#skF_5', k9_subset_1(A_4896, C_4897, '#skF_5')) | ~m1_subset_1(E_4898, k1_zfmisc_1(k2_zfmisc_1(C_4897, '#skF_3'))) | ~v1_funct_2(E_4898, C_4897, '#skF_3') | ~v1_funct_1(E_4898) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4896)) | ~m1_subset_1(C_4897, k1_zfmisc_1(A_4896)) | v1_xboole_0(C_4897) | v1_xboole_0(A_4896))), inference(negUnitSimplification, [status(thm)], [c_98, c_92, c_86307])).
% 21.41/11.43  tff(c_87953, plain, (![A_4896]: (k2_partfun1(k4_subset_1(A_4896, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_4896, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_4896, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5')) | k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1(A_4896, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_5', k9_subset_1(A_4896, '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4896)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4896)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_4896))), inference(resolution, [status(thm)], [c_82, c_87946])).
% 21.41/11.43  tff(c_87963, plain, (![A_4896]: (k2_partfun1(k4_subset_1(A_4896, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_4896, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_4896, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5')) | k7_relat_1('#skF_5', k9_subset_1(A_4896, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_4896, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4896)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4896)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_4896))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82008, c_87953])).
% 21.41/11.43  tff(c_89431, plain, (![A_4932]: (k2_partfun1(k4_subset_1(A_4932, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_4932, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_4932, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5')) | k7_relat_1('#skF_5', k9_subset_1(A_4932, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_4932, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4932)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4932)) | v1_xboole_0(A_4932))), inference(negUnitSimplification, [status(thm)], [c_96, c_87963])).
% 21.41/11.43  tff(c_73386, plain, (![B_3956, A_3957]: (k1_relat_1(B_3956)=A_3957 | ~v1_partfun1(B_3956, A_3957) | ~v4_relat_1(B_3956, A_3957) | ~v1_relat_1(B_3956))), inference(cnfTransformation, [status(thm)], [f_141])).
% 21.41/11.43  tff(c_73395, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_70616, c_73386])).
% 21.41/11.43  tff(c_73404, plain, ('#skF_7'='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7643, c_70577, c_73395])).
% 21.41/11.43  tff(c_73405, plain, (~v1_partfun1('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_73404])).
% 21.41/11.43  tff(c_73751, plain, (![C_3987, A_3988, B_3989]: (v1_partfun1(C_3987, A_3988) | ~v1_funct_2(C_3987, A_3988, B_3989) | ~v1_funct_1(C_3987) | ~m1_subset_1(C_3987, k1_zfmisc_1(k2_zfmisc_1(A_3988, B_3989))) | v1_xboole_0(B_3989))), inference(cnfTransformation, [status(thm)], [f_133])).
% 21.41/11.43  tff(c_73754, plain, (v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_76, c_73751])).
% 21.41/11.43  tff(c_73760, plain, (v1_partfun1('#skF_7', '#skF_5') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_73754])).
% 21.41/11.43  tff(c_73762, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_73405, c_73760])).
% 21.41/11.43  tff(c_73763, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_73404])).
% 21.41/11.43  tff(c_73815, plain, (v1_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_73763, c_80])).
% 21.41/11.43  tff(c_73814, plain, (v1_funct_2('#skF_5', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_73763, c_78])).
% 21.41/11.43  tff(c_73813, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_73763, c_76])).
% 21.41/11.43  tff(c_74399, plain, (![A_4049, E_4051, D_4048, F_4050, C_4047, B_4052]: (v1_funct_1(k1_tmap_1(A_4049, B_4052, C_4047, D_4048, E_4051, F_4050)) | ~m1_subset_1(F_4050, k1_zfmisc_1(k2_zfmisc_1(D_4048, B_4052))) | ~v1_funct_2(F_4050, D_4048, B_4052) | ~v1_funct_1(F_4050) | ~m1_subset_1(E_4051, k1_zfmisc_1(k2_zfmisc_1(C_4047, B_4052))) | ~v1_funct_2(E_4051, C_4047, B_4052) | ~v1_funct_1(E_4051) | ~m1_subset_1(D_4048, k1_zfmisc_1(A_4049)) | v1_xboole_0(D_4048) | ~m1_subset_1(C_4047, k1_zfmisc_1(A_4049)) | v1_xboole_0(C_4047) | v1_xboole_0(B_4052) | v1_xboole_0(A_4049))), inference(cnfTransformation, [status(thm)], [f_229])).
% 21.41/11.43  tff(c_74401, plain, (![A_4049, C_4047, E_4051]: (v1_funct_1(k1_tmap_1(A_4049, '#skF_3', C_4047, '#skF_5', E_4051, '#skF_5')) | ~v1_funct_2('#skF_5', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_4051, k1_zfmisc_1(k2_zfmisc_1(C_4047, '#skF_3'))) | ~v1_funct_2(E_4051, C_4047, '#skF_3') | ~v1_funct_1(E_4051) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4049)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_4047, k1_zfmisc_1(A_4049)) | v1_xboole_0(C_4047) | v1_xboole_0('#skF_3') | v1_xboole_0(A_4049))), inference(resolution, [status(thm)], [c_73813, c_74399])).
% 21.41/11.43  tff(c_74406, plain, (![A_4049, C_4047, E_4051]: (v1_funct_1(k1_tmap_1(A_4049, '#skF_3', C_4047, '#skF_5', E_4051, '#skF_5')) | ~m1_subset_1(E_4051, k1_zfmisc_1(k2_zfmisc_1(C_4047, '#skF_3'))) | ~v1_funct_2(E_4051, C_4047, '#skF_3') | ~v1_funct_1(E_4051) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4049)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_4047, k1_zfmisc_1(A_4049)) | v1_xboole_0(C_4047) | v1_xboole_0('#skF_3') | v1_xboole_0(A_4049))), inference(demodulation, [status(thm), theory('equality')], [c_73815, c_73814, c_74401])).
% 21.41/11.43  tff(c_75723, plain, (![A_4139, C_4140, E_4141]: (v1_funct_1(k1_tmap_1(A_4139, '#skF_3', C_4140, '#skF_5', E_4141, '#skF_5')) | ~m1_subset_1(E_4141, k1_zfmisc_1(k2_zfmisc_1(C_4140, '#skF_3'))) | ~v1_funct_2(E_4141, C_4140, '#skF_3') | ~v1_funct_1(E_4141) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4139)) | ~m1_subset_1(C_4140, k1_zfmisc_1(A_4139)) | v1_xboole_0(C_4140) | v1_xboole_0(A_4139))), inference(negUnitSimplification, [status(thm)], [c_98, c_92, c_74406])).
% 21.41/11.43  tff(c_75730, plain, (![A_4139]: (v1_funct_1(k1_tmap_1(A_4139, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4139)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4139)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_4139))), inference(resolution, [status(thm)], [c_82, c_75723])).
% 21.41/11.43  tff(c_75740, plain, (![A_4139]: (v1_funct_1(k1_tmap_1(A_4139, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4139)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4139)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_4139))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_75730])).
% 21.41/11.43  tff(c_75986, plain, (![A_4158]: (v1_funct_1(k1_tmap_1(A_4158, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4158)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4158)) | v1_xboole_0(A_4158))), inference(negUnitSimplification, [status(thm)], [c_96, c_75740])).
% 21.41/11.43  tff(c_75992, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_90, c_75986])).
% 21.41/11.43  tff(c_75998, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_75992])).
% 21.41/11.43  tff(c_75999, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_100, c_75998])).
% 21.41/11.43  tff(c_74638, plain, (![A_4072, B_4075, E_4074, F_4073, C_4070, D_4071]: (m1_subset_1(k1_tmap_1(A_4072, B_4075, C_4070, D_4071, E_4074, F_4073), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_4072, C_4070, D_4071), B_4075))) | ~m1_subset_1(F_4073, k1_zfmisc_1(k2_zfmisc_1(D_4071, B_4075))) | ~v1_funct_2(F_4073, D_4071, B_4075) | ~v1_funct_1(F_4073) | ~m1_subset_1(E_4074, k1_zfmisc_1(k2_zfmisc_1(C_4070, B_4075))) | ~v1_funct_2(E_4074, C_4070, B_4075) | ~v1_funct_1(E_4074) | ~m1_subset_1(D_4071, k1_zfmisc_1(A_4072)) | v1_xboole_0(D_4071) | ~m1_subset_1(C_4070, k1_zfmisc_1(A_4072)) | v1_xboole_0(C_4070) | v1_xboole_0(B_4075) | v1_xboole_0(A_4072))), inference(cnfTransformation, [status(thm)], [f_229])).
% 21.41/11.43  tff(c_77077, plain, (![A_4222, C_4224, D_4221, E_4219, B_4220, F_4225, D_4223]: (k2_partfun1(k4_subset_1(A_4222, C_4224, D_4223), B_4220, k1_tmap_1(A_4222, B_4220, C_4224, D_4223, E_4219, F_4225), D_4221)=k7_relat_1(k1_tmap_1(A_4222, B_4220, C_4224, D_4223, E_4219, F_4225), D_4221) | ~v1_funct_1(k1_tmap_1(A_4222, B_4220, C_4224, D_4223, E_4219, F_4225)) | ~m1_subset_1(F_4225, k1_zfmisc_1(k2_zfmisc_1(D_4223, B_4220))) | ~v1_funct_2(F_4225, D_4223, B_4220) | ~v1_funct_1(F_4225) | ~m1_subset_1(E_4219, k1_zfmisc_1(k2_zfmisc_1(C_4224, B_4220))) | ~v1_funct_2(E_4219, C_4224, B_4220) | ~v1_funct_1(E_4219) | ~m1_subset_1(D_4223, k1_zfmisc_1(A_4222)) | v1_xboole_0(D_4223) | ~m1_subset_1(C_4224, k1_zfmisc_1(A_4222)) | v1_xboole_0(C_4224) | v1_xboole_0(B_4220) | v1_xboole_0(A_4222))), inference(resolution, [status(thm)], [c_74638, c_60])).
% 21.41/11.43  tff(c_77081, plain, (![A_4222, C_4224, E_4219, D_4221]: (k2_partfun1(k4_subset_1(A_4222, C_4224, '#skF_5'), '#skF_3', k1_tmap_1(A_4222, '#skF_3', C_4224, '#skF_5', E_4219, '#skF_5'), D_4221)=k7_relat_1(k1_tmap_1(A_4222, '#skF_3', C_4224, '#skF_5', E_4219, '#skF_5'), D_4221) | ~v1_funct_1(k1_tmap_1(A_4222, '#skF_3', C_4224, '#skF_5', E_4219, '#skF_5')) | ~v1_funct_2('#skF_5', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_4219, k1_zfmisc_1(k2_zfmisc_1(C_4224, '#skF_3'))) | ~v1_funct_2(E_4219, C_4224, '#skF_3') | ~v1_funct_1(E_4219) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4222)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_4224, k1_zfmisc_1(A_4222)) | v1_xboole_0(C_4224) | v1_xboole_0('#skF_3') | v1_xboole_0(A_4222))), inference(resolution, [status(thm)], [c_73813, c_77077])).
% 21.41/11.43  tff(c_77087, plain, (![A_4222, C_4224, E_4219, D_4221]: (k2_partfun1(k4_subset_1(A_4222, C_4224, '#skF_5'), '#skF_3', k1_tmap_1(A_4222, '#skF_3', C_4224, '#skF_5', E_4219, '#skF_5'), D_4221)=k7_relat_1(k1_tmap_1(A_4222, '#skF_3', C_4224, '#skF_5', E_4219, '#skF_5'), D_4221) | ~v1_funct_1(k1_tmap_1(A_4222, '#skF_3', C_4224, '#skF_5', E_4219, '#skF_5')) | ~m1_subset_1(E_4219, k1_zfmisc_1(k2_zfmisc_1(C_4224, '#skF_3'))) | ~v1_funct_2(E_4219, C_4224, '#skF_3') | ~v1_funct_1(E_4219) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4222)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_4224, k1_zfmisc_1(A_4222)) | v1_xboole_0(C_4224) | v1_xboole_0('#skF_3') | v1_xboole_0(A_4222))), inference(demodulation, [status(thm), theory('equality')], [c_73815, c_73814, c_77081])).
% 21.41/11.43  tff(c_78416, plain, (![A_4336, C_4337, E_4338, D_4339]: (k2_partfun1(k4_subset_1(A_4336, C_4337, '#skF_5'), '#skF_3', k1_tmap_1(A_4336, '#skF_3', C_4337, '#skF_5', E_4338, '#skF_5'), D_4339)=k7_relat_1(k1_tmap_1(A_4336, '#skF_3', C_4337, '#skF_5', E_4338, '#skF_5'), D_4339) | ~v1_funct_1(k1_tmap_1(A_4336, '#skF_3', C_4337, '#skF_5', E_4338, '#skF_5')) | ~m1_subset_1(E_4338, k1_zfmisc_1(k2_zfmisc_1(C_4337, '#skF_3'))) | ~v1_funct_2(E_4338, C_4337, '#skF_3') | ~v1_funct_1(E_4338) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4336)) | ~m1_subset_1(C_4337, k1_zfmisc_1(A_4336)) | v1_xboole_0(C_4337) | v1_xboole_0(A_4336))), inference(negUnitSimplification, [status(thm)], [c_98, c_92, c_77087])).
% 21.41/11.43  tff(c_78423, plain, (![A_4336, D_4339]: (k2_partfun1(k4_subset_1(A_4336, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_4336, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5'), D_4339)=k7_relat_1(k1_tmap_1(A_4336, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5'), D_4339) | ~v1_funct_1(k1_tmap_1(A_4336, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4336)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4336)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_4336))), inference(resolution, [status(thm)], [c_82, c_78416])).
% 21.41/11.43  tff(c_78433, plain, (![A_4336, D_4339]: (k2_partfun1(k4_subset_1(A_4336, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_4336, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5'), D_4339)=k7_relat_1(k1_tmap_1(A_4336, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5'), D_4339) | ~v1_funct_1(k1_tmap_1(A_4336, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4336)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4336)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_4336))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_78423])).
% 21.41/11.43  tff(c_79831, plain, (![A_4372, D_4373]: (k2_partfun1(k4_subset_1(A_4372, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_4372, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5'), D_4373)=k7_relat_1(k1_tmap_1(A_4372, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5'), D_4373) | ~v1_funct_1(k1_tmap_1(A_4372, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4372)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4372)) | v1_xboole_0(A_4372))), inference(negUnitSimplification, [status(thm)], [c_96, c_78433])).
% 21.41/11.43  tff(c_70661, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')!='#skF_7'), inference(splitLeft, [status(thm)], [c_7591])).
% 21.41/11.43  tff(c_73786, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5'), '#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_73763, c_73763, c_70661])).
% 21.41/11.43  tff(c_79837, plain, (k7_relat_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5'), '#skF_5')!='#skF_5' | ~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_79831, c_73786])).
% 21.41/11.43  tff(c_79846, plain, (k7_relat_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5'), '#skF_5')!='#skF_5' | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_90, c_75999, c_79837])).
% 21.41/11.43  tff(c_79847, plain, (k7_relat_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5'), '#skF_5')!='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_100, c_79846])).
% 21.41/11.43  tff(c_76002, plain, (![A_4161, B_4160, D_4162, F_4164, E_4159, C_4163]: (v1_relat_1(k1_tmap_1(A_4161, B_4160, C_4163, D_4162, E_4159, F_4164)) | ~m1_subset_1(F_4164, k1_zfmisc_1(k2_zfmisc_1(D_4162, B_4160))) | ~v1_funct_2(F_4164, D_4162, B_4160) | ~v1_funct_1(F_4164) | ~m1_subset_1(E_4159, k1_zfmisc_1(k2_zfmisc_1(C_4163, B_4160))) | ~v1_funct_2(E_4159, C_4163, B_4160) | ~v1_funct_1(E_4159) | ~m1_subset_1(D_4162, k1_zfmisc_1(A_4161)) | v1_xboole_0(D_4162) | ~m1_subset_1(C_4163, k1_zfmisc_1(A_4161)) | v1_xboole_0(C_4163) | v1_xboole_0(B_4160) | v1_xboole_0(A_4161))), inference(resolution, [status(thm)], [c_74638, c_42])).
% 21.41/11.43  tff(c_76006, plain, (![A_4161, C_4163, E_4159]: (v1_relat_1(k1_tmap_1(A_4161, '#skF_3', C_4163, '#skF_5', E_4159, '#skF_5')) | ~v1_funct_2('#skF_5', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_4159, k1_zfmisc_1(k2_zfmisc_1(C_4163, '#skF_3'))) | ~v1_funct_2(E_4159, C_4163, '#skF_3') | ~v1_funct_1(E_4159) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4161)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_4163, k1_zfmisc_1(A_4161)) | v1_xboole_0(C_4163) | v1_xboole_0('#skF_3') | v1_xboole_0(A_4161))), inference(resolution, [status(thm)], [c_73813, c_76002])).
% 21.41/11.43  tff(c_76012, plain, (![A_4161, C_4163, E_4159]: (v1_relat_1(k1_tmap_1(A_4161, '#skF_3', C_4163, '#skF_5', E_4159, '#skF_5')) | ~m1_subset_1(E_4159, k1_zfmisc_1(k2_zfmisc_1(C_4163, '#skF_3'))) | ~v1_funct_2(E_4159, C_4163, '#skF_3') | ~v1_funct_1(E_4159) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4161)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_4163, k1_zfmisc_1(A_4161)) | v1_xboole_0(C_4163) | v1_xboole_0('#skF_3') | v1_xboole_0(A_4161))), inference(demodulation, [status(thm), theory('equality')], [c_73815, c_73814, c_76006])).
% 21.41/11.43  tff(c_76604, plain, (![A_4200, C_4201, E_4202]: (v1_relat_1(k1_tmap_1(A_4200, '#skF_3', C_4201, '#skF_5', E_4202, '#skF_5')) | ~m1_subset_1(E_4202, k1_zfmisc_1(k2_zfmisc_1(C_4201, '#skF_3'))) | ~v1_funct_2(E_4202, C_4201, '#skF_3') | ~v1_funct_1(E_4202) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4200)) | ~m1_subset_1(C_4201, k1_zfmisc_1(A_4200)) | v1_xboole_0(C_4201) | v1_xboole_0(A_4200))), inference(negUnitSimplification, [status(thm)], [c_98, c_92, c_76012])).
% 21.41/11.43  tff(c_76611, plain, (![A_4200]: (v1_relat_1(k1_tmap_1(A_4200, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4200)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4200)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_4200))), inference(resolution, [status(thm)], [c_82, c_76604])).
% 21.41/11.43  tff(c_76621, plain, (![A_4200]: (v1_relat_1(k1_tmap_1(A_4200, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4200)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4200)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_4200))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_76611])).
% 21.41/11.43  tff(c_77248, plain, (![A_4231]: (v1_relat_1(k1_tmap_1(A_4231, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4231)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4231)) | v1_xboole_0(A_4231))), inference(negUnitSimplification, [status(thm)], [c_96, c_76621])).
% 21.41/11.43  tff(c_77254, plain, (v1_relat_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_90, c_77248])).
% 21.41/11.43  tff(c_77260, plain, (v1_relat_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_77254])).
% 21.41/11.43  tff(c_77261, plain, (v1_relat_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_100, c_77260])).
% 21.41/11.43  tff(c_70572, plain, (![A_3]: (r1_tarski('#skF_7', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_70561, c_6])).
% 21.41/11.43  tff(c_73808, plain, (![A_3]: (r1_tarski('#skF_5', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_73763, c_70572])).
% 21.41/11.43  tff(c_73807, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_73763, c_73763, c_70571])).
% 21.41/11.43  tff(c_70568, plain, (![A_36]: (r1_xboole_0('#skF_1'(A_36), A_36) | A_36='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70561, c_48])).
% 21.41/11.43  tff(c_73801, plain, (![A_36]: (r1_xboole_0('#skF_1'(A_36), A_36) | A_36='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_73763, c_70568])).
% 21.41/11.43  tff(c_72638, plain, (![A_22, B_24]: (k7_relat_1(A_22, B_24)='#skF_7' | ~r1_xboole_0(B_24, k1_relat_1(A_22)) | ~v1_relat_1(A_22))), inference(demodulation, [status(thm), theory('equality')], [c_70561, c_24])).
% 21.41/11.43  tff(c_74749, plain, (![A_4080, B_4081]: (k7_relat_1(A_4080, B_4081)='#skF_5' | ~r1_xboole_0(B_4081, k1_relat_1(A_4080)) | ~v1_relat_1(A_4080))), inference(demodulation, [status(thm), theory('equality')], [c_73763, c_72638])).
% 21.41/11.43  tff(c_74781, plain, (![A_4080]: (k7_relat_1(A_4080, '#skF_1'(k1_relat_1(A_4080)))='#skF_5' | ~v1_relat_1(A_4080) | k1_relat_1(A_4080)='#skF_5')), inference(resolution, [status(thm)], [c_73801, c_74749])).
% 21.41/11.43  tff(c_73803, plain, (k9_relat_1('#skF_5', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_73763, c_73763, c_73763, c_70619])).
% 21.41/11.43  tff(c_16, plain, (![A_14]: (k9_relat_1(A_14, k1_relat_1(A_14))=k2_relat_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 21.41/11.43  tff(c_72467, plain, (![B_16, A_15]: (r1_xboole_0(k1_relat_1(B_16), A_15) | k9_relat_1(B_16, A_15)!='#skF_7' | ~v1_relat_1(B_16))), inference(demodulation, [status(thm), theory('equality')], [c_70561, c_20])).
% 21.41/11.43  tff(c_72515, plain, (![B_3893, A_3894]: (k7_relat_1(B_3893, A_3894)='#skF_7' | ~r1_xboole_0(k1_relat_1(B_3893), A_3894) | ~v1_relat_1(B_3893))), inference(demodulation, [status(thm), theory('equality')], [c_70561, c_34])).
% 21.41/11.43  tff(c_72529, plain, (![B_16, A_15]: (k7_relat_1(B_16, A_15)='#skF_7' | k9_relat_1(B_16, A_15)!='#skF_7' | ~v1_relat_1(B_16))), inference(resolution, [status(thm)], [c_72467, c_72515])).
% 21.41/11.43  tff(c_75470, plain, (![B_4128, A_4129]: (k7_relat_1(B_4128, A_4129)='#skF_5' | k9_relat_1(B_4128, A_4129)!='#skF_5' | ~v1_relat_1(B_4128))), inference(demodulation, [status(thm), theory('equality')], [c_73763, c_73763, c_72529])).
% 21.41/11.43  tff(c_76623, plain, (![A_4203]: (k7_relat_1(A_4203, k1_relat_1(A_4203))='#skF_5' | k2_relat_1(A_4203)!='#skF_5' | ~v1_relat_1(A_4203) | ~v1_relat_1(A_4203))), inference(superposition, [status(thm), theory('equality')], [c_16, c_75470])).
% 21.41/11.43  tff(c_73810, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_73763, c_70561])).
% 21.41/11.43  tff(c_7598, plain, (![A_736]: (k2_relat_1(A_736)!=k1_xboole_0 | k1_xboole_0=A_736 | ~v1_relat_1(A_736))), inference(cnfTransformation, [status(thm)], [f_83])).
% 21.41/11.43  tff(c_7602, plain, (![A_12, B_13]: (k2_relat_1(k7_relat_1(A_12, B_13))!=k1_xboole_0 | k7_relat_1(A_12, B_13)=k1_xboole_0 | ~v1_relat_1(A_12))), inference(resolution, [status(thm)], [c_14, c_7598])).
% 21.41/11.43  tff(c_75541, plain, (![A_12, B_13]: (k2_relat_1(k7_relat_1(A_12, B_13))!='#skF_5' | k7_relat_1(A_12, B_13)='#skF_5' | ~v1_relat_1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_73810, c_73810, c_7602])).
% 21.41/11.43  tff(c_76655, plain, (![A_4203]: (k2_relat_1('#skF_5')!='#skF_5' | k7_relat_1(A_4203, k1_relat_1(A_4203))='#skF_5' | ~v1_relat_1(A_4203) | k2_relat_1(A_4203)!='#skF_5' | ~v1_relat_1(A_4203) | ~v1_relat_1(A_4203))), inference(superposition, [status(thm), theory('equality')], [c_76623, c_75541])).
% 21.41/11.43  tff(c_76798, plain, (![A_4204]: (k7_relat_1(A_4204, k1_relat_1(A_4204))='#skF_5' | k2_relat_1(A_4204)!='#skF_5' | ~v1_relat_1(A_4204))), inference(demodulation, [status(thm), theory('equality')], [c_73807, c_76655])).
% 21.41/11.43  tff(c_78019, plain, (![A_4320, B_4321]: (k9_relat_1(A_4320, B_4321)=k9_relat_1('#skF_5', B_4321) | ~r1_tarski(B_4321, k1_relat_1(A_4320)) | ~v1_relat_1(A_4320) | k2_relat_1(A_4320)!='#skF_5' | ~v1_relat_1(A_4320))), inference(superposition, [status(thm), theory('equality')], [c_76798, c_22])).
% 21.41/11.43  tff(c_78026, plain, (![A_4320]: (k9_relat_1(A_4320, '#skF_5')=k9_relat_1('#skF_5', '#skF_5') | k2_relat_1(A_4320)!='#skF_5' | ~v1_relat_1(A_4320))), inference(resolution, [status(thm)], [c_73808, c_78019])).
% 21.41/11.43  tff(c_78050, plain, (![A_4324]: (k9_relat_1(A_4324, '#skF_5')='#skF_5' | k2_relat_1(A_4324)!='#skF_5' | ~v1_relat_1(A_4324))), inference(demodulation, [status(thm), theory('equality')], [c_73803, c_78026])).
% 21.41/11.43  tff(c_78086, plain, (![A_4325, B_4326]: (k9_relat_1(k7_relat_1(A_4325, B_4326), '#skF_5')='#skF_5' | k2_relat_1(k7_relat_1(A_4325, B_4326))!='#skF_5' | ~v1_relat_1(A_4325))), inference(resolution, [status(thm)], [c_14, c_78050])).
% 21.41/11.43  tff(c_78097, plain, (![A_4325, B_4326]: (k9_relat_1(A_4325, '#skF_5')='#skF_5' | ~r1_tarski('#skF_5', B_4326) | ~v1_relat_1(A_4325) | k2_relat_1(k7_relat_1(A_4325, B_4326))!='#skF_5' | ~v1_relat_1(A_4325))), inference(superposition, [status(thm), theory('equality')], [c_78086, c_22])).
% 21.41/11.43  tff(c_78186, plain, (![A_4327, B_4328]: (k9_relat_1(A_4327, '#skF_5')='#skF_5' | k2_relat_1(k7_relat_1(A_4327, B_4328))!='#skF_5' | ~v1_relat_1(A_4327))), inference(demodulation, [status(thm), theory('equality')], [c_73808, c_78097])).
% 21.41/11.43  tff(c_78204, plain, (![A_4080]: (k9_relat_1(A_4080, '#skF_5')='#skF_5' | k2_relat_1('#skF_5')!='#skF_5' | ~v1_relat_1(A_4080) | ~v1_relat_1(A_4080) | k1_relat_1(A_4080)='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_74781, c_78186])).
% 21.41/11.43  tff(c_78257, plain, (![A_4329]: (k9_relat_1(A_4329, '#skF_5')='#skF_5' | ~v1_relat_1(A_4329) | k1_relat_1(A_4329)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_73807, c_78204])).
% 21.41/11.43  tff(c_78435, plain, (![A_4340, B_4341]: (k9_relat_1(k7_relat_1(A_4340, B_4341), '#skF_5')='#skF_5' | k1_relat_1(k7_relat_1(A_4340, B_4341))='#skF_5' | ~v1_relat_1(A_4340))), inference(resolution, [status(thm)], [c_14, c_78257])).
% 21.41/11.43  tff(c_78449, plain, (![A_4340, B_4341]: (k9_relat_1(A_4340, '#skF_5')='#skF_5' | ~r1_tarski('#skF_5', B_4341) | ~v1_relat_1(A_4340) | k1_relat_1(k7_relat_1(A_4340, B_4341))='#skF_5' | ~v1_relat_1(A_4340))), inference(superposition, [status(thm), theory('equality')], [c_78435, c_22])).
% 21.41/11.43  tff(c_78553, plain, (![A_4342, B_4343]: (k9_relat_1(A_4342, '#skF_5')='#skF_5' | k1_relat_1(k7_relat_1(A_4342, B_4343))='#skF_5' | ~v1_relat_1(A_4342))), inference(demodulation, [status(thm), theory('equality')], [c_73808, c_78449])).
% 21.41/11.43  tff(c_7593, plain, (![A_735]: (k1_relat_1(A_735)!=k1_xboole_0 | k1_xboole_0=A_735 | ~v1_relat_1(A_735))), inference(cnfTransformation, [status(thm)], [f_83])).
% 21.41/11.43  tff(c_7597, plain, (![A_12, B_13]: (k1_relat_1(k7_relat_1(A_12, B_13))!=k1_xboole_0 | k7_relat_1(A_12, B_13)=k1_xboole_0 | ~v1_relat_1(A_12))), inference(resolution, [status(thm)], [c_14, c_7593])).
% 21.41/11.43  tff(c_75413, plain, (![A_12, B_13]: (k1_relat_1(k7_relat_1(A_12, B_13))!='#skF_5' | k7_relat_1(A_12, B_13)='#skF_5' | ~v1_relat_1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_73810, c_73810, c_7597])).
% 21.41/11.43  tff(c_78787, plain, (![A_4344, B_4345]: (k7_relat_1(A_4344, B_4345)='#skF_5' | k9_relat_1(A_4344, '#skF_5')='#skF_5' | ~v1_relat_1(A_4344))), inference(superposition, [status(thm), theory('equality')], [c_78553, c_75413])).
% 21.41/11.43  tff(c_78832, plain, (![A_4352, B_4353, B_4354]: (k7_relat_1(k7_relat_1(A_4352, B_4353), B_4354)='#skF_5' | k9_relat_1(k7_relat_1(A_4352, B_4353), '#skF_5')='#skF_5' | ~v1_relat_1(A_4352))), inference(resolution, [status(thm)], [c_14, c_78787])).
% 21.41/11.43  tff(c_78155, plain, (![A_4325, B_4326]: (k9_relat_1(A_4325, '#skF_5')='#skF_5' | k2_relat_1(k7_relat_1(A_4325, B_4326))!='#skF_5' | ~v1_relat_1(A_4325))), inference(demodulation, [status(thm), theory('equality')], [c_73808, c_78097])).
% 21.41/11.43  tff(c_78850, plain, (![A_4352, B_4353]: (k9_relat_1(k7_relat_1(A_4352, B_4353), '#skF_5')='#skF_5' | k2_relat_1('#skF_5')!='#skF_5' | ~v1_relat_1(k7_relat_1(A_4352, B_4353)) | k9_relat_1(k7_relat_1(A_4352, B_4353), '#skF_5')='#skF_5' | ~v1_relat_1(A_4352))), inference(superposition, [status(thm), theory('equality')], [c_78832, c_78155])).
% 21.41/11.43  tff(c_79180, plain, (![A_4355, B_4356]: (~v1_relat_1(k7_relat_1(A_4355, B_4356)) | k9_relat_1(k7_relat_1(A_4355, B_4356), '#skF_5')='#skF_5' | ~v1_relat_1(A_4355))), inference(demodulation, [status(thm), theory('equality')], [c_73807, c_78850])).
% 21.41/11.43  tff(c_79270, plain, (![A_4357, B_4358]: (k9_relat_1(k7_relat_1(A_4357, B_4358), '#skF_5')='#skF_5' | ~v1_relat_1(A_4357))), inference(resolution, [status(thm)], [c_14, c_79180])).
% 21.41/11.43  tff(c_79281, plain, (![A_4357, B_4358]: (k9_relat_1(A_4357, '#skF_5')='#skF_5' | ~r1_tarski('#skF_5', B_4358) | ~v1_relat_1(A_4357) | ~v1_relat_1(A_4357))), inference(superposition, [status(thm), theory('equality')], [c_79270, c_22])).
% 21.41/11.43  tff(c_79395, plain, (![A_4361]: (k9_relat_1(A_4361, '#skF_5')='#skF_5' | ~v1_relat_1(A_4361))), inference(demodulation, [status(thm), theory('equality')], [c_73808, c_79281])).
% 21.41/11.43  tff(c_79420, plain, (k9_relat_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5'), '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_77261, c_79395])).
% 21.41/11.43  tff(c_73765, plain, (![B_16, A_15]: (k7_relat_1(B_16, A_15)='#skF_5' | k9_relat_1(B_16, A_15)!='#skF_5' | ~v1_relat_1(B_16))), inference(demodulation, [status(thm), theory('equality')], [c_73763, c_73763, c_72529])).
% 21.41/11.43  tff(c_79824, plain, (k7_relat_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5'), '#skF_5')='#skF_5' | ~v1_relat_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_79420, c_73765])).
% 21.41/11.43  tff(c_79829, plain, (k7_relat_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5'), '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_77261, c_79824])).
% 21.41/11.43  tff(c_79893, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79847, c_79829])).
% 21.41/11.43  tff(c_79894, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_7591])).
% 21.41/11.43  tff(c_81891, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5'), '#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_81876, c_79894])).
% 21.41/11.43  tff(c_89440, plain, (~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_5')) | k7_relat_1('#skF_5', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_89431, c_81891])).
% 21.41/11.43  tff(c_89451, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_90, c_82820, c_82840, c_81887, c_82840, c_81566, c_81566, c_83932, c_89440])).
% 21.41/11.43  tff(c_89453, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_89451])).
% 21.41/11.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.41/11.43  
% 21.41/11.43  Inference rules
% 21.41/11.43  ----------------------
% 21.41/11.43  #Ref     : 0
% 21.41/11.43  #Sup     : 18177
% 21.41/11.43  #Fact    : 0
% 21.41/11.43  #Define  : 0
% 21.41/11.43  #Split   : 171
% 21.41/11.43  #Chain   : 0
% 21.41/11.43  #Close   : 0
% 21.41/11.43  
% 21.41/11.43  Ordering : KBO
% 21.41/11.43  
% 21.41/11.43  Simplification rules
% 21.41/11.43  ----------------------
% 21.41/11.43  #Subsume      : 3954
% 21.41/11.43  #Demod        : 21814
% 21.41/11.43  #Tautology    : 9523
% 21.41/11.43  #SimpNegUnit  : 1836
% 21.41/11.43  #BackRed      : 704
% 21.41/11.43  
% 21.41/11.43  #Partial instantiations: 0
% 21.41/11.43  #Strategies tried      : 1
% 21.41/11.43  
% 21.41/11.43  Timing (in seconds)
% 21.41/11.43  ----------------------
% 21.41/11.43  Preprocessing        : 0.47
% 21.41/11.43  Parsing              : 0.23
% 21.41/11.43  CNF conversion       : 0.06
% 21.41/11.43  Main loop            : 9.89
% 21.41/11.43  Inferencing          : 2.67
% 21.41/11.43  Reduction            : 3.74
% 21.41/11.43  Demodulation         : 2.75
% 21.41/11.43  BG Simplification    : 0.21
% 21.41/11.43  Subsumption          : 2.73
% 21.41/11.43  Abstraction          : 0.29
% 21.41/11.43  MUC search           : 0.00
% 21.41/11.43  Cooper               : 0.00
% 21.41/11.43  Total                : 10.64
% 21.41/11.43  Index Insertion      : 0.00
% 21.41/11.43  Index Deletion       : 0.00
% 21.41/11.43  Index Matching       : 0.00
% 21.41/11.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
