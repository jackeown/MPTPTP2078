%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:19 EST 2020

% Result     : Theorem 7.81s
% Output     : CNFRefutation 7.81s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 872 expanded)
%              Number of leaves         :   39 ( 332 expanded)
%              Depth                    :   12
%              Number of atoms          :  609 (4587 expanded)
%              Number of equality atoms :  125 ( 967 expanded)
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

tff(f_197,negated_conjecture,(
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

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_57,axiom,(
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

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_155,axiom,(
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

tff(f_121,axiom,(
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

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_52,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_542,plain,(
    ! [A_296,B_297] :
      ( r1_xboole_0(A_296,B_297)
      | ~ r1_subset_1(A_296,B_297)
      | v1_xboole_0(B_297)
      | v1_xboole_0(A_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2511,plain,(
    ! [A_695,B_696] :
      ( k3_xboole_0(A_695,B_696) = k1_xboole_0
      | ~ r1_subset_1(A_695,B_696)
      | v1_xboole_0(B_696)
      | v1_xboole_0(A_695) ) ),
    inference(resolution,[status(thm)],[c_542,c_2])).

tff(c_2514,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_2511])).

tff(c_2517,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_56,c_2514])).

tff(c_44,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_657,plain,(
    ! [A_312,B_313,C_314,D_315] :
      ( k2_partfun1(A_312,B_313,C_314,D_315) = k7_relat_1(C_314,D_315)
      | ~ m1_subset_1(C_314,k1_zfmisc_1(k2_zfmisc_1(A_312,B_313)))
      | ~ v1_funct_1(C_314) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_659,plain,(
    ! [D_315] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_315) = k7_relat_1('#skF_6',D_315)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_40,c_657])).

tff(c_664,plain,(
    ! [D_315] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_315) = k7_relat_1('#skF_6',D_315) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_659])).

tff(c_50,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_661,plain,(
    ! [D_315] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_315) = k7_relat_1('#skF_5',D_315)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_46,c_657])).

tff(c_667,plain,(
    ! [D_315] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_315) = k7_relat_1('#skF_5',D_315) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_661])).

tff(c_556,plain,(
    ! [A_300,B_301,C_302] :
      ( k9_subset_1(A_300,B_301,C_302) = k3_xboole_0(B_301,C_302)
      | ~ m1_subset_1(C_302,k1_zfmisc_1(A_300)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_568,plain,(
    ! [B_301] : k9_subset_1('#skF_1',B_301,'#skF_4') = k3_xboole_0(B_301,'#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_556])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_78,plain,(
    ! [C_219,A_220,B_221] :
      ( v1_relat_1(C_219)
      | ~ m1_subset_1(C_219,k1_zfmisc_1(k2_zfmisc_1(A_220,B_221))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_85,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_78])).

tff(c_97,plain,(
    ! [C_225,A_226,B_227] :
      ( v4_relat_1(C_225,A_226)
      | ~ m1_subset_1(C_225,k1_zfmisc_1(k2_zfmisc_1(A_226,B_227))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_104,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_97])).

tff(c_106,plain,(
    ! [B_228,A_229] :
      ( k7_relat_1(B_228,A_229) = B_228
      | ~ v4_relat_1(B_228,A_229)
      | ~ v1_relat_1(B_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_109,plain,
    ( k7_relat_1('#skF_6','#skF_4') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_104,c_106])).

tff(c_112,plain,(
    k7_relat_1('#skF_6','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_109])).

tff(c_141,plain,(
    ! [C_234,A_235,B_236] :
      ( k7_relat_1(k7_relat_1(C_234,A_235),B_236) = k1_xboole_0
      | ~ r1_xboole_0(A_235,B_236)
      | ~ v1_relat_1(C_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_159,plain,(
    ! [B_236] :
      ( k7_relat_1('#skF_6',B_236) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_236)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_141])).

tff(c_179,plain,(
    ! [B_238] :
      ( k7_relat_1('#skF_6',B_238) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_238) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_159])).

tff(c_191,plain,(
    ! [B_2] :
      ( k7_relat_1('#skF_6',B_2) = k1_xboole_0
      | k3_xboole_0('#skF_4',B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_179])).

tff(c_86,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_78])).

tff(c_105,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_97])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( k7_relat_1(B_11,A_10) = B_11
      | ~ v4_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_115,plain,
    ( k7_relat_1('#skF_5','#skF_3') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_105,c_12])).

tff(c_118,plain,(
    k7_relat_1('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_115])).

tff(c_156,plain,(
    ! [B_236] :
      ( k7_relat_1('#skF_5',B_236) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_236)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_141])).

tff(c_166,plain,(
    ! [B_237] :
      ( k7_relat_1('#skF_5',B_237) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_237) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_156])).

tff(c_178,plain,(
    ! [B_2] :
      ( k7_relat_1('#skF_5',B_2) = k1_xboole_0
      | k3_xboole_0('#skF_3',B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_166])).

tff(c_132,plain,(
    ! [A_232,B_233] :
      ( r1_xboole_0(A_232,B_233)
      | ~ r1_subset_1(A_232,B_233)
      | v1_xboole_0(B_233)
      | v1_xboole_0(A_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_409,plain,(
    ! [A_270,B_271] :
      ( k3_xboole_0(A_270,B_271) = k1_xboole_0
      | ~ r1_subset_1(A_270,B_271)
      | v1_xboole_0(B_271)
      | v1_xboole_0(A_270) ) ),
    inference(resolution,[status(thm)],[c_132,c_2])).

tff(c_415,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_409])).

tff(c_419,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_56,c_415])).

tff(c_275,plain,(
    ! [A_247,B_248,C_249,D_250] :
      ( k2_partfun1(A_247,B_248,C_249,D_250) = k7_relat_1(C_249,D_250)
      | ~ m1_subset_1(C_249,k1_zfmisc_1(k2_zfmisc_1(A_247,B_248)))
      | ~ v1_funct_1(C_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_279,plain,(
    ! [D_250] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_250) = k7_relat_1('#skF_5',D_250)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_46,c_275])).

tff(c_285,plain,(
    ! [D_250] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_250) = k7_relat_1('#skF_5',D_250) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_279])).

tff(c_277,plain,(
    ! [D_250] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_250) = k7_relat_1('#skF_6',D_250)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_40,c_275])).

tff(c_282,plain,(
    ! [D_250] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_250) = k7_relat_1('#skF_6',D_250) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_277])).

tff(c_192,plain,(
    ! [A_239,B_240,C_241] :
      ( k9_subset_1(A_239,B_240,C_241) = k3_xboole_0(B_240,C_241)
      | ~ m1_subset_1(C_241,k1_zfmisc_1(A_239)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_204,plain,(
    ! [B_240] : k9_subset_1('#skF_1',B_240,'#skF_4') = k3_xboole_0(B_240,'#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_192])).

tff(c_38,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_87,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_214,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_204,c_87])).

tff(c_484,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) != k7_relat_1('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_419,c_285,c_282,c_214])).

tff(c_487,plain,
    ( k7_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0
    | k3_xboole_0('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_484])).

tff(c_489,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_487])).

tff(c_492,plain,(
    k3_xboole_0('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_489])).

tff(c_496,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_492])).

tff(c_498,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_578,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_568,c_568,c_498])).

tff(c_2601,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k7_relat_1('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2517,c_2517,c_664,c_667,c_578])).

tff(c_513,plain,(
    ! [C_293,A_294,B_295] :
      ( v4_relat_1(C_293,A_294)
      | ~ m1_subset_1(C_293,k1_zfmisc_1(k2_zfmisc_1(A_294,B_295))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_521,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_513])).

tff(c_530,plain,
    ( k7_relat_1('#skF_5','#skF_3') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_521,c_12])).

tff(c_533,plain,(
    k7_relat_1('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_530])).

tff(c_606,plain,(
    ! [C_307,A_308,B_309] :
      ( k7_relat_1(k7_relat_1(C_307,A_308),B_309) = k1_xboole_0
      | ~ r1_xboole_0(A_308,B_309)
      | ~ v1_relat_1(C_307) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_621,plain,(
    ! [B_309] :
      ( k7_relat_1('#skF_5',B_309) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_309)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_533,c_606])).

tff(c_631,plain,(
    ! [B_310] :
      ( k7_relat_1('#skF_5',B_310) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_310) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_621])).

tff(c_643,plain,(
    ! [B_2] :
      ( k7_relat_1('#skF_5',B_2) = k1_xboole_0
      | k3_xboole_0('#skF_3',B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_631])).

tff(c_2605,plain,
    ( k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0
    | k3_xboole_0('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2601,c_643])).

tff(c_2615,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2605])).

tff(c_2621,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2615,c_2601])).

tff(c_48,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_42,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_2676,plain,(
    ! [F_710,D_713,A_712,B_711,E_709,C_714] :
      ( v1_funct_1(k1_tmap_1(A_712,B_711,C_714,D_713,E_709,F_710))
      | ~ m1_subset_1(F_710,k1_zfmisc_1(k2_zfmisc_1(D_713,B_711)))
      | ~ v1_funct_2(F_710,D_713,B_711)
      | ~ v1_funct_1(F_710)
      | ~ m1_subset_1(E_709,k1_zfmisc_1(k2_zfmisc_1(C_714,B_711)))
      | ~ v1_funct_2(E_709,C_714,B_711)
      | ~ v1_funct_1(E_709)
      | ~ m1_subset_1(D_713,k1_zfmisc_1(A_712))
      | v1_xboole_0(D_713)
      | ~ m1_subset_1(C_714,k1_zfmisc_1(A_712))
      | v1_xboole_0(C_714)
      | v1_xboole_0(B_711)
      | v1_xboole_0(A_712) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_2678,plain,(
    ! [A_712,C_714,E_709] :
      ( v1_funct_1(k1_tmap_1(A_712,'#skF_2',C_714,'#skF_4',E_709,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_709,k1_zfmisc_1(k2_zfmisc_1(C_714,'#skF_2')))
      | ~ v1_funct_2(E_709,C_714,'#skF_2')
      | ~ v1_funct_1(E_709)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_712))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_714,k1_zfmisc_1(A_712))
      | v1_xboole_0(C_714)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_712) ) ),
    inference(resolution,[status(thm)],[c_40,c_2676])).

tff(c_2683,plain,(
    ! [A_712,C_714,E_709] :
      ( v1_funct_1(k1_tmap_1(A_712,'#skF_2',C_714,'#skF_4',E_709,'#skF_6'))
      | ~ m1_subset_1(E_709,k1_zfmisc_1(k2_zfmisc_1(C_714,'#skF_2')))
      | ~ v1_funct_2(E_709,C_714,'#skF_2')
      | ~ v1_funct_1(E_709)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_712))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_714,k1_zfmisc_1(A_712))
      | v1_xboole_0(C_714)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_712) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_2678])).

tff(c_2691,plain,(
    ! [A_715,C_716,E_717] :
      ( v1_funct_1(k1_tmap_1(A_715,'#skF_2',C_716,'#skF_4',E_717,'#skF_6'))
      | ~ m1_subset_1(E_717,k1_zfmisc_1(k2_zfmisc_1(C_716,'#skF_2')))
      | ~ v1_funct_2(E_717,C_716,'#skF_2')
      | ~ v1_funct_1(E_717)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_715))
      | ~ m1_subset_1(C_716,k1_zfmisc_1(A_715))
      | v1_xboole_0(C_716)
      | v1_xboole_0(A_715) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_2683])).

tff(c_2695,plain,(
    ! [A_715] :
      ( v1_funct_1(k1_tmap_1(A_715,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_715))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_715))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_715) ) ),
    inference(resolution,[status(thm)],[c_46,c_2691])).

tff(c_2702,plain,(
    ! [A_715] :
      ( v1_funct_1(k1_tmap_1(A_715,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_715))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_715))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_715) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_2695])).

tff(c_2741,plain,(
    ! [A_733] :
      ( v1_funct_1(k1_tmap_1(A_733,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_733))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_733))
      | v1_xboole_0(A_733) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2702])).

tff(c_2744,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_2741])).

tff(c_2747,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2744])).

tff(c_2748,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2747])).

tff(c_34,plain,(
    ! [E_155,B_152,F_156,C_153,D_154,A_151] :
      ( v1_funct_2(k1_tmap_1(A_151,B_152,C_153,D_154,E_155,F_156),k4_subset_1(A_151,C_153,D_154),B_152)
      | ~ m1_subset_1(F_156,k1_zfmisc_1(k2_zfmisc_1(D_154,B_152)))
      | ~ v1_funct_2(F_156,D_154,B_152)
      | ~ v1_funct_1(F_156)
      | ~ m1_subset_1(E_155,k1_zfmisc_1(k2_zfmisc_1(C_153,B_152)))
      | ~ v1_funct_2(E_155,C_153,B_152)
      | ~ v1_funct_1(E_155)
      | ~ m1_subset_1(D_154,k1_zfmisc_1(A_151))
      | v1_xboole_0(D_154)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(A_151))
      | v1_xboole_0(C_153)
      | v1_xboole_0(B_152)
      | v1_xboole_0(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_32,plain,(
    ! [E_155,B_152,F_156,C_153,D_154,A_151] :
      ( m1_subset_1(k1_tmap_1(A_151,B_152,C_153,D_154,E_155,F_156),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_151,C_153,D_154),B_152)))
      | ~ m1_subset_1(F_156,k1_zfmisc_1(k2_zfmisc_1(D_154,B_152)))
      | ~ v1_funct_2(F_156,D_154,B_152)
      | ~ v1_funct_1(F_156)
      | ~ m1_subset_1(E_155,k1_zfmisc_1(k2_zfmisc_1(C_153,B_152)))
      | ~ v1_funct_2(E_155,C_153,B_152)
      | ~ v1_funct_1(E_155)
      | ~ m1_subset_1(D_154,k1_zfmisc_1(A_151))
      | v1_xboole_0(D_154)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(A_151))
      | v1_xboole_0(C_153)
      | v1_xboole_0(B_152)
      | v1_xboole_0(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_2899,plain,(
    ! [D_757,C_752,F_753,A_754,B_755,E_756] :
      ( k2_partfun1(k4_subset_1(A_754,C_752,D_757),B_755,k1_tmap_1(A_754,B_755,C_752,D_757,E_756,F_753),C_752) = E_756
      | ~ m1_subset_1(k1_tmap_1(A_754,B_755,C_752,D_757,E_756,F_753),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_754,C_752,D_757),B_755)))
      | ~ v1_funct_2(k1_tmap_1(A_754,B_755,C_752,D_757,E_756,F_753),k4_subset_1(A_754,C_752,D_757),B_755)
      | ~ v1_funct_1(k1_tmap_1(A_754,B_755,C_752,D_757,E_756,F_753))
      | k2_partfun1(D_757,B_755,F_753,k9_subset_1(A_754,C_752,D_757)) != k2_partfun1(C_752,B_755,E_756,k9_subset_1(A_754,C_752,D_757))
      | ~ m1_subset_1(F_753,k1_zfmisc_1(k2_zfmisc_1(D_757,B_755)))
      | ~ v1_funct_2(F_753,D_757,B_755)
      | ~ v1_funct_1(F_753)
      | ~ m1_subset_1(E_756,k1_zfmisc_1(k2_zfmisc_1(C_752,B_755)))
      | ~ v1_funct_2(E_756,C_752,B_755)
      | ~ v1_funct_1(E_756)
      | ~ m1_subset_1(D_757,k1_zfmisc_1(A_754))
      | v1_xboole_0(D_757)
      | ~ m1_subset_1(C_752,k1_zfmisc_1(A_754))
      | v1_xboole_0(C_752)
      | v1_xboole_0(B_755)
      | v1_xboole_0(A_754) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_3342,plain,(
    ! [E_874,F_875,D_878,B_876,C_879,A_877] :
      ( k2_partfun1(k4_subset_1(A_877,C_879,D_878),B_876,k1_tmap_1(A_877,B_876,C_879,D_878,E_874,F_875),C_879) = E_874
      | ~ v1_funct_2(k1_tmap_1(A_877,B_876,C_879,D_878,E_874,F_875),k4_subset_1(A_877,C_879,D_878),B_876)
      | ~ v1_funct_1(k1_tmap_1(A_877,B_876,C_879,D_878,E_874,F_875))
      | k2_partfun1(D_878,B_876,F_875,k9_subset_1(A_877,C_879,D_878)) != k2_partfun1(C_879,B_876,E_874,k9_subset_1(A_877,C_879,D_878))
      | ~ m1_subset_1(F_875,k1_zfmisc_1(k2_zfmisc_1(D_878,B_876)))
      | ~ v1_funct_2(F_875,D_878,B_876)
      | ~ v1_funct_1(F_875)
      | ~ m1_subset_1(E_874,k1_zfmisc_1(k2_zfmisc_1(C_879,B_876)))
      | ~ v1_funct_2(E_874,C_879,B_876)
      | ~ v1_funct_1(E_874)
      | ~ m1_subset_1(D_878,k1_zfmisc_1(A_877))
      | v1_xboole_0(D_878)
      | ~ m1_subset_1(C_879,k1_zfmisc_1(A_877))
      | v1_xboole_0(C_879)
      | v1_xboole_0(B_876)
      | v1_xboole_0(A_877) ) ),
    inference(resolution,[status(thm)],[c_32,c_2899])).

tff(c_3749,plain,(
    ! [B_953,C_956,F_952,A_954,D_955,E_951] :
      ( k2_partfun1(k4_subset_1(A_954,C_956,D_955),B_953,k1_tmap_1(A_954,B_953,C_956,D_955,E_951,F_952),C_956) = E_951
      | ~ v1_funct_1(k1_tmap_1(A_954,B_953,C_956,D_955,E_951,F_952))
      | k2_partfun1(D_955,B_953,F_952,k9_subset_1(A_954,C_956,D_955)) != k2_partfun1(C_956,B_953,E_951,k9_subset_1(A_954,C_956,D_955))
      | ~ m1_subset_1(F_952,k1_zfmisc_1(k2_zfmisc_1(D_955,B_953)))
      | ~ v1_funct_2(F_952,D_955,B_953)
      | ~ v1_funct_1(F_952)
      | ~ m1_subset_1(E_951,k1_zfmisc_1(k2_zfmisc_1(C_956,B_953)))
      | ~ v1_funct_2(E_951,C_956,B_953)
      | ~ v1_funct_1(E_951)
      | ~ m1_subset_1(D_955,k1_zfmisc_1(A_954))
      | v1_xboole_0(D_955)
      | ~ m1_subset_1(C_956,k1_zfmisc_1(A_954))
      | v1_xboole_0(C_956)
      | v1_xboole_0(B_953)
      | v1_xboole_0(A_954) ) ),
    inference(resolution,[status(thm)],[c_34,c_3342])).

tff(c_3753,plain,(
    ! [A_954,C_956,E_951] :
      ( k2_partfun1(k4_subset_1(A_954,C_956,'#skF_4'),'#skF_2',k1_tmap_1(A_954,'#skF_2',C_956,'#skF_4',E_951,'#skF_6'),C_956) = E_951
      | ~ v1_funct_1(k1_tmap_1(A_954,'#skF_2',C_956,'#skF_4',E_951,'#skF_6'))
      | k2_partfun1(C_956,'#skF_2',E_951,k9_subset_1(A_954,C_956,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_954,C_956,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_951,k1_zfmisc_1(k2_zfmisc_1(C_956,'#skF_2')))
      | ~ v1_funct_2(E_951,C_956,'#skF_2')
      | ~ v1_funct_1(E_951)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_954))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_956,k1_zfmisc_1(A_954))
      | v1_xboole_0(C_956)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_954) ) ),
    inference(resolution,[status(thm)],[c_40,c_3749])).

tff(c_3759,plain,(
    ! [A_954,C_956,E_951] :
      ( k2_partfun1(k4_subset_1(A_954,C_956,'#skF_4'),'#skF_2',k1_tmap_1(A_954,'#skF_2',C_956,'#skF_4',E_951,'#skF_6'),C_956) = E_951
      | ~ v1_funct_1(k1_tmap_1(A_954,'#skF_2',C_956,'#skF_4',E_951,'#skF_6'))
      | k2_partfun1(C_956,'#skF_2',E_951,k9_subset_1(A_954,C_956,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_954,C_956,'#skF_4'))
      | ~ m1_subset_1(E_951,k1_zfmisc_1(k2_zfmisc_1(C_956,'#skF_2')))
      | ~ v1_funct_2(E_951,C_956,'#skF_2')
      | ~ v1_funct_1(E_951)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_954))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_956,k1_zfmisc_1(A_954))
      | v1_xboole_0(C_956)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_954) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_664,c_3753])).

tff(c_4134,plain,(
    ! [A_1034,C_1035,E_1036] :
      ( k2_partfun1(k4_subset_1(A_1034,C_1035,'#skF_4'),'#skF_2',k1_tmap_1(A_1034,'#skF_2',C_1035,'#skF_4',E_1036,'#skF_6'),C_1035) = E_1036
      | ~ v1_funct_1(k1_tmap_1(A_1034,'#skF_2',C_1035,'#skF_4',E_1036,'#skF_6'))
      | k2_partfun1(C_1035,'#skF_2',E_1036,k9_subset_1(A_1034,C_1035,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1034,C_1035,'#skF_4'))
      | ~ m1_subset_1(E_1036,k1_zfmisc_1(k2_zfmisc_1(C_1035,'#skF_2')))
      | ~ v1_funct_2(E_1036,C_1035,'#skF_2')
      | ~ v1_funct_1(E_1036)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1034))
      | ~ m1_subset_1(C_1035,k1_zfmisc_1(A_1034))
      | v1_xboole_0(C_1035)
      | v1_xboole_0(A_1034) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_3759])).

tff(c_4141,plain,(
    ! [A_1034] :
      ( k2_partfun1(k4_subset_1(A_1034,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1034,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1034,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1034,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1034,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1034))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1034))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1034) ) ),
    inference(resolution,[status(thm)],[c_46,c_4134])).

tff(c_4151,plain,(
    ! [A_1034] :
      ( k2_partfun1(k4_subset_1(A_1034,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1034,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1034,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1034,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1034,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1034))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1034))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1034) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_667,c_4141])).

tff(c_4153,plain,(
    ! [A_1037] :
      ( k2_partfun1(k4_subset_1(A_1037,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1037,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1037,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1037,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1037,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1037))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1037))
      | v1_xboole_0(A_1037) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_4151])).

tff(c_799,plain,(
    ! [A_327,B_328] :
      ( k3_xboole_0(A_327,B_328) = k1_xboole_0
      | ~ r1_subset_1(A_327,B_328)
      | v1_xboole_0(B_328)
      | v1_xboole_0(A_327) ) ),
    inference(resolution,[status(thm)],[c_542,c_2])).

tff(c_805,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_799])).

tff(c_809,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_56,c_805])).

tff(c_832,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k7_relat_1('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_809,c_809,c_667,c_664,c_578])).

tff(c_836,plain,
    ( k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0
    | k3_xboole_0('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_832,c_643])).

tff(c_846,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_836])).

tff(c_852,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_846,c_832])).

tff(c_907,plain,(
    ! [A_337,E_334,C_339,D_338,B_336,F_335] :
      ( v1_funct_1(k1_tmap_1(A_337,B_336,C_339,D_338,E_334,F_335))
      | ~ m1_subset_1(F_335,k1_zfmisc_1(k2_zfmisc_1(D_338,B_336)))
      | ~ v1_funct_2(F_335,D_338,B_336)
      | ~ v1_funct_1(F_335)
      | ~ m1_subset_1(E_334,k1_zfmisc_1(k2_zfmisc_1(C_339,B_336)))
      | ~ v1_funct_2(E_334,C_339,B_336)
      | ~ v1_funct_1(E_334)
      | ~ m1_subset_1(D_338,k1_zfmisc_1(A_337))
      | v1_xboole_0(D_338)
      | ~ m1_subset_1(C_339,k1_zfmisc_1(A_337))
      | v1_xboole_0(C_339)
      | v1_xboole_0(B_336)
      | v1_xboole_0(A_337) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_909,plain,(
    ! [A_337,C_339,E_334] :
      ( v1_funct_1(k1_tmap_1(A_337,'#skF_2',C_339,'#skF_4',E_334,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_334,k1_zfmisc_1(k2_zfmisc_1(C_339,'#skF_2')))
      | ~ v1_funct_2(E_334,C_339,'#skF_2')
      | ~ v1_funct_1(E_334)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_337))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_339,k1_zfmisc_1(A_337))
      | v1_xboole_0(C_339)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_337) ) ),
    inference(resolution,[status(thm)],[c_40,c_907])).

tff(c_914,plain,(
    ! [A_337,C_339,E_334] :
      ( v1_funct_1(k1_tmap_1(A_337,'#skF_2',C_339,'#skF_4',E_334,'#skF_6'))
      | ~ m1_subset_1(E_334,k1_zfmisc_1(k2_zfmisc_1(C_339,'#skF_2')))
      | ~ v1_funct_2(E_334,C_339,'#skF_2')
      | ~ v1_funct_1(E_334)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_337))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_339,k1_zfmisc_1(A_337))
      | v1_xboole_0(C_339)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_337) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_909])).

tff(c_942,plain,(
    ! [A_341,C_342,E_343] :
      ( v1_funct_1(k1_tmap_1(A_341,'#skF_2',C_342,'#skF_4',E_343,'#skF_6'))
      | ~ m1_subset_1(E_343,k1_zfmisc_1(k2_zfmisc_1(C_342,'#skF_2')))
      | ~ v1_funct_2(E_343,C_342,'#skF_2')
      | ~ v1_funct_1(E_343)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_341))
      | ~ m1_subset_1(C_342,k1_zfmisc_1(A_341))
      | v1_xboole_0(C_342)
      | v1_xboole_0(A_341) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_914])).

tff(c_946,plain,(
    ! [A_341] :
      ( v1_funct_1(k1_tmap_1(A_341,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_341))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_341))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_341) ) ),
    inference(resolution,[status(thm)],[c_46,c_942])).

tff(c_953,plain,(
    ! [A_341] :
      ( v1_funct_1(k1_tmap_1(A_341,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_341))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_341))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_341) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_946])).

tff(c_977,plain,(
    ! [A_355] :
      ( v1_funct_1(k1_tmap_1(A_355,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_355))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_355))
      | v1_xboole_0(A_355) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_953])).

tff(c_980,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_977])).

tff(c_983,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_980])).

tff(c_984,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_983])).

tff(c_1133,plain,(
    ! [B_386,A_385,D_388,C_383,F_384,E_387] :
      ( k2_partfun1(k4_subset_1(A_385,C_383,D_388),B_386,k1_tmap_1(A_385,B_386,C_383,D_388,E_387,F_384),D_388) = F_384
      | ~ m1_subset_1(k1_tmap_1(A_385,B_386,C_383,D_388,E_387,F_384),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_385,C_383,D_388),B_386)))
      | ~ v1_funct_2(k1_tmap_1(A_385,B_386,C_383,D_388,E_387,F_384),k4_subset_1(A_385,C_383,D_388),B_386)
      | ~ v1_funct_1(k1_tmap_1(A_385,B_386,C_383,D_388,E_387,F_384))
      | k2_partfun1(D_388,B_386,F_384,k9_subset_1(A_385,C_383,D_388)) != k2_partfun1(C_383,B_386,E_387,k9_subset_1(A_385,C_383,D_388))
      | ~ m1_subset_1(F_384,k1_zfmisc_1(k2_zfmisc_1(D_388,B_386)))
      | ~ v1_funct_2(F_384,D_388,B_386)
      | ~ v1_funct_1(F_384)
      | ~ m1_subset_1(E_387,k1_zfmisc_1(k2_zfmisc_1(C_383,B_386)))
      | ~ v1_funct_2(E_387,C_383,B_386)
      | ~ v1_funct_1(E_387)
      | ~ m1_subset_1(D_388,k1_zfmisc_1(A_385))
      | v1_xboole_0(D_388)
      | ~ m1_subset_1(C_383,k1_zfmisc_1(A_385))
      | v1_xboole_0(C_383)
      | v1_xboole_0(B_386)
      | v1_xboole_0(A_385) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1588,plain,(
    ! [E_488,C_493,A_491,F_489,D_492,B_490] :
      ( k2_partfun1(k4_subset_1(A_491,C_493,D_492),B_490,k1_tmap_1(A_491,B_490,C_493,D_492,E_488,F_489),D_492) = F_489
      | ~ v1_funct_2(k1_tmap_1(A_491,B_490,C_493,D_492,E_488,F_489),k4_subset_1(A_491,C_493,D_492),B_490)
      | ~ v1_funct_1(k1_tmap_1(A_491,B_490,C_493,D_492,E_488,F_489))
      | k2_partfun1(D_492,B_490,F_489,k9_subset_1(A_491,C_493,D_492)) != k2_partfun1(C_493,B_490,E_488,k9_subset_1(A_491,C_493,D_492))
      | ~ m1_subset_1(F_489,k1_zfmisc_1(k2_zfmisc_1(D_492,B_490)))
      | ~ v1_funct_2(F_489,D_492,B_490)
      | ~ v1_funct_1(F_489)
      | ~ m1_subset_1(E_488,k1_zfmisc_1(k2_zfmisc_1(C_493,B_490)))
      | ~ v1_funct_2(E_488,C_493,B_490)
      | ~ v1_funct_1(E_488)
      | ~ m1_subset_1(D_492,k1_zfmisc_1(A_491))
      | v1_xboole_0(D_492)
      | ~ m1_subset_1(C_493,k1_zfmisc_1(A_491))
      | v1_xboole_0(C_493)
      | v1_xboole_0(B_490)
      | v1_xboole_0(A_491) ) ),
    inference(resolution,[status(thm)],[c_32,c_1133])).

tff(c_2019,plain,(
    ! [B_587,D_589,A_588,F_586,E_585,C_590] :
      ( k2_partfun1(k4_subset_1(A_588,C_590,D_589),B_587,k1_tmap_1(A_588,B_587,C_590,D_589,E_585,F_586),D_589) = F_586
      | ~ v1_funct_1(k1_tmap_1(A_588,B_587,C_590,D_589,E_585,F_586))
      | k2_partfun1(D_589,B_587,F_586,k9_subset_1(A_588,C_590,D_589)) != k2_partfun1(C_590,B_587,E_585,k9_subset_1(A_588,C_590,D_589))
      | ~ m1_subset_1(F_586,k1_zfmisc_1(k2_zfmisc_1(D_589,B_587)))
      | ~ v1_funct_2(F_586,D_589,B_587)
      | ~ v1_funct_1(F_586)
      | ~ m1_subset_1(E_585,k1_zfmisc_1(k2_zfmisc_1(C_590,B_587)))
      | ~ v1_funct_2(E_585,C_590,B_587)
      | ~ v1_funct_1(E_585)
      | ~ m1_subset_1(D_589,k1_zfmisc_1(A_588))
      | v1_xboole_0(D_589)
      | ~ m1_subset_1(C_590,k1_zfmisc_1(A_588))
      | v1_xboole_0(C_590)
      | v1_xboole_0(B_587)
      | v1_xboole_0(A_588) ) ),
    inference(resolution,[status(thm)],[c_34,c_1588])).

tff(c_2023,plain,(
    ! [A_588,C_590,E_585] :
      ( k2_partfun1(k4_subset_1(A_588,C_590,'#skF_4'),'#skF_2',k1_tmap_1(A_588,'#skF_2',C_590,'#skF_4',E_585,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_588,'#skF_2',C_590,'#skF_4',E_585,'#skF_6'))
      | k2_partfun1(C_590,'#skF_2',E_585,k9_subset_1(A_588,C_590,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_588,C_590,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_585,k1_zfmisc_1(k2_zfmisc_1(C_590,'#skF_2')))
      | ~ v1_funct_2(E_585,C_590,'#skF_2')
      | ~ v1_funct_1(E_585)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_588))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_590,k1_zfmisc_1(A_588))
      | v1_xboole_0(C_590)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_588) ) ),
    inference(resolution,[status(thm)],[c_40,c_2019])).

tff(c_2029,plain,(
    ! [A_588,C_590,E_585] :
      ( k2_partfun1(k4_subset_1(A_588,C_590,'#skF_4'),'#skF_2',k1_tmap_1(A_588,'#skF_2',C_590,'#skF_4',E_585,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_588,'#skF_2',C_590,'#skF_4',E_585,'#skF_6'))
      | k2_partfun1(C_590,'#skF_2',E_585,k9_subset_1(A_588,C_590,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_588,C_590,'#skF_4'))
      | ~ m1_subset_1(E_585,k1_zfmisc_1(k2_zfmisc_1(C_590,'#skF_2')))
      | ~ v1_funct_2(E_585,C_590,'#skF_2')
      | ~ v1_funct_1(E_585)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_588))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_590,k1_zfmisc_1(A_588))
      | v1_xboole_0(C_590)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_588) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_664,c_2023])).

tff(c_2364,plain,(
    ! [A_673,C_674,E_675] :
      ( k2_partfun1(k4_subset_1(A_673,C_674,'#skF_4'),'#skF_2',k1_tmap_1(A_673,'#skF_2',C_674,'#skF_4',E_675,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_673,'#skF_2',C_674,'#skF_4',E_675,'#skF_6'))
      | k2_partfun1(C_674,'#skF_2',E_675,k9_subset_1(A_673,C_674,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_673,C_674,'#skF_4'))
      | ~ m1_subset_1(E_675,k1_zfmisc_1(k2_zfmisc_1(C_674,'#skF_2')))
      | ~ v1_funct_2(E_675,C_674,'#skF_2')
      | ~ v1_funct_1(E_675)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_673))
      | ~ m1_subset_1(C_674,k1_zfmisc_1(A_673))
      | v1_xboole_0(C_674)
      | v1_xboole_0(A_673) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_2029])).

tff(c_2371,plain,(
    ! [A_673] :
      ( k2_partfun1(k4_subset_1(A_673,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_673,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_673,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_673,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_673,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_673))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_673))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_673) ) ),
    inference(resolution,[status(thm)],[c_46,c_2364])).

tff(c_2381,plain,(
    ! [A_673] :
      ( k2_partfun1(k4_subset_1(A_673,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_673,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_673,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_673,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_673,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_673))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_673))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_673) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_667,c_2371])).

tff(c_2446,plain,(
    ! [A_690] :
      ( k2_partfun1(k4_subset_1(A_690,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_690,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_690,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_690,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_690,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_690))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_690))
      | v1_xboole_0(A_690) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2381])).

tff(c_497,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_744,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_497])).

tff(c_2457,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2446,c_744])).

tff(c_2471,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_852,c_846,c_809,c_809,c_568,c_568,c_984,c_2457])).

tff(c_2473,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2471])).

tff(c_2474,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_497])).

tff(c_4162,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4153,c_2474])).

tff(c_4173,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_2621,c_2615,c_2517,c_2517,c_568,c_568,c_2748,c_4162])).

tff(c_4175,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_4173])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:37:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.81/2.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.81/2.63  
% 7.81/2.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.81/2.63  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.81/2.63  
% 7.81/2.63  %Foreground sorts:
% 7.81/2.63  
% 7.81/2.63  
% 7.81/2.63  %Background operators:
% 7.81/2.63  
% 7.81/2.63  
% 7.81/2.63  %Foreground operators:
% 7.81/2.63  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 7.81/2.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.81/2.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.81/2.63  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.81/2.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.81/2.63  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 7.81/2.63  tff('#skF_5', type, '#skF_5': $i).
% 7.81/2.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.81/2.63  tff('#skF_6', type, '#skF_6': $i).
% 7.81/2.63  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.81/2.63  tff('#skF_2', type, '#skF_2': $i).
% 7.81/2.63  tff('#skF_3', type, '#skF_3': $i).
% 7.81/2.63  tff('#skF_1', type, '#skF_1': $i).
% 7.81/2.63  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.81/2.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.81/2.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.81/2.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.81/2.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.81/2.63  tff('#skF_4', type, '#skF_4': $i).
% 7.81/2.63  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.81/2.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.81/2.63  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 7.81/2.63  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.81/2.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.81/2.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.81/2.63  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.81/2.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.81/2.63  
% 7.81/2.66  tff(f_197, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 7.81/2.66  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 7.81/2.66  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 7.81/2.66  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 7.81/2.66  tff(f_73, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 7.81/2.66  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 7.81/2.66  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.81/2.66  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.81/2.66  tff(f_47, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 7.81/2.66  tff(f_41, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 7.81/2.66  tff(f_155, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 7.81/2.66  tff(f_121, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 7.81/2.66  tff(c_64, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.81/2.66  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.81/2.66  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.81/2.66  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.81/2.66  tff(c_60, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.81/2.66  tff(c_56, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.81/2.66  tff(c_52, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.81/2.66  tff(c_542, plain, (![A_296, B_297]: (r1_xboole_0(A_296, B_297) | ~r1_subset_1(A_296, B_297) | v1_xboole_0(B_297) | v1_xboole_0(A_296))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.81/2.66  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.81/2.66  tff(c_2511, plain, (![A_695, B_696]: (k3_xboole_0(A_695, B_696)=k1_xboole_0 | ~r1_subset_1(A_695, B_696) | v1_xboole_0(B_696) | v1_xboole_0(A_695))), inference(resolution, [status(thm)], [c_542, c_2])).
% 7.81/2.66  tff(c_2514, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_2511])).
% 7.81/2.66  tff(c_2517, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_60, c_56, c_2514])).
% 7.81/2.66  tff(c_44, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.81/2.66  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.81/2.66  tff(c_657, plain, (![A_312, B_313, C_314, D_315]: (k2_partfun1(A_312, B_313, C_314, D_315)=k7_relat_1(C_314, D_315) | ~m1_subset_1(C_314, k1_zfmisc_1(k2_zfmisc_1(A_312, B_313))) | ~v1_funct_1(C_314))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.81/2.66  tff(c_659, plain, (![D_315]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_315)=k7_relat_1('#skF_6', D_315) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_40, c_657])).
% 7.81/2.66  tff(c_664, plain, (![D_315]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_315)=k7_relat_1('#skF_6', D_315))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_659])).
% 7.81/2.66  tff(c_50, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.81/2.66  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.81/2.66  tff(c_661, plain, (![D_315]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_315)=k7_relat_1('#skF_5', D_315) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_46, c_657])).
% 7.81/2.66  tff(c_667, plain, (![D_315]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_315)=k7_relat_1('#skF_5', D_315))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_661])).
% 7.81/2.66  tff(c_556, plain, (![A_300, B_301, C_302]: (k9_subset_1(A_300, B_301, C_302)=k3_xboole_0(B_301, C_302) | ~m1_subset_1(C_302, k1_zfmisc_1(A_300)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.81/2.66  tff(c_568, plain, (![B_301]: (k9_subset_1('#skF_1', B_301, '#skF_4')=k3_xboole_0(B_301, '#skF_4'))), inference(resolution, [status(thm)], [c_54, c_556])).
% 7.81/2.66  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.81/2.66  tff(c_78, plain, (![C_219, A_220, B_221]: (v1_relat_1(C_219) | ~m1_subset_1(C_219, k1_zfmisc_1(k2_zfmisc_1(A_220, B_221))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.81/2.66  tff(c_85, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_40, c_78])).
% 7.81/2.66  tff(c_97, plain, (![C_225, A_226, B_227]: (v4_relat_1(C_225, A_226) | ~m1_subset_1(C_225, k1_zfmisc_1(k2_zfmisc_1(A_226, B_227))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.81/2.66  tff(c_104, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_97])).
% 7.81/2.66  tff(c_106, plain, (![B_228, A_229]: (k7_relat_1(B_228, A_229)=B_228 | ~v4_relat_1(B_228, A_229) | ~v1_relat_1(B_228))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.81/2.66  tff(c_109, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_104, c_106])).
% 7.81/2.66  tff(c_112, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_85, c_109])).
% 7.81/2.66  tff(c_141, plain, (![C_234, A_235, B_236]: (k7_relat_1(k7_relat_1(C_234, A_235), B_236)=k1_xboole_0 | ~r1_xboole_0(A_235, B_236) | ~v1_relat_1(C_234))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.81/2.66  tff(c_159, plain, (![B_236]: (k7_relat_1('#skF_6', B_236)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_236) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_141])).
% 7.81/2.66  tff(c_179, plain, (![B_238]: (k7_relat_1('#skF_6', B_238)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_238))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_159])).
% 7.81/2.66  tff(c_191, plain, (![B_2]: (k7_relat_1('#skF_6', B_2)=k1_xboole_0 | k3_xboole_0('#skF_4', B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_179])).
% 7.81/2.66  tff(c_86, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_78])).
% 7.81/2.66  tff(c_105, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_97])).
% 7.81/2.66  tff(c_12, plain, (![B_11, A_10]: (k7_relat_1(B_11, A_10)=B_11 | ~v4_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.81/2.66  tff(c_115, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_105, c_12])).
% 7.81/2.66  tff(c_118, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_115])).
% 7.81/2.66  tff(c_156, plain, (![B_236]: (k7_relat_1('#skF_5', B_236)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_236) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_118, c_141])).
% 7.81/2.66  tff(c_166, plain, (![B_237]: (k7_relat_1('#skF_5', B_237)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_237))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_156])).
% 7.81/2.66  tff(c_178, plain, (![B_2]: (k7_relat_1('#skF_5', B_2)=k1_xboole_0 | k3_xboole_0('#skF_3', B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_166])).
% 7.81/2.66  tff(c_132, plain, (![A_232, B_233]: (r1_xboole_0(A_232, B_233) | ~r1_subset_1(A_232, B_233) | v1_xboole_0(B_233) | v1_xboole_0(A_232))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.81/2.66  tff(c_409, plain, (![A_270, B_271]: (k3_xboole_0(A_270, B_271)=k1_xboole_0 | ~r1_subset_1(A_270, B_271) | v1_xboole_0(B_271) | v1_xboole_0(A_270))), inference(resolution, [status(thm)], [c_132, c_2])).
% 7.81/2.66  tff(c_415, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_409])).
% 7.81/2.66  tff(c_419, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_60, c_56, c_415])).
% 7.81/2.66  tff(c_275, plain, (![A_247, B_248, C_249, D_250]: (k2_partfun1(A_247, B_248, C_249, D_250)=k7_relat_1(C_249, D_250) | ~m1_subset_1(C_249, k1_zfmisc_1(k2_zfmisc_1(A_247, B_248))) | ~v1_funct_1(C_249))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.81/2.66  tff(c_279, plain, (![D_250]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_250)=k7_relat_1('#skF_5', D_250) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_46, c_275])).
% 7.81/2.66  tff(c_285, plain, (![D_250]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_250)=k7_relat_1('#skF_5', D_250))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_279])).
% 7.81/2.66  tff(c_277, plain, (![D_250]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_250)=k7_relat_1('#skF_6', D_250) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_40, c_275])).
% 7.81/2.66  tff(c_282, plain, (![D_250]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_250)=k7_relat_1('#skF_6', D_250))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_277])).
% 7.81/2.66  tff(c_192, plain, (![A_239, B_240, C_241]: (k9_subset_1(A_239, B_240, C_241)=k3_xboole_0(B_240, C_241) | ~m1_subset_1(C_241, k1_zfmisc_1(A_239)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.81/2.66  tff(c_204, plain, (![B_240]: (k9_subset_1('#skF_1', B_240, '#skF_4')=k3_xboole_0(B_240, '#skF_4'))), inference(resolution, [status(thm)], [c_54, c_192])).
% 7.81/2.66  tff(c_38, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.81/2.66  tff(c_87, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_38])).
% 7.81/2.66  tff(c_214, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_204, c_87])).
% 7.81/2.66  tff(c_484, plain, (k7_relat_1('#skF_5', k1_xboole_0)!=k7_relat_1('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_419, c_419, c_285, c_282, c_214])).
% 7.81/2.66  tff(c_487, plain, (k7_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0 | k3_xboole_0('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_178, c_484])).
% 7.81/2.66  tff(c_489, plain, (k7_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6, c_487])).
% 7.81/2.66  tff(c_492, plain, (k3_xboole_0('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_191, c_489])).
% 7.81/2.66  tff(c_496, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_492])).
% 7.81/2.66  tff(c_498, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_38])).
% 7.81/2.66  tff(c_578, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_568, c_568, c_498])).
% 7.81/2.66  tff(c_2601, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k7_relat_1('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2517, c_2517, c_664, c_667, c_578])).
% 7.81/2.66  tff(c_513, plain, (![C_293, A_294, B_295]: (v4_relat_1(C_293, A_294) | ~m1_subset_1(C_293, k1_zfmisc_1(k2_zfmisc_1(A_294, B_295))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.81/2.66  tff(c_521, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_513])).
% 7.81/2.66  tff(c_530, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_521, c_12])).
% 7.81/2.66  tff(c_533, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_530])).
% 7.81/2.66  tff(c_606, plain, (![C_307, A_308, B_309]: (k7_relat_1(k7_relat_1(C_307, A_308), B_309)=k1_xboole_0 | ~r1_xboole_0(A_308, B_309) | ~v1_relat_1(C_307))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.81/2.66  tff(c_621, plain, (![B_309]: (k7_relat_1('#skF_5', B_309)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_309) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_533, c_606])).
% 7.81/2.66  tff(c_631, plain, (![B_310]: (k7_relat_1('#skF_5', B_310)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_310))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_621])).
% 7.81/2.66  tff(c_643, plain, (![B_2]: (k7_relat_1('#skF_5', B_2)=k1_xboole_0 | k3_xboole_0('#skF_3', B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_631])).
% 7.81/2.66  tff(c_2605, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0 | k3_xboole_0('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2601, c_643])).
% 7.81/2.66  tff(c_2615, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2605])).
% 7.81/2.66  tff(c_2621, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2615, c_2601])).
% 7.81/2.66  tff(c_48, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.81/2.66  tff(c_62, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.81/2.66  tff(c_42, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.81/2.66  tff(c_2676, plain, (![F_710, D_713, A_712, B_711, E_709, C_714]: (v1_funct_1(k1_tmap_1(A_712, B_711, C_714, D_713, E_709, F_710)) | ~m1_subset_1(F_710, k1_zfmisc_1(k2_zfmisc_1(D_713, B_711))) | ~v1_funct_2(F_710, D_713, B_711) | ~v1_funct_1(F_710) | ~m1_subset_1(E_709, k1_zfmisc_1(k2_zfmisc_1(C_714, B_711))) | ~v1_funct_2(E_709, C_714, B_711) | ~v1_funct_1(E_709) | ~m1_subset_1(D_713, k1_zfmisc_1(A_712)) | v1_xboole_0(D_713) | ~m1_subset_1(C_714, k1_zfmisc_1(A_712)) | v1_xboole_0(C_714) | v1_xboole_0(B_711) | v1_xboole_0(A_712))), inference(cnfTransformation, [status(thm)], [f_155])).
% 7.81/2.66  tff(c_2678, plain, (![A_712, C_714, E_709]: (v1_funct_1(k1_tmap_1(A_712, '#skF_2', C_714, '#skF_4', E_709, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_709, k1_zfmisc_1(k2_zfmisc_1(C_714, '#skF_2'))) | ~v1_funct_2(E_709, C_714, '#skF_2') | ~v1_funct_1(E_709) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_712)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_714, k1_zfmisc_1(A_712)) | v1_xboole_0(C_714) | v1_xboole_0('#skF_2') | v1_xboole_0(A_712))), inference(resolution, [status(thm)], [c_40, c_2676])).
% 7.81/2.66  tff(c_2683, plain, (![A_712, C_714, E_709]: (v1_funct_1(k1_tmap_1(A_712, '#skF_2', C_714, '#skF_4', E_709, '#skF_6')) | ~m1_subset_1(E_709, k1_zfmisc_1(k2_zfmisc_1(C_714, '#skF_2'))) | ~v1_funct_2(E_709, C_714, '#skF_2') | ~v1_funct_1(E_709) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_712)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_714, k1_zfmisc_1(A_712)) | v1_xboole_0(C_714) | v1_xboole_0('#skF_2') | v1_xboole_0(A_712))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_2678])).
% 7.81/2.66  tff(c_2691, plain, (![A_715, C_716, E_717]: (v1_funct_1(k1_tmap_1(A_715, '#skF_2', C_716, '#skF_4', E_717, '#skF_6')) | ~m1_subset_1(E_717, k1_zfmisc_1(k2_zfmisc_1(C_716, '#skF_2'))) | ~v1_funct_2(E_717, C_716, '#skF_2') | ~v1_funct_1(E_717) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_715)) | ~m1_subset_1(C_716, k1_zfmisc_1(A_715)) | v1_xboole_0(C_716) | v1_xboole_0(A_715))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_2683])).
% 7.81/2.66  tff(c_2695, plain, (![A_715]: (v1_funct_1(k1_tmap_1(A_715, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_715)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_715)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_715))), inference(resolution, [status(thm)], [c_46, c_2691])).
% 7.81/2.66  tff(c_2702, plain, (![A_715]: (v1_funct_1(k1_tmap_1(A_715, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_715)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_715)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_715))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_2695])).
% 7.81/2.66  tff(c_2741, plain, (![A_733]: (v1_funct_1(k1_tmap_1(A_733, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_733)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_733)) | v1_xboole_0(A_733))), inference(negUnitSimplification, [status(thm)], [c_60, c_2702])).
% 7.81/2.66  tff(c_2744, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_58, c_2741])).
% 7.81/2.66  tff(c_2747, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2744])).
% 7.81/2.66  tff(c_2748, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_64, c_2747])).
% 7.81/2.66  tff(c_34, plain, (![E_155, B_152, F_156, C_153, D_154, A_151]: (v1_funct_2(k1_tmap_1(A_151, B_152, C_153, D_154, E_155, F_156), k4_subset_1(A_151, C_153, D_154), B_152) | ~m1_subset_1(F_156, k1_zfmisc_1(k2_zfmisc_1(D_154, B_152))) | ~v1_funct_2(F_156, D_154, B_152) | ~v1_funct_1(F_156) | ~m1_subset_1(E_155, k1_zfmisc_1(k2_zfmisc_1(C_153, B_152))) | ~v1_funct_2(E_155, C_153, B_152) | ~v1_funct_1(E_155) | ~m1_subset_1(D_154, k1_zfmisc_1(A_151)) | v1_xboole_0(D_154) | ~m1_subset_1(C_153, k1_zfmisc_1(A_151)) | v1_xboole_0(C_153) | v1_xboole_0(B_152) | v1_xboole_0(A_151))), inference(cnfTransformation, [status(thm)], [f_155])).
% 7.81/2.66  tff(c_32, plain, (![E_155, B_152, F_156, C_153, D_154, A_151]: (m1_subset_1(k1_tmap_1(A_151, B_152, C_153, D_154, E_155, F_156), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_151, C_153, D_154), B_152))) | ~m1_subset_1(F_156, k1_zfmisc_1(k2_zfmisc_1(D_154, B_152))) | ~v1_funct_2(F_156, D_154, B_152) | ~v1_funct_1(F_156) | ~m1_subset_1(E_155, k1_zfmisc_1(k2_zfmisc_1(C_153, B_152))) | ~v1_funct_2(E_155, C_153, B_152) | ~v1_funct_1(E_155) | ~m1_subset_1(D_154, k1_zfmisc_1(A_151)) | v1_xboole_0(D_154) | ~m1_subset_1(C_153, k1_zfmisc_1(A_151)) | v1_xboole_0(C_153) | v1_xboole_0(B_152) | v1_xboole_0(A_151))), inference(cnfTransformation, [status(thm)], [f_155])).
% 7.81/2.66  tff(c_2899, plain, (![D_757, C_752, F_753, A_754, B_755, E_756]: (k2_partfun1(k4_subset_1(A_754, C_752, D_757), B_755, k1_tmap_1(A_754, B_755, C_752, D_757, E_756, F_753), C_752)=E_756 | ~m1_subset_1(k1_tmap_1(A_754, B_755, C_752, D_757, E_756, F_753), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_754, C_752, D_757), B_755))) | ~v1_funct_2(k1_tmap_1(A_754, B_755, C_752, D_757, E_756, F_753), k4_subset_1(A_754, C_752, D_757), B_755) | ~v1_funct_1(k1_tmap_1(A_754, B_755, C_752, D_757, E_756, F_753)) | k2_partfun1(D_757, B_755, F_753, k9_subset_1(A_754, C_752, D_757))!=k2_partfun1(C_752, B_755, E_756, k9_subset_1(A_754, C_752, D_757)) | ~m1_subset_1(F_753, k1_zfmisc_1(k2_zfmisc_1(D_757, B_755))) | ~v1_funct_2(F_753, D_757, B_755) | ~v1_funct_1(F_753) | ~m1_subset_1(E_756, k1_zfmisc_1(k2_zfmisc_1(C_752, B_755))) | ~v1_funct_2(E_756, C_752, B_755) | ~v1_funct_1(E_756) | ~m1_subset_1(D_757, k1_zfmisc_1(A_754)) | v1_xboole_0(D_757) | ~m1_subset_1(C_752, k1_zfmisc_1(A_754)) | v1_xboole_0(C_752) | v1_xboole_0(B_755) | v1_xboole_0(A_754))), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.81/2.66  tff(c_3342, plain, (![E_874, F_875, D_878, B_876, C_879, A_877]: (k2_partfun1(k4_subset_1(A_877, C_879, D_878), B_876, k1_tmap_1(A_877, B_876, C_879, D_878, E_874, F_875), C_879)=E_874 | ~v1_funct_2(k1_tmap_1(A_877, B_876, C_879, D_878, E_874, F_875), k4_subset_1(A_877, C_879, D_878), B_876) | ~v1_funct_1(k1_tmap_1(A_877, B_876, C_879, D_878, E_874, F_875)) | k2_partfun1(D_878, B_876, F_875, k9_subset_1(A_877, C_879, D_878))!=k2_partfun1(C_879, B_876, E_874, k9_subset_1(A_877, C_879, D_878)) | ~m1_subset_1(F_875, k1_zfmisc_1(k2_zfmisc_1(D_878, B_876))) | ~v1_funct_2(F_875, D_878, B_876) | ~v1_funct_1(F_875) | ~m1_subset_1(E_874, k1_zfmisc_1(k2_zfmisc_1(C_879, B_876))) | ~v1_funct_2(E_874, C_879, B_876) | ~v1_funct_1(E_874) | ~m1_subset_1(D_878, k1_zfmisc_1(A_877)) | v1_xboole_0(D_878) | ~m1_subset_1(C_879, k1_zfmisc_1(A_877)) | v1_xboole_0(C_879) | v1_xboole_0(B_876) | v1_xboole_0(A_877))), inference(resolution, [status(thm)], [c_32, c_2899])).
% 7.81/2.66  tff(c_3749, plain, (![B_953, C_956, F_952, A_954, D_955, E_951]: (k2_partfun1(k4_subset_1(A_954, C_956, D_955), B_953, k1_tmap_1(A_954, B_953, C_956, D_955, E_951, F_952), C_956)=E_951 | ~v1_funct_1(k1_tmap_1(A_954, B_953, C_956, D_955, E_951, F_952)) | k2_partfun1(D_955, B_953, F_952, k9_subset_1(A_954, C_956, D_955))!=k2_partfun1(C_956, B_953, E_951, k9_subset_1(A_954, C_956, D_955)) | ~m1_subset_1(F_952, k1_zfmisc_1(k2_zfmisc_1(D_955, B_953))) | ~v1_funct_2(F_952, D_955, B_953) | ~v1_funct_1(F_952) | ~m1_subset_1(E_951, k1_zfmisc_1(k2_zfmisc_1(C_956, B_953))) | ~v1_funct_2(E_951, C_956, B_953) | ~v1_funct_1(E_951) | ~m1_subset_1(D_955, k1_zfmisc_1(A_954)) | v1_xboole_0(D_955) | ~m1_subset_1(C_956, k1_zfmisc_1(A_954)) | v1_xboole_0(C_956) | v1_xboole_0(B_953) | v1_xboole_0(A_954))), inference(resolution, [status(thm)], [c_34, c_3342])).
% 7.81/2.66  tff(c_3753, plain, (![A_954, C_956, E_951]: (k2_partfun1(k4_subset_1(A_954, C_956, '#skF_4'), '#skF_2', k1_tmap_1(A_954, '#skF_2', C_956, '#skF_4', E_951, '#skF_6'), C_956)=E_951 | ~v1_funct_1(k1_tmap_1(A_954, '#skF_2', C_956, '#skF_4', E_951, '#skF_6')) | k2_partfun1(C_956, '#skF_2', E_951, k9_subset_1(A_954, C_956, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_954, C_956, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_951, k1_zfmisc_1(k2_zfmisc_1(C_956, '#skF_2'))) | ~v1_funct_2(E_951, C_956, '#skF_2') | ~v1_funct_1(E_951) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_954)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_956, k1_zfmisc_1(A_954)) | v1_xboole_0(C_956) | v1_xboole_0('#skF_2') | v1_xboole_0(A_954))), inference(resolution, [status(thm)], [c_40, c_3749])).
% 7.81/2.66  tff(c_3759, plain, (![A_954, C_956, E_951]: (k2_partfun1(k4_subset_1(A_954, C_956, '#skF_4'), '#skF_2', k1_tmap_1(A_954, '#skF_2', C_956, '#skF_4', E_951, '#skF_6'), C_956)=E_951 | ~v1_funct_1(k1_tmap_1(A_954, '#skF_2', C_956, '#skF_4', E_951, '#skF_6')) | k2_partfun1(C_956, '#skF_2', E_951, k9_subset_1(A_954, C_956, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_954, C_956, '#skF_4')) | ~m1_subset_1(E_951, k1_zfmisc_1(k2_zfmisc_1(C_956, '#skF_2'))) | ~v1_funct_2(E_951, C_956, '#skF_2') | ~v1_funct_1(E_951) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_954)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_956, k1_zfmisc_1(A_954)) | v1_xboole_0(C_956) | v1_xboole_0('#skF_2') | v1_xboole_0(A_954))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_664, c_3753])).
% 7.81/2.66  tff(c_4134, plain, (![A_1034, C_1035, E_1036]: (k2_partfun1(k4_subset_1(A_1034, C_1035, '#skF_4'), '#skF_2', k1_tmap_1(A_1034, '#skF_2', C_1035, '#skF_4', E_1036, '#skF_6'), C_1035)=E_1036 | ~v1_funct_1(k1_tmap_1(A_1034, '#skF_2', C_1035, '#skF_4', E_1036, '#skF_6')) | k2_partfun1(C_1035, '#skF_2', E_1036, k9_subset_1(A_1034, C_1035, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1034, C_1035, '#skF_4')) | ~m1_subset_1(E_1036, k1_zfmisc_1(k2_zfmisc_1(C_1035, '#skF_2'))) | ~v1_funct_2(E_1036, C_1035, '#skF_2') | ~v1_funct_1(E_1036) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1034)) | ~m1_subset_1(C_1035, k1_zfmisc_1(A_1034)) | v1_xboole_0(C_1035) | v1_xboole_0(A_1034))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_3759])).
% 7.81/2.66  tff(c_4141, plain, (![A_1034]: (k2_partfun1(k4_subset_1(A_1034, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1034, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1034, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_1034, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1034, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1034)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1034)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1034))), inference(resolution, [status(thm)], [c_46, c_4134])).
% 7.81/2.66  tff(c_4151, plain, (![A_1034]: (k2_partfun1(k4_subset_1(A_1034, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1034, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1034, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1034, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1034, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1034)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1034)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1034))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_667, c_4141])).
% 7.81/2.66  tff(c_4153, plain, (![A_1037]: (k2_partfun1(k4_subset_1(A_1037, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1037, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1037, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1037, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1037, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1037)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1037)) | v1_xboole_0(A_1037))), inference(negUnitSimplification, [status(thm)], [c_60, c_4151])).
% 7.81/2.66  tff(c_799, plain, (![A_327, B_328]: (k3_xboole_0(A_327, B_328)=k1_xboole_0 | ~r1_subset_1(A_327, B_328) | v1_xboole_0(B_328) | v1_xboole_0(A_327))), inference(resolution, [status(thm)], [c_542, c_2])).
% 7.81/2.66  tff(c_805, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_799])).
% 7.81/2.66  tff(c_809, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_60, c_56, c_805])).
% 7.81/2.66  tff(c_832, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k7_relat_1('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_809, c_809, c_667, c_664, c_578])).
% 7.81/2.66  tff(c_836, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0 | k3_xboole_0('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_832, c_643])).
% 7.81/2.66  tff(c_846, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6, c_836])).
% 7.81/2.66  tff(c_852, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_846, c_832])).
% 7.81/2.66  tff(c_907, plain, (![A_337, E_334, C_339, D_338, B_336, F_335]: (v1_funct_1(k1_tmap_1(A_337, B_336, C_339, D_338, E_334, F_335)) | ~m1_subset_1(F_335, k1_zfmisc_1(k2_zfmisc_1(D_338, B_336))) | ~v1_funct_2(F_335, D_338, B_336) | ~v1_funct_1(F_335) | ~m1_subset_1(E_334, k1_zfmisc_1(k2_zfmisc_1(C_339, B_336))) | ~v1_funct_2(E_334, C_339, B_336) | ~v1_funct_1(E_334) | ~m1_subset_1(D_338, k1_zfmisc_1(A_337)) | v1_xboole_0(D_338) | ~m1_subset_1(C_339, k1_zfmisc_1(A_337)) | v1_xboole_0(C_339) | v1_xboole_0(B_336) | v1_xboole_0(A_337))), inference(cnfTransformation, [status(thm)], [f_155])).
% 7.81/2.66  tff(c_909, plain, (![A_337, C_339, E_334]: (v1_funct_1(k1_tmap_1(A_337, '#skF_2', C_339, '#skF_4', E_334, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_334, k1_zfmisc_1(k2_zfmisc_1(C_339, '#skF_2'))) | ~v1_funct_2(E_334, C_339, '#skF_2') | ~v1_funct_1(E_334) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_337)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_339, k1_zfmisc_1(A_337)) | v1_xboole_0(C_339) | v1_xboole_0('#skF_2') | v1_xboole_0(A_337))), inference(resolution, [status(thm)], [c_40, c_907])).
% 7.81/2.66  tff(c_914, plain, (![A_337, C_339, E_334]: (v1_funct_1(k1_tmap_1(A_337, '#skF_2', C_339, '#skF_4', E_334, '#skF_6')) | ~m1_subset_1(E_334, k1_zfmisc_1(k2_zfmisc_1(C_339, '#skF_2'))) | ~v1_funct_2(E_334, C_339, '#skF_2') | ~v1_funct_1(E_334) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_337)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_339, k1_zfmisc_1(A_337)) | v1_xboole_0(C_339) | v1_xboole_0('#skF_2') | v1_xboole_0(A_337))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_909])).
% 7.81/2.66  tff(c_942, plain, (![A_341, C_342, E_343]: (v1_funct_1(k1_tmap_1(A_341, '#skF_2', C_342, '#skF_4', E_343, '#skF_6')) | ~m1_subset_1(E_343, k1_zfmisc_1(k2_zfmisc_1(C_342, '#skF_2'))) | ~v1_funct_2(E_343, C_342, '#skF_2') | ~v1_funct_1(E_343) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_341)) | ~m1_subset_1(C_342, k1_zfmisc_1(A_341)) | v1_xboole_0(C_342) | v1_xboole_0(A_341))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_914])).
% 7.81/2.66  tff(c_946, plain, (![A_341]: (v1_funct_1(k1_tmap_1(A_341, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_341)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_341)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_341))), inference(resolution, [status(thm)], [c_46, c_942])).
% 7.81/2.66  tff(c_953, plain, (![A_341]: (v1_funct_1(k1_tmap_1(A_341, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_341)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_341)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_341))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_946])).
% 7.81/2.66  tff(c_977, plain, (![A_355]: (v1_funct_1(k1_tmap_1(A_355, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_355)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_355)) | v1_xboole_0(A_355))), inference(negUnitSimplification, [status(thm)], [c_60, c_953])).
% 7.81/2.66  tff(c_980, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_58, c_977])).
% 7.81/2.66  tff(c_983, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_980])).
% 7.81/2.66  tff(c_984, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_64, c_983])).
% 7.81/2.66  tff(c_1133, plain, (![B_386, A_385, D_388, C_383, F_384, E_387]: (k2_partfun1(k4_subset_1(A_385, C_383, D_388), B_386, k1_tmap_1(A_385, B_386, C_383, D_388, E_387, F_384), D_388)=F_384 | ~m1_subset_1(k1_tmap_1(A_385, B_386, C_383, D_388, E_387, F_384), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_385, C_383, D_388), B_386))) | ~v1_funct_2(k1_tmap_1(A_385, B_386, C_383, D_388, E_387, F_384), k4_subset_1(A_385, C_383, D_388), B_386) | ~v1_funct_1(k1_tmap_1(A_385, B_386, C_383, D_388, E_387, F_384)) | k2_partfun1(D_388, B_386, F_384, k9_subset_1(A_385, C_383, D_388))!=k2_partfun1(C_383, B_386, E_387, k9_subset_1(A_385, C_383, D_388)) | ~m1_subset_1(F_384, k1_zfmisc_1(k2_zfmisc_1(D_388, B_386))) | ~v1_funct_2(F_384, D_388, B_386) | ~v1_funct_1(F_384) | ~m1_subset_1(E_387, k1_zfmisc_1(k2_zfmisc_1(C_383, B_386))) | ~v1_funct_2(E_387, C_383, B_386) | ~v1_funct_1(E_387) | ~m1_subset_1(D_388, k1_zfmisc_1(A_385)) | v1_xboole_0(D_388) | ~m1_subset_1(C_383, k1_zfmisc_1(A_385)) | v1_xboole_0(C_383) | v1_xboole_0(B_386) | v1_xboole_0(A_385))), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.81/2.66  tff(c_1588, plain, (![E_488, C_493, A_491, F_489, D_492, B_490]: (k2_partfun1(k4_subset_1(A_491, C_493, D_492), B_490, k1_tmap_1(A_491, B_490, C_493, D_492, E_488, F_489), D_492)=F_489 | ~v1_funct_2(k1_tmap_1(A_491, B_490, C_493, D_492, E_488, F_489), k4_subset_1(A_491, C_493, D_492), B_490) | ~v1_funct_1(k1_tmap_1(A_491, B_490, C_493, D_492, E_488, F_489)) | k2_partfun1(D_492, B_490, F_489, k9_subset_1(A_491, C_493, D_492))!=k2_partfun1(C_493, B_490, E_488, k9_subset_1(A_491, C_493, D_492)) | ~m1_subset_1(F_489, k1_zfmisc_1(k2_zfmisc_1(D_492, B_490))) | ~v1_funct_2(F_489, D_492, B_490) | ~v1_funct_1(F_489) | ~m1_subset_1(E_488, k1_zfmisc_1(k2_zfmisc_1(C_493, B_490))) | ~v1_funct_2(E_488, C_493, B_490) | ~v1_funct_1(E_488) | ~m1_subset_1(D_492, k1_zfmisc_1(A_491)) | v1_xboole_0(D_492) | ~m1_subset_1(C_493, k1_zfmisc_1(A_491)) | v1_xboole_0(C_493) | v1_xboole_0(B_490) | v1_xboole_0(A_491))), inference(resolution, [status(thm)], [c_32, c_1133])).
% 7.81/2.66  tff(c_2019, plain, (![B_587, D_589, A_588, F_586, E_585, C_590]: (k2_partfun1(k4_subset_1(A_588, C_590, D_589), B_587, k1_tmap_1(A_588, B_587, C_590, D_589, E_585, F_586), D_589)=F_586 | ~v1_funct_1(k1_tmap_1(A_588, B_587, C_590, D_589, E_585, F_586)) | k2_partfun1(D_589, B_587, F_586, k9_subset_1(A_588, C_590, D_589))!=k2_partfun1(C_590, B_587, E_585, k9_subset_1(A_588, C_590, D_589)) | ~m1_subset_1(F_586, k1_zfmisc_1(k2_zfmisc_1(D_589, B_587))) | ~v1_funct_2(F_586, D_589, B_587) | ~v1_funct_1(F_586) | ~m1_subset_1(E_585, k1_zfmisc_1(k2_zfmisc_1(C_590, B_587))) | ~v1_funct_2(E_585, C_590, B_587) | ~v1_funct_1(E_585) | ~m1_subset_1(D_589, k1_zfmisc_1(A_588)) | v1_xboole_0(D_589) | ~m1_subset_1(C_590, k1_zfmisc_1(A_588)) | v1_xboole_0(C_590) | v1_xboole_0(B_587) | v1_xboole_0(A_588))), inference(resolution, [status(thm)], [c_34, c_1588])).
% 7.81/2.66  tff(c_2023, plain, (![A_588, C_590, E_585]: (k2_partfun1(k4_subset_1(A_588, C_590, '#skF_4'), '#skF_2', k1_tmap_1(A_588, '#skF_2', C_590, '#skF_4', E_585, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_588, '#skF_2', C_590, '#skF_4', E_585, '#skF_6')) | k2_partfun1(C_590, '#skF_2', E_585, k9_subset_1(A_588, C_590, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_588, C_590, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_585, k1_zfmisc_1(k2_zfmisc_1(C_590, '#skF_2'))) | ~v1_funct_2(E_585, C_590, '#skF_2') | ~v1_funct_1(E_585) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_588)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_590, k1_zfmisc_1(A_588)) | v1_xboole_0(C_590) | v1_xboole_0('#skF_2') | v1_xboole_0(A_588))), inference(resolution, [status(thm)], [c_40, c_2019])).
% 7.81/2.66  tff(c_2029, plain, (![A_588, C_590, E_585]: (k2_partfun1(k4_subset_1(A_588, C_590, '#skF_4'), '#skF_2', k1_tmap_1(A_588, '#skF_2', C_590, '#skF_4', E_585, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_588, '#skF_2', C_590, '#skF_4', E_585, '#skF_6')) | k2_partfun1(C_590, '#skF_2', E_585, k9_subset_1(A_588, C_590, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_588, C_590, '#skF_4')) | ~m1_subset_1(E_585, k1_zfmisc_1(k2_zfmisc_1(C_590, '#skF_2'))) | ~v1_funct_2(E_585, C_590, '#skF_2') | ~v1_funct_1(E_585) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_588)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_590, k1_zfmisc_1(A_588)) | v1_xboole_0(C_590) | v1_xboole_0('#skF_2') | v1_xboole_0(A_588))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_664, c_2023])).
% 7.81/2.66  tff(c_2364, plain, (![A_673, C_674, E_675]: (k2_partfun1(k4_subset_1(A_673, C_674, '#skF_4'), '#skF_2', k1_tmap_1(A_673, '#skF_2', C_674, '#skF_4', E_675, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_673, '#skF_2', C_674, '#skF_4', E_675, '#skF_6')) | k2_partfun1(C_674, '#skF_2', E_675, k9_subset_1(A_673, C_674, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_673, C_674, '#skF_4')) | ~m1_subset_1(E_675, k1_zfmisc_1(k2_zfmisc_1(C_674, '#skF_2'))) | ~v1_funct_2(E_675, C_674, '#skF_2') | ~v1_funct_1(E_675) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_673)) | ~m1_subset_1(C_674, k1_zfmisc_1(A_673)) | v1_xboole_0(C_674) | v1_xboole_0(A_673))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_2029])).
% 7.81/2.66  tff(c_2371, plain, (![A_673]: (k2_partfun1(k4_subset_1(A_673, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_673, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_673, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_673, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_673, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_673)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_673)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_673))), inference(resolution, [status(thm)], [c_46, c_2364])).
% 7.81/2.66  tff(c_2381, plain, (![A_673]: (k2_partfun1(k4_subset_1(A_673, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_673, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_673, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_673, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_673, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_673)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_673)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_673))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_667, c_2371])).
% 7.81/2.66  tff(c_2446, plain, (![A_690]: (k2_partfun1(k4_subset_1(A_690, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_690, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_690, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_690, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_690, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_690)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_690)) | v1_xboole_0(A_690))), inference(negUnitSimplification, [status(thm)], [c_60, c_2381])).
% 7.81/2.66  tff(c_497, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_38])).
% 7.81/2.66  tff(c_744, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_497])).
% 7.81/2.66  tff(c_2457, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2446, c_744])).
% 7.81/2.66  tff(c_2471, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_852, c_846, c_809, c_809, c_568, c_568, c_984, c_2457])).
% 7.81/2.66  tff(c_2473, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_2471])).
% 7.81/2.66  tff(c_2474, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_497])).
% 7.81/2.66  tff(c_4162, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4153, c_2474])).
% 7.81/2.66  tff(c_4173, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_2621, c_2615, c_2517, c_2517, c_568, c_568, c_2748, c_4162])).
% 7.81/2.66  tff(c_4175, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_4173])).
% 7.81/2.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.81/2.66  
% 7.81/2.66  Inference rules
% 7.81/2.66  ----------------------
% 7.81/2.66  #Ref     : 0
% 7.81/2.66  #Sup     : 866
% 7.81/2.66  #Fact    : 0
% 7.81/2.66  #Define  : 0
% 7.81/2.66  #Split   : 37
% 7.81/2.66  #Chain   : 0
% 7.81/2.66  #Close   : 0
% 7.81/2.66  
% 7.81/2.66  Ordering : KBO
% 7.81/2.66  
% 7.81/2.66  Simplification rules
% 7.81/2.66  ----------------------
% 7.81/2.66  #Subsume      : 186
% 7.81/2.66  #Demod        : 522
% 7.81/2.66  #Tautology    : 256
% 7.81/2.66  #SimpNegUnit  : 237
% 7.81/2.66  #BackRed      : 4
% 7.81/2.66  
% 7.81/2.66  #Partial instantiations: 0
% 7.81/2.66  #Strategies tried      : 1
% 7.81/2.66  
% 7.81/2.66  Timing (in seconds)
% 7.81/2.66  ----------------------
% 7.81/2.66  Preprocessing        : 0.40
% 7.81/2.66  Parsing              : 0.18
% 7.81/2.66  CNF conversion       : 0.07
% 7.81/2.66  Main loop            : 1.43
% 7.81/2.66  Inferencing          : 0.52
% 7.81/2.66  Reduction            : 0.45
% 7.81/2.67  Demodulation         : 0.31
% 7.81/2.67  BG Simplification    : 0.05
% 7.81/2.67  Subsumption          : 0.33
% 7.81/2.67  Abstraction          : 0.06
% 7.81/2.67  MUC search           : 0.00
% 7.81/2.67  Cooper               : 0.00
% 7.81/2.67  Total                : 1.89
% 7.81/2.67  Index Insertion      : 0.00
% 7.81/2.67  Index Deletion       : 0.00
% 7.81/2.67  Index Matching       : 0.00
% 7.81/2.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
