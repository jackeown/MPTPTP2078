%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:14 EST 2020

% Result     : Theorem 8.57s
% Output     : CNFRefutation 8.81s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 499 expanded)
%              Number of leaves         :   42 ( 196 expanded)
%              Depth                    :   12
%              Number of atoms          :  571 (2738 expanded)
%              Number of equality atoms :   94 ( 524 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_2

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff(f_107,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

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

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

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
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_66,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_62,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_58,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_54,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_3567,plain,(
    ! [A_668,B_669,C_670,D_671] :
      ( k2_partfun1(A_668,B_669,C_670,D_671) = k7_relat_1(C_670,D_671)
      | ~ m1_subset_1(C_670,k1_zfmisc_1(k2_zfmisc_1(A_668,B_669)))
      | ~ v1_funct_1(C_670) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_3569,plain,(
    ! [D_671] :
      ( k2_partfun1('#skF_6','#skF_5','#skF_8',D_671) = k7_relat_1('#skF_8',D_671)
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_54,c_3567])).

tff(c_3574,plain,(
    ! [D_671] : k2_partfun1('#skF_6','#skF_5','#skF_8',D_671) = k7_relat_1('#skF_8',D_671) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_3569])).

tff(c_3351,plain,(
    ! [A_639,B_640,C_641] :
      ( k9_subset_1(A_639,B_640,C_641) = k3_xboole_0(B_640,C_641)
      | ~ m1_subset_1(C_641,k1_zfmisc_1(A_639)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3363,plain,(
    ! [B_640] : k9_subset_1('#skF_4',B_640,'#skF_7') = k3_xboole_0(B_640,'#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_3351])).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_60,plain,(
    r1_subset_1('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_28,plain,(
    ! [A_28,B_29] :
      ( r1_xboole_0(A_28,B_29)
      | ~ r1_subset_1(A_28,B_29)
      | v1_xboole_0(B_29)
      | v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_129,plain,(
    ! [A_245,B_246,C_247] :
      ( ~ r1_xboole_0(A_245,B_246)
      | ~ r2_hidden(C_247,k3_xboole_0(A_245,B_246)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_144,plain,(
    ! [A_245,B_246] :
      ( ~ r1_xboole_0(A_245,B_246)
      | v1_xboole_0(k3_xboole_0(A_245,B_246)) ) ),
    inference(resolution,[status(thm)],[c_4,c_129])).

tff(c_48,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_120,plain,(
    ! [C_242,A_243,B_244] :
      ( v1_relat_1(C_242)
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1(A_243,B_244))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_128,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_48,c_120])).

tff(c_80,plain,(
    ! [A_232,B_233] :
      ( r2_hidden('#skF_2'(A_232,B_233),A_232)
      | r1_xboole_0(A_232,B_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_84,plain,(
    ! [A_232,B_233] :
      ( ~ v1_xboole_0(A_232)
      | r1_xboole_0(A_232,B_233) ) ),
    inference(resolution,[status(thm)],[c_80,c_2])).

tff(c_224,plain,(
    ! [A_269,B_270] :
      ( k7_relat_1(A_269,B_270) = k1_xboole_0
      | ~ r1_xboole_0(B_270,k1_relat_1(A_269))
      | ~ v1_relat_1(A_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_245,plain,(
    ! [A_271,A_272] :
      ( k7_relat_1(A_271,A_272) = k1_xboole_0
      | ~ v1_relat_1(A_271)
      | ~ v1_xboole_0(A_272) ) ),
    inference(resolution,[status(thm)],[c_84,c_224])).

tff(c_252,plain,(
    ! [A_273] :
      ( k7_relat_1('#skF_9',A_273) = k1_xboole_0
      | ~ v1_xboole_0(A_273) ) ),
    inference(resolution,[status(thm)],[c_128,c_245])).

tff(c_256,plain,(
    ! [A_245,B_246] :
      ( k7_relat_1('#skF_9',k3_xboole_0(A_245,B_246)) = k1_xboole_0
      | ~ r1_xboole_0(A_245,B_246) ) ),
    inference(resolution,[status(thm)],[c_144,c_252])).

tff(c_52,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_359,plain,(
    ! [A_292,B_293,C_294,D_295] :
      ( k2_partfun1(A_292,B_293,C_294,D_295) = k7_relat_1(C_294,D_295)
      | ~ m1_subset_1(C_294,k1_zfmisc_1(k2_zfmisc_1(A_292,B_293)))
      | ~ v1_funct_1(C_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_363,plain,(
    ! [D_295] :
      ( k2_partfun1('#skF_7','#skF_5','#skF_9',D_295) = k7_relat_1('#skF_9',D_295)
      | ~ v1_funct_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_48,c_359])).

tff(c_369,plain,(
    ! [D_295] : k2_partfun1('#skF_7','#skF_5','#skF_9',D_295) = k7_relat_1('#skF_9',D_295) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_363])).

tff(c_361,plain,(
    ! [D_295] :
      ( k2_partfun1('#skF_6','#skF_5','#skF_8',D_295) = k7_relat_1('#skF_8',D_295)
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_54,c_359])).

tff(c_366,plain,(
    ! [D_295] : k2_partfun1('#skF_6','#skF_5','#skF_8',D_295) = k7_relat_1('#skF_8',D_295) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_361])).

tff(c_262,plain,(
    ! [A_275,B_276,C_277] :
      ( k9_subset_1(A_275,B_276,C_277) = k3_xboole_0(B_276,C_277)
      | ~ m1_subset_1(C_277,k1_zfmisc_1(A_275)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_274,plain,(
    ! [B_276] : k9_subset_1('#skF_4',B_276,'#skF_7') = k3_xboole_0(B_276,'#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_262])).

tff(c_46,plain,
    ( k2_partfun1(k4_subset_1('#skF_4','#skF_6','#skF_7'),'#skF_5',k1_tmap_1('#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_7') != '#skF_9'
    | k2_partfun1(k4_subset_1('#skF_4','#skF_6','#skF_7'),'#skF_5',k1_tmap_1('#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_6') != '#skF_8'
    | k2_partfun1('#skF_7','#skF_5','#skF_9',k9_subset_1('#skF_4','#skF_6','#skF_7')) != k2_partfun1('#skF_6','#skF_5','#skF_8',k9_subset_1('#skF_4','#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_93,plain,(
    k2_partfun1('#skF_7','#skF_5','#skF_9',k9_subset_1('#skF_4','#skF_6','#skF_7')) != k2_partfun1('#skF_6','#skF_5','#skF_8',k9_subset_1('#skF_4','#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_284,plain,(
    k2_partfun1('#skF_7','#skF_5','#skF_9',k3_xboole_0('#skF_6','#skF_7')) != k2_partfun1('#skF_6','#skF_5','#skF_8',k3_xboole_0('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_274,c_93])).

tff(c_389,plain,(
    k7_relat_1('#skF_9',k3_xboole_0('#skF_6','#skF_7')) != k7_relat_1('#skF_8',k3_xboole_0('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_366,c_284])).

tff(c_392,plain,
    ( k7_relat_1('#skF_8',k3_xboole_0('#skF_6','#skF_7')) != k1_xboole_0
    | ~ r1_xboole_0('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_389])).

tff(c_393,plain,(
    ~ r1_xboole_0('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_392])).

tff(c_399,plain,
    ( ~ r1_subset_1('#skF_6','#skF_7')
    | v1_xboole_0('#skF_7')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_28,c_393])).

tff(c_411,plain,
    ( v1_xboole_0('#skF_7')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_399])).

tff(c_413,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_64,c_411])).

tff(c_415,plain,(
    r1_xboole_0('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_392])).

tff(c_127,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_54,c_120])).

tff(c_257,plain,(
    ! [A_274] :
      ( k7_relat_1('#skF_8',A_274) = k1_xboole_0
      | ~ v1_xboole_0(A_274) ) ),
    inference(resolution,[status(thm)],[c_127,c_245])).

tff(c_261,plain,(
    ! [A_245,B_246] :
      ( k7_relat_1('#skF_8',k3_xboole_0(A_245,B_246)) = k1_xboole_0
      | ~ r1_xboole_0(A_245,B_246) ) ),
    inference(resolution,[status(thm)],[c_144,c_257])).

tff(c_414,plain,(
    k7_relat_1('#skF_8',k3_xboole_0('#skF_6','#skF_7')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_392])).

tff(c_456,plain,(
    ~ r1_xboole_0('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_414])).

tff(c_460,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_415,c_456])).

tff(c_462,plain,(
    k2_partfun1('#skF_7','#skF_5','#skF_9',k9_subset_1('#skF_4','#skF_6','#skF_7')) = k2_partfun1('#skF_6','#skF_5','#skF_8',k9_subset_1('#skF_4','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_3373,plain,(
    k2_partfun1('#skF_7','#skF_5','#skF_9',k3_xboole_0('#skF_6','#skF_7')) = k2_partfun1('#skF_6','#skF_5','#skF_8',k3_xboole_0('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3363,c_3363,c_462])).

tff(c_3578,plain,(
    k2_partfun1('#skF_7','#skF_5','#skF_9',k3_xboole_0('#skF_6','#skF_7')) = k7_relat_1('#skF_8',k3_xboole_0('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3574,c_3373])).

tff(c_3571,plain,(
    ! [D_671] :
      ( k2_partfun1('#skF_7','#skF_5','#skF_9',D_671) = k7_relat_1('#skF_9',D_671)
      | ~ v1_funct_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_48,c_3567])).

tff(c_3577,plain,(
    ! [D_671] : k2_partfun1('#skF_7','#skF_5','#skF_9',D_671) = k7_relat_1('#skF_9',D_671) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3571])).

tff(c_3600,plain,(
    k7_relat_1('#skF_9',k3_xboole_0('#skF_6','#skF_7')) = k7_relat_1('#skF_8',k3_xboole_0('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3578,c_3577])).

tff(c_56,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_50,plain,(
    v1_funct_2('#skF_9','#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_3648,plain,(
    ! [E_687,B_686,D_684,F_688,A_685,C_689] :
      ( v1_funct_1(k1_tmap_1(A_685,B_686,C_689,D_684,E_687,F_688))
      | ~ m1_subset_1(F_688,k1_zfmisc_1(k2_zfmisc_1(D_684,B_686)))
      | ~ v1_funct_2(F_688,D_684,B_686)
      | ~ v1_funct_1(F_688)
      | ~ m1_subset_1(E_687,k1_zfmisc_1(k2_zfmisc_1(C_689,B_686)))
      | ~ v1_funct_2(E_687,C_689,B_686)
      | ~ v1_funct_1(E_687)
      | ~ m1_subset_1(D_684,k1_zfmisc_1(A_685))
      | v1_xboole_0(D_684)
      | ~ m1_subset_1(C_689,k1_zfmisc_1(A_685))
      | v1_xboole_0(C_689)
      | v1_xboole_0(B_686)
      | v1_xboole_0(A_685) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_3652,plain,(
    ! [A_685,C_689,E_687] :
      ( v1_funct_1(k1_tmap_1(A_685,'#skF_5',C_689,'#skF_7',E_687,'#skF_9'))
      | ~ v1_funct_2('#skF_9','#skF_7','#skF_5')
      | ~ v1_funct_1('#skF_9')
      | ~ m1_subset_1(E_687,k1_zfmisc_1(k2_zfmisc_1(C_689,'#skF_5')))
      | ~ v1_funct_2(E_687,C_689,'#skF_5')
      | ~ v1_funct_1(E_687)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_685))
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(C_689,k1_zfmisc_1(A_685))
      | v1_xboole_0(C_689)
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_685) ) ),
    inference(resolution,[status(thm)],[c_48,c_3648])).

tff(c_3659,plain,(
    ! [A_685,C_689,E_687] :
      ( v1_funct_1(k1_tmap_1(A_685,'#skF_5',C_689,'#skF_7',E_687,'#skF_9'))
      | ~ m1_subset_1(E_687,k1_zfmisc_1(k2_zfmisc_1(C_689,'#skF_5')))
      | ~ v1_funct_2(E_687,C_689,'#skF_5')
      | ~ v1_funct_1(E_687)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_685))
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(C_689,k1_zfmisc_1(A_685))
      | v1_xboole_0(C_689)
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_685) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_3652])).

tff(c_3730,plain,(
    ! [A_698,C_699,E_700] :
      ( v1_funct_1(k1_tmap_1(A_698,'#skF_5',C_699,'#skF_7',E_700,'#skF_9'))
      | ~ m1_subset_1(E_700,k1_zfmisc_1(k2_zfmisc_1(C_699,'#skF_5')))
      | ~ v1_funct_2(E_700,C_699,'#skF_5')
      | ~ v1_funct_1(E_700)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_698))
      | ~ m1_subset_1(C_699,k1_zfmisc_1(A_698))
      | v1_xboole_0(C_699)
      | v1_xboole_0(A_698) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_3659])).

tff(c_3732,plain,(
    ! [A_698] :
      ( v1_funct_1(k1_tmap_1(A_698,'#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_5')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_698))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_698))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(A_698) ) ),
    inference(resolution,[status(thm)],[c_54,c_3730])).

tff(c_3737,plain,(
    ! [A_698] :
      ( v1_funct_1(k1_tmap_1(A_698,'#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_698))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_698))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(A_698) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_3732])).

tff(c_3751,plain,(
    ! [A_702] :
      ( v1_funct_1(k1_tmap_1(A_702,'#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_702))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_702))
      | v1_xboole_0(A_702) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3737])).

tff(c_3754,plain,
    ( v1_funct_1(k1_tmap_1('#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_3751])).

tff(c_3757,plain,
    ( v1_funct_1(k1_tmap_1('#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'))
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3754])).

tff(c_3758,plain,(
    v1_funct_1(k1_tmap_1('#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3757])).

tff(c_42,plain,(
    ! [C_166,D_167,E_168,A_164,B_165,F_169] :
      ( v1_funct_2(k1_tmap_1(A_164,B_165,C_166,D_167,E_168,F_169),k4_subset_1(A_164,C_166,D_167),B_165)
      | ~ m1_subset_1(F_169,k1_zfmisc_1(k2_zfmisc_1(D_167,B_165)))
      | ~ v1_funct_2(F_169,D_167,B_165)
      | ~ v1_funct_1(F_169)
      | ~ m1_subset_1(E_168,k1_zfmisc_1(k2_zfmisc_1(C_166,B_165)))
      | ~ v1_funct_2(E_168,C_166,B_165)
      | ~ v1_funct_1(E_168)
      | ~ m1_subset_1(D_167,k1_zfmisc_1(A_164))
      | v1_xboole_0(D_167)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(A_164))
      | v1_xboole_0(C_166)
      | v1_xboole_0(B_165)
      | v1_xboole_0(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_40,plain,(
    ! [C_166,D_167,E_168,A_164,B_165,F_169] :
      ( m1_subset_1(k1_tmap_1(A_164,B_165,C_166,D_167,E_168,F_169),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_164,C_166,D_167),B_165)))
      | ~ m1_subset_1(F_169,k1_zfmisc_1(k2_zfmisc_1(D_167,B_165)))
      | ~ v1_funct_2(F_169,D_167,B_165)
      | ~ v1_funct_1(F_169)
      | ~ m1_subset_1(E_168,k1_zfmisc_1(k2_zfmisc_1(C_166,B_165)))
      | ~ v1_funct_2(E_168,C_166,B_165)
      | ~ v1_funct_1(E_168)
      | ~ m1_subset_1(D_167,k1_zfmisc_1(A_164))
      | v1_xboole_0(D_167)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(A_164))
      | v1_xboole_0(C_166)
      | v1_xboole_0(B_165)
      | v1_xboole_0(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_3989,plain,(
    ! [C_739,F_740,B_741,D_743,E_742,A_738] :
      ( k2_partfun1(k4_subset_1(A_738,C_739,D_743),B_741,k1_tmap_1(A_738,B_741,C_739,D_743,E_742,F_740),C_739) = E_742
      | ~ m1_subset_1(k1_tmap_1(A_738,B_741,C_739,D_743,E_742,F_740),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_738,C_739,D_743),B_741)))
      | ~ v1_funct_2(k1_tmap_1(A_738,B_741,C_739,D_743,E_742,F_740),k4_subset_1(A_738,C_739,D_743),B_741)
      | ~ v1_funct_1(k1_tmap_1(A_738,B_741,C_739,D_743,E_742,F_740))
      | k2_partfun1(D_743,B_741,F_740,k9_subset_1(A_738,C_739,D_743)) != k2_partfun1(C_739,B_741,E_742,k9_subset_1(A_738,C_739,D_743))
      | ~ m1_subset_1(F_740,k1_zfmisc_1(k2_zfmisc_1(D_743,B_741)))
      | ~ v1_funct_2(F_740,D_743,B_741)
      | ~ v1_funct_1(F_740)
      | ~ m1_subset_1(E_742,k1_zfmisc_1(k2_zfmisc_1(C_739,B_741)))
      | ~ v1_funct_2(E_742,C_739,B_741)
      | ~ v1_funct_1(E_742)
      | ~ m1_subset_1(D_743,k1_zfmisc_1(A_738))
      | v1_xboole_0(D_743)
      | ~ m1_subset_1(C_739,k1_zfmisc_1(A_738))
      | v1_xboole_0(C_739)
      | v1_xboole_0(B_741)
      | v1_xboole_0(A_738) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_5064,plain,(
    ! [D_835,C_840,F_839,E_838,A_836,B_837] :
      ( k2_partfun1(k4_subset_1(A_836,C_840,D_835),B_837,k1_tmap_1(A_836,B_837,C_840,D_835,E_838,F_839),C_840) = E_838
      | ~ v1_funct_2(k1_tmap_1(A_836,B_837,C_840,D_835,E_838,F_839),k4_subset_1(A_836,C_840,D_835),B_837)
      | ~ v1_funct_1(k1_tmap_1(A_836,B_837,C_840,D_835,E_838,F_839))
      | k2_partfun1(D_835,B_837,F_839,k9_subset_1(A_836,C_840,D_835)) != k2_partfun1(C_840,B_837,E_838,k9_subset_1(A_836,C_840,D_835))
      | ~ m1_subset_1(F_839,k1_zfmisc_1(k2_zfmisc_1(D_835,B_837)))
      | ~ v1_funct_2(F_839,D_835,B_837)
      | ~ v1_funct_1(F_839)
      | ~ m1_subset_1(E_838,k1_zfmisc_1(k2_zfmisc_1(C_840,B_837)))
      | ~ v1_funct_2(E_838,C_840,B_837)
      | ~ v1_funct_1(E_838)
      | ~ m1_subset_1(D_835,k1_zfmisc_1(A_836))
      | v1_xboole_0(D_835)
      | ~ m1_subset_1(C_840,k1_zfmisc_1(A_836))
      | v1_xboole_0(C_840)
      | v1_xboole_0(B_837)
      | v1_xboole_0(A_836) ) ),
    inference(resolution,[status(thm)],[c_40,c_3989])).

tff(c_5318,plain,(
    ! [B_862,A_861,F_864,E_863,C_865,D_860] :
      ( k2_partfun1(k4_subset_1(A_861,C_865,D_860),B_862,k1_tmap_1(A_861,B_862,C_865,D_860,E_863,F_864),C_865) = E_863
      | ~ v1_funct_1(k1_tmap_1(A_861,B_862,C_865,D_860,E_863,F_864))
      | k2_partfun1(D_860,B_862,F_864,k9_subset_1(A_861,C_865,D_860)) != k2_partfun1(C_865,B_862,E_863,k9_subset_1(A_861,C_865,D_860))
      | ~ m1_subset_1(F_864,k1_zfmisc_1(k2_zfmisc_1(D_860,B_862)))
      | ~ v1_funct_2(F_864,D_860,B_862)
      | ~ v1_funct_1(F_864)
      | ~ m1_subset_1(E_863,k1_zfmisc_1(k2_zfmisc_1(C_865,B_862)))
      | ~ v1_funct_2(E_863,C_865,B_862)
      | ~ v1_funct_1(E_863)
      | ~ m1_subset_1(D_860,k1_zfmisc_1(A_861))
      | v1_xboole_0(D_860)
      | ~ m1_subset_1(C_865,k1_zfmisc_1(A_861))
      | v1_xboole_0(C_865)
      | v1_xboole_0(B_862)
      | v1_xboole_0(A_861) ) ),
    inference(resolution,[status(thm)],[c_42,c_5064])).

tff(c_5324,plain,(
    ! [A_861,C_865,E_863] :
      ( k2_partfun1(k4_subset_1(A_861,C_865,'#skF_7'),'#skF_5',k1_tmap_1(A_861,'#skF_5',C_865,'#skF_7',E_863,'#skF_9'),C_865) = E_863
      | ~ v1_funct_1(k1_tmap_1(A_861,'#skF_5',C_865,'#skF_7',E_863,'#skF_9'))
      | k2_partfun1(C_865,'#skF_5',E_863,k9_subset_1(A_861,C_865,'#skF_7')) != k2_partfun1('#skF_7','#skF_5','#skF_9',k9_subset_1(A_861,C_865,'#skF_7'))
      | ~ v1_funct_2('#skF_9','#skF_7','#skF_5')
      | ~ v1_funct_1('#skF_9')
      | ~ m1_subset_1(E_863,k1_zfmisc_1(k2_zfmisc_1(C_865,'#skF_5')))
      | ~ v1_funct_2(E_863,C_865,'#skF_5')
      | ~ v1_funct_1(E_863)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_861))
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(C_865,k1_zfmisc_1(A_861))
      | v1_xboole_0(C_865)
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_861) ) ),
    inference(resolution,[status(thm)],[c_48,c_5318])).

tff(c_5332,plain,(
    ! [A_861,C_865,E_863] :
      ( k2_partfun1(k4_subset_1(A_861,C_865,'#skF_7'),'#skF_5',k1_tmap_1(A_861,'#skF_5',C_865,'#skF_7',E_863,'#skF_9'),C_865) = E_863
      | ~ v1_funct_1(k1_tmap_1(A_861,'#skF_5',C_865,'#skF_7',E_863,'#skF_9'))
      | k2_partfun1(C_865,'#skF_5',E_863,k9_subset_1(A_861,C_865,'#skF_7')) != k7_relat_1('#skF_9',k9_subset_1(A_861,C_865,'#skF_7'))
      | ~ m1_subset_1(E_863,k1_zfmisc_1(k2_zfmisc_1(C_865,'#skF_5')))
      | ~ v1_funct_2(E_863,C_865,'#skF_5')
      | ~ v1_funct_1(E_863)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_861))
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(C_865,k1_zfmisc_1(A_861))
      | v1_xboole_0(C_865)
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_861) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_3577,c_5324])).

tff(c_5481,plain,(
    ! [A_876,C_877,E_878] :
      ( k2_partfun1(k4_subset_1(A_876,C_877,'#skF_7'),'#skF_5',k1_tmap_1(A_876,'#skF_5',C_877,'#skF_7',E_878,'#skF_9'),C_877) = E_878
      | ~ v1_funct_1(k1_tmap_1(A_876,'#skF_5',C_877,'#skF_7',E_878,'#skF_9'))
      | k2_partfun1(C_877,'#skF_5',E_878,k9_subset_1(A_876,C_877,'#skF_7')) != k7_relat_1('#skF_9',k9_subset_1(A_876,C_877,'#skF_7'))
      | ~ m1_subset_1(E_878,k1_zfmisc_1(k2_zfmisc_1(C_877,'#skF_5')))
      | ~ v1_funct_2(E_878,C_877,'#skF_5')
      | ~ v1_funct_1(E_878)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_876))
      | ~ m1_subset_1(C_877,k1_zfmisc_1(A_876))
      | v1_xboole_0(C_877)
      | v1_xboole_0(A_876) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_5332])).

tff(c_5486,plain,(
    ! [A_876] :
      ( k2_partfun1(k4_subset_1(A_876,'#skF_6','#skF_7'),'#skF_5',k1_tmap_1(A_876,'#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_876,'#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'))
      | k2_partfun1('#skF_6','#skF_5','#skF_8',k9_subset_1(A_876,'#skF_6','#skF_7')) != k7_relat_1('#skF_9',k9_subset_1(A_876,'#skF_6','#skF_7'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_5')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_876))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_876))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(A_876) ) ),
    inference(resolution,[status(thm)],[c_54,c_5481])).

tff(c_5494,plain,(
    ! [A_876] :
      ( k2_partfun1(k4_subset_1(A_876,'#skF_6','#skF_7'),'#skF_5',k1_tmap_1(A_876,'#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_876,'#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'))
      | k7_relat_1('#skF_9',k9_subset_1(A_876,'#skF_6','#skF_7')) != k7_relat_1('#skF_8',k9_subset_1(A_876,'#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_876))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_876))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(A_876) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_3574,c_5486])).

tff(c_5723,plain,(
    ! [A_892] :
      ( k2_partfun1(k4_subset_1(A_892,'#skF_6','#skF_7'),'#skF_5',k1_tmap_1(A_892,'#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_892,'#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'))
      | k7_relat_1('#skF_9',k9_subset_1(A_892,'#skF_6','#skF_7')) != k7_relat_1('#skF_8',k9_subset_1(A_892,'#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_892))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_892))
      | v1_xboole_0(A_892) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_5494])).

tff(c_854,plain,(
    ! [A_376,B_377,C_378,D_379] :
      ( k2_partfun1(A_376,B_377,C_378,D_379) = k7_relat_1(C_378,D_379)
      | ~ m1_subset_1(C_378,k1_zfmisc_1(k2_zfmisc_1(A_376,B_377)))
      | ~ v1_funct_1(C_378) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_856,plain,(
    ! [D_379] :
      ( k2_partfun1('#skF_6','#skF_5','#skF_8',D_379) = k7_relat_1('#skF_8',D_379)
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_54,c_854])).

tff(c_861,plain,(
    ! [D_379] : k2_partfun1('#skF_6','#skF_5','#skF_8',D_379) = k7_relat_1('#skF_8',D_379) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_856])).

tff(c_650,plain,(
    ! [A_345,B_346,C_347] :
      ( k9_subset_1(A_345,B_346,C_347) = k3_xboole_0(B_346,C_347)
      | ~ m1_subset_1(C_347,k1_zfmisc_1(A_345)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_662,plain,(
    ! [B_346] : k9_subset_1('#skF_4',B_346,'#skF_7') = k3_xboole_0(B_346,'#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_650])).

tff(c_677,plain,(
    k2_partfun1('#skF_7','#skF_5','#skF_9',k3_xboole_0('#skF_6','#skF_7')) = k2_partfun1('#skF_6','#skF_5','#skF_8',k3_xboole_0('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_662,c_662,c_462])).

tff(c_865,plain,(
    k2_partfun1('#skF_7','#skF_5','#skF_9',k3_xboole_0('#skF_6','#skF_7')) = k7_relat_1('#skF_8',k3_xboole_0('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_861,c_677])).

tff(c_858,plain,(
    ! [D_379] :
      ( k2_partfun1('#skF_7','#skF_5','#skF_9',D_379) = k7_relat_1('#skF_9',D_379)
      | ~ v1_funct_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_48,c_854])).

tff(c_864,plain,(
    ! [D_379] : k2_partfun1('#skF_7','#skF_5','#skF_9',D_379) = k7_relat_1('#skF_9',D_379) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_858])).

tff(c_887,plain,(
    k7_relat_1('#skF_9',k3_xboole_0('#skF_6','#skF_7')) = k7_relat_1('#skF_8',k3_xboole_0('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_865,c_864])).

tff(c_950,plain,(
    ! [A_390,E_392,F_393,B_391,C_394,D_389] :
      ( v1_funct_1(k1_tmap_1(A_390,B_391,C_394,D_389,E_392,F_393))
      | ~ m1_subset_1(F_393,k1_zfmisc_1(k2_zfmisc_1(D_389,B_391)))
      | ~ v1_funct_2(F_393,D_389,B_391)
      | ~ v1_funct_1(F_393)
      | ~ m1_subset_1(E_392,k1_zfmisc_1(k2_zfmisc_1(C_394,B_391)))
      | ~ v1_funct_2(E_392,C_394,B_391)
      | ~ v1_funct_1(E_392)
      | ~ m1_subset_1(D_389,k1_zfmisc_1(A_390))
      | v1_xboole_0(D_389)
      | ~ m1_subset_1(C_394,k1_zfmisc_1(A_390))
      | v1_xboole_0(C_394)
      | v1_xboole_0(B_391)
      | v1_xboole_0(A_390) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_954,plain,(
    ! [A_390,C_394,E_392] :
      ( v1_funct_1(k1_tmap_1(A_390,'#skF_5',C_394,'#skF_7',E_392,'#skF_9'))
      | ~ v1_funct_2('#skF_9','#skF_7','#skF_5')
      | ~ v1_funct_1('#skF_9')
      | ~ m1_subset_1(E_392,k1_zfmisc_1(k2_zfmisc_1(C_394,'#skF_5')))
      | ~ v1_funct_2(E_392,C_394,'#skF_5')
      | ~ v1_funct_1(E_392)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_390))
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(C_394,k1_zfmisc_1(A_390))
      | v1_xboole_0(C_394)
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_390) ) ),
    inference(resolution,[status(thm)],[c_48,c_950])).

tff(c_961,plain,(
    ! [A_390,C_394,E_392] :
      ( v1_funct_1(k1_tmap_1(A_390,'#skF_5',C_394,'#skF_7',E_392,'#skF_9'))
      | ~ m1_subset_1(E_392,k1_zfmisc_1(k2_zfmisc_1(C_394,'#skF_5')))
      | ~ v1_funct_2(E_392,C_394,'#skF_5')
      | ~ v1_funct_1(E_392)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_390))
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(C_394,k1_zfmisc_1(A_390))
      | v1_xboole_0(C_394)
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_390) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_954])).

tff(c_1108,plain,(
    ! [A_421,C_422,E_423] :
      ( v1_funct_1(k1_tmap_1(A_421,'#skF_5',C_422,'#skF_7',E_423,'#skF_9'))
      | ~ m1_subset_1(E_423,k1_zfmisc_1(k2_zfmisc_1(C_422,'#skF_5')))
      | ~ v1_funct_2(E_423,C_422,'#skF_5')
      | ~ v1_funct_1(E_423)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_421))
      | ~ m1_subset_1(C_422,k1_zfmisc_1(A_421))
      | v1_xboole_0(C_422)
      | v1_xboole_0(A_421) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_961])).

tff(c_1110,plain,(
    ! [A_421] :
      ( v1_funct_1(k1_tmap_1(A_421,'#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_5')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_421))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_421))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(A_421) ) ),
    inference(resolution,[status(thm)],[c_54,c_1108])).

tff(c_1115,plain,(
    ! [A_421] :
      ( v1_funct_1(k1_tmap_1(A_421,'#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_421))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_421))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(A_421) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1110])).

tff(c_1128,plain,(
    ! [A_425] :
      ( v1_funct_1(k1_tmap_1(A_425,'#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_425))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_425))
      | v1_xboole_0(A_425) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1115])).

tff(c_1131,plain,
    ( v1_funct_1(k1_tmap_1('#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_1128])).

tff(c_1134,plain,
    ( v1_funct_1(k1_tmap_1('#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'))
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1131])).

tff(c_1135,plain,(
    v1_funct_1(k1_tmap_1('#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1134])).

tff(c_1299,plain,(
    ! [B_451,A_448,E_452,F_450,D_453,C_449] :
      ( k2_partfun1(k4_subset_1(A_448,C_449,D_453),B_451,k1_tmap_1(A_448,B_451,C_449,D_453,E_452,F_450),D_453) = F_450
      | ~ m1_subset_1(k1_tmap_1(A_448,B_451,C_449,D_453,E_452,F_450),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_448,C_449,D_453),B_451)))
      | ~ v1_funct_2(k1_tmap_1(A_448,B_451,C_449,D_453,E_452,F_450),k4_subset_1(A_448,C_449,D_453),B_451)
      | ~ v1_funct_1(k1_tmap_1(A_448,B_451,C_449,D_453,E_452,F_450))
      | k2_partfun1(D_453,B_451,F_450,k9_subset_1(A_448,C_449,D_453)) != k2_partfun1(C_449,B_451,E_452,k9_subset_1(A_448,C_449,D_453))
      | ~ m1_subset_1(F_450,k1_zfmisc_1(k2_zfmisc_1(D_453,B_451)))
      | ~ v1_funct_2(F_450,D_453,B_451)
      | ~ v1_funct_1(F_450)
      | ~ m1_subset_1(E_452,k1_zfmisc_1(k2_zfmisc_1(C_449,B_451)))
      | ~ v1_funct_2(E_452,C_449,B_451)
      | ~ v1_funct_1(E_452)
      | ~ m1_subset_1(D_453,k1_zfmisc_1(A_448))
      | v1_xboole_0(D_453)
      | ~ m1_subset_1(C_449,k1_zfmisc_1(A_448))
      | v1_xboole_0(C_449)
      | v1_xboole_0(B_451)
      | v1_xboole_0(A_448) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_2107,plain,(
    ! [E_536,D_533,F_537,A_534,B_535,C_538] :
      ( k2_partfun1(k4_subset_1(A_534,C_538,D_533),B_535,k1_tmap_1(A_534,B_535,C_538,D_533,E_536,F_537),D_533) = F_537
      | ~ v1_funct_2(k1_tmap_1(A_534,B_535,C_538,D_533,E_536,F_537),k4_subset_1(A_534,C_538,D_533),B_535)
      | ~ v1_funct_1(k1_tmap_1(A_534,B_535,C_538,D_533,E_536,F_537))
      | k2_partfun1(D_533,B_535,F_537,k9_subset_1(A_534,C_538,D_533)) != k2_partfun1(C_538,B_535,E_536,k9_subset_1(A_534,C_538,D_533))
      | ~ m1_subset_1(F_537,k1_zfmisc_1(k2_zfmisc_1(D_533,B_535)))
      | ~ v1_funct_2(F_537,D_533,B_535)
      | ~ v1_funct_1(F_537)
      | ~ m1_subset_1(E_536,k1_zfmisc_1(k2_zfmisc_1(C_538,B_535)))
      | ~ v1_funct_2(E_536,C_538,B_535)
      | ~ v1_funct_1(E_536)
      | ~ m1_subset_1(D_533,k1_zfmisc_1(A_534))
      | v1_xboole_0(D_533)
      | ~ m1_subset_1(C_538,k1_zfmisc_1(A_534))
      | v1_xboole_0(C_538)
      | v1_xboole_0(B_535)
      | v1_xboole_0(A_534) ) ),
    inference(resolution,[status(thm)],[c_40,c_1299])).

tff(c_2746,plain,(
    ! [E_583,A_581,F_584,C_585,D_580,B_582] :
      ( k2_partfun1(k4_subset_1(A_581,C_585,D_580),B_582,k1_tmap_1(A_581,B_582,C_585,D_580,E_583,F_584),D_580) = F_584
      | ~ v1_funct_1(k1_tmap_1(A_581,B_582,C_585,D_580,E_583,F_584))
      | k2_partfun1(D_580,B_582,F_584,k9_subset_1(A_581,C_585,D_580)) != k2_partfun1(C_585,B_582,E_583,k9_subset_1(A_581,C_585,D_580))
      | ~ m1_subset_1(F_584,k1_zfmisc_1(k2_zfmisc_1(D_580,B_582)))
      | ~ v1_funct_2(F_584,D_580,B_582)
      | ~ v1_funct_1(F_584)
      | ~ m1_subset_1(E_583,k1_zfmisc_1(k2_zfmisc_1(C_585,B_582)))
      | ~ v1_funct_2(E_583,C_585,B_582)
      | ~ v1_funct_1(E_583)
      | ~ m1_subset_1(D_580,k1_zfmisc_1(A_581))
      | v1_xboole_0(D_580)
      | ~ m1_subset_1(C_585,k1_zfmisc_1(A_581))
      | v1_xboole_0(C_585)
      | v1_xboole_0(B_582)
      | v1_xboole_0(A_581) ) ),
    inference(resolution,[status(thm)],[c_42,c_2107])).

tff(c_2752,plain,(
    ! [A_581,C_585,E_583] :
      ( k2_partfun1(k4_subset_1(A_581,C_585,'#skF_7'),'#skF_5',k1_tmap_1(A_581,'#skF_5',C_585,'#skF_7',E_583,'#skF_9'),'#skF_7') = '#skF_9'
      | ~ v1_funct_1(k1_tmap_1(A_581,'#skF_5',C_585,'#skF_7',E_583,'#skF_9'))
      | k2_partfun1(C_585,'#skF_5',E_583,k9_subset_1(A_581,C_585,'#skF_7')) != k2_partfun1('#skF_7','#skF_5','#skF_9',k9_subset_1(A_581,C_585,'#skF_7'))
      | ~ v1_funct_2('#skF_9','#skF_7','#skF_5')
      | ~ v1_funct_1('#skF_9')
      | ~ m1_subset_1(E_583,k1_zfmisc_1(k2_zfmisc_1(C_585,'#skF_5')))
      | ~ v1_funct_2(E_583,C_585,'#skF_5')
      | ~ v1_funct_1(E_583)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_581))
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(C_585,k1_zfmisc_1(A_581))
      | v1_xboole_0(C_585)
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_581) ) ),
    inference(resolution,[status(thm)],[c_48,c_2746])).

tff(c_2760,plain,(
    ! [A_581,C_585,E_583] :
      ( k2_partfun1(k4_subset_1(A_581,C_585,'#skF_7'),'#skF_5',k1_tmap_1(A_581,'#skF_5',C_585,'#skF_7',E_583,'#skF_9'),'#skF_7') = '#skF_9'
      | ~ v1_funct_1(k1_tmap_1(A_581,'#skF_5',C_585,'#skF_7',E_583,'#skF_9'))
      | k2_partfun1(C_585,'#skF_5',E_583,k9_subset_1(A_581,C_585,'#skF_7')) != k7_relat_1('#skF_9',k9_subset_1(A_581,C_585,'#skF_7'))
      | ~ m1_subset_1(E_583,k1_zfmisc_1(k2_zfmisc_1(C_585,'#skF_5')))
      | ~ v1_funct_2(E_583,C_585,'#skF_5')
      | ~ v1_funct_1(E_583)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_581))
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(C_585,k1_zfmisc_1(A_581))
      | v1_xboole_0(C_585)
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_581) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_864,c_2752])).

tff(c_3241,plain,(
    ! [A_621,C_622,E_623] :
      ( k2_partfun1(k4_subset_1(A_621,C_622,'#skF_7'),'#skF_5',k1_tmap_1(A_621,'#skF_5',C_622,'#skF_7',E_623,'#skF_9'),'#skF_7') = '#skF_9'
      | ~ v1_funct_1(k1_tmap_1(A_621,'#skF_5',C_622,'#skF_7',E_623,'#skF_9'))
      | k2_partfun1(C_622,'#skF_5',E_623,k9_subset_1(A_621,C_622,'#skF_7')) != k7_relat_1('#skF_9',k9_subset_1(A_621,C_622,'#skF_7'))
      | ~ m1_subset_1(E_623,k1_zfmisc_1(k2_zfmisc_1(C_622,'#skF_5')))
      | ~ v1_funct_2(E_623,C_622,'#skF_5')
      | ~ v1_funct_1(E_623)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_621))
      | ~ m1_subset_1(C_622,k1_zfmisc_1(A_621))
      | v1_xboole_0(C_622)
      | v1_xboole_0(A_621) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_2760])).

tff(c_3246,plain,(
    ! [A_621] :
      ( k2_partfun1(k4_subset_1(A_621,'#skF_6','#skF_7'),'#skF_5',k1_tmap_1(A_621,'#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_7') = '#skF_9'
      | ~ v1_funct_1(k1_tmap_1(A_621,'#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'))
      | k2_partfun1('#skF_6','#skF_5','#skF_8',k9_subset_1(A_621,'#skF_6','#skF_7')) != k7_relat_1('#skF_9',k9_subset_1(A_621,'#skF_6','#skF_7'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_5')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_621))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_621))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(A_621) ) ),
    inference(resolution,[status(thm)],[c_54,c_3241])).

tff(c_3254,plain,(
    ! [A_621] :
      ( k2_partfun1(k4_subset_1(A_621,'#skF_6','#skF_7'),'#skF_5',k1_tmap_1(A_621,'#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_7') = '#skF_9'
      | ~ v1_funct_1(k1_tmap_1(A_621,'#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'))
      | k7_relat_1('#skF_9',k9_subset_1(A_621,'#skF_6','#skF_7')) != k7_relat_1('#skF_8',k9_subset_1(A_621,'#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_621))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_621))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(A_621) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_861,c_3246])).

tff(c_3260,plain,(
    ! [A_624] :
      ( k2_partfun1(k4_subset_1(A_624,'#skF_6','#skF_7'),'#skF_5',k1_tmap_1(A_624,'#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_7') = '#skF_9'
      | ~ v1_funct_1(k1_tmap_1(A_624,'#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'))
      | k7_relat_1('#skF_9',k9_subset_1(A_624,'#skF_6','#skF_7')) != k7_relat_1('#skF_8',k9_subset_1(A_624,'#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_624))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_624))
      | v1_xboole_0(A_624) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3254])).

tff(c_461,plain,
    ( k2_partfun1(k4_subset_1('#skF_4','#skF_6','#skF_7'),'#skF_5',k1_tmap_1('#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_6') != '#skF_8'
    | k2_partfun1(k4_subset_1('#skF_4','#skF_6','#skF_7'),'#skF_5',k1_tmap_1('#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_7') != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_605,plain,(
    k2_partfun1(k4_subset_1('#skF_4','#skF_6','#skF_7'),'#skF_5',k1_tmap_1('#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_7') != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_461])).

tff(c_3271,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'))
    | k7_relat_1('#skF_9',k9_subset_1('#skF_4','#skF_6','#skF_7')) != k7_relat_1('#skF_8',k9_subset_1('#skF_4','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3260,c_605])).

tff(c_3285,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_887,c_662,c_662,c_1135,c_3271])).

tff(c_3287,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3285])).

tff(c_3288,plain,(
    k2_partfun1(k4_subset_1('#skF_4','#skF_6','#skF_7'),'#skF_5',k1_tmap_1('#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_6') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_461])).

tff(c_5732,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'))
    | k7_relat_1('#skF_9',k9_subset_1('#skF_4','#skF_6','#skF_7')) != k7_relat_1('#skF_8',k9_subset_1('#skF_4','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5723,c_3288])).

tff(c_5743,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_3600,c_3363,c_3363,c_3758,c_5732])).

tff(c_5745,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_5743])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:43:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.57/2.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.57/2.75  
% 8.57/2.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.57/2.75  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_2
% 8.57/2.75  
% 8.57/2.75  %Foreground sorts:
% 8.57/2.75  
% 8.57/2.75  
% 8.57/2.75  %Background operators:
% 8.57/2.75  
% 8.57/2.75  
% 8.57/2.75  %Foreground operators:
% 8.57/2.75  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 8.57/2.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.57/2.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.57/2.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.57/2.75  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.57/2.75  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.57/2.75  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.57/2.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.57/2.75  tff('#skF_7', type, '#skF_7': $i).
% 8.57/2.75  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.57/2.75  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 8.57/2.75  tff('#skF_5', type, '#skF_5': $i).
% 8.57/2.75  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.57/2.75  tff('#skF_6', type, '#skF_6': $i).
% 8.57/2.75  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.57/2.75  tff('#skF_9', type, '#skF_9': $i).
% 8.57/2.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.57/2.75  tff('#skF_8', type, '#skF_8': $i).
% 8.57/2.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.57/2.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.57/2.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.57/2.75  tff('#skF_4', type, '#skF_4': $i).
% 8.57/2.75  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.57/2.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.57/2.75  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.57/2.75  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 8.57/2.75  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.57/2.75  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.57/2.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.57/2.75  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 8.57/2.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.57/2.75  
% 8.81/2.78  tff(f_231, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 8.81/2.78  tff(f_107, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 8.81/2.78  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 8.81/2.78  tff(f_97, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 8.81/2.78  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.81/2.78  tff(f_67, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 8.81/2.78  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.81/2.78  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 8.81/2.78  tff(f_87, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 8.81/2.78  tff(f_189, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 8.81/2.78  tff(f_155, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 8.81/2.78  tff(c_72, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.81/2.78  tff(c_66, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.81/2.78  tff(c_62, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.81/2.78  tff(c_58, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.81/2.78  tff(c_54, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.81/2.78  tff(c_3567, plain, (![A_668, B_669, C_670, D_671]: (k2_partfun1(A_668, B_669, C_670, D_671)=k7_relat_1(C_670, D_671) | ~m1_subset_1(C_670, k1_zfmisc_1(k2_zfmisc_1(A_668, B_669))) | ~v1_funct_1(C_670))), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.81/2.78  tff(c_3569, plain, (![D_671]: (k2_partfun1('#skF_6', '#skF_5', '#skF_8', D_671)=k7_relat_1('#skF_8', D_671) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_54, c_3567])).
% 8.81/2.78  tff(c_3574, plain, (![D_671]: (k2_partfun1('#skF_6', '#skF_5', '#skF_8', D_671)=k7_relat_1('#skF_8', D_671))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_3569])).
% 8.81/2.78  tff(c_3351, plain, (![A_639, B_640, C_641]: (k9_subset_1(A_639, B_640, C_641)=k3_xboole_0(B_640, C_641) | ~m1_subset_1(C_641, k1_zfmisc_1(A_639)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.81/2.78  tff(c_3363, plain, (![B_640]: (k9_subset_1('#skF_4', B_640, '#skF_7')=k3_xboole_0(B_640, '#skF_7'))), inference(resolution, [status(thm)], [c_62, c_3351])).
% 8.81/2.78  tff(c_68, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.81/2.78  tff(c_64, plain, (~v1_xboole_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.81/2.78  tff(c_60, plain, (r1_subset_1('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.81/2.78  tff(c_28, plain, (![A_28, B_29]: (r1_xboole_0(A_28, B_29) | ~r1_subset_1(A_28, B_29) | v1_xboole_0(B_29) | v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.81/2.78  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.81/2.78  tff(c_129, plain, (![A_245, B_246, C_247]: (~r1_xboole_0(A_245, B_246) | ~r2_hidden(C_247, k3_xboole_0(A_245, B_246)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.81/2.78  tff(c_144, plain, (![A_245, B_246]: (~r1_xboole_0(A_245, B_246) | v1_xboole_0(k3_xboole_0(A_245, B_246)))), inference(resolution, [status(thm)], [c_4, c_129])).
% 8.81/2.78  tff(c_48, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.81/2.78  tff(c_120, plain, (![C_242, A_243, B_244]: (v1_relat_1(C_242) | ~m1_subset_1(C_242, k1_zfmisc_1(k2_zfmisc_1(A_243, B_244))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.81/2.78  tff(c_128, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_48, c_120])).
% 8.81/2.78  tff(c_80, plain, (![A_232, B_233]: (r2_hidden('#skF_2'(A_232, B_233), A_232) | r1_xboole_0(A_232, B_233))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.81/2.78  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.81/2.78  tff(c_84, plain, (![A_232, B_233]: (~v1_xboole_0(A_232) | r1_xboole_0(A_232, B_233))), inference(resolution, [status(thm)], [c_80, c_2])).
% 8.81/2.78  tff(c_224, plain, (![A_269, B_270]: (k7_relat_1(A_269, B_270)=k1_xboole_0 | ~r1_xboole_0(B_270, k1_relat_1(A_269)) | ~v1_relat_1(A_269))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.81/2.78  tff(c_245, plain, (![A_271, A_272]: (k7_relat_1(A_271, A_272)=k1_xboole_0 | ~v1_relat_1(A_271) | ~v1_xboole_0(A_272))), inference(resolution, [status(thm)], [c_84, c_224])).
% 8.81/2.78  tff(c_252, plain, (![A_273]: (k7_relat_1('#skF_9', A_273)=k1_xboole_0 | ~v1_xboole_0(A_273))), inference(resolution, [status(thm)], [c_128, c_245])).
% 8.81/2.78  tff(c_256, plain, (![A_245, B_246]: (k7_relat_1('#skF_9', k3_xboole_0(A_245, B_246))=k1_xboole_0 | ~r1_xboole_0(A_245, B_246))), inference(resolution, [status(thm)], [c_144, c_252])).
% 8.81/2.78  tff(c_52, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.81/2.78  tff(c_359, plain, (![A_292, B_293, C_294, D_295]: (k2_partfun1(A_292, B_293, C_294, D_295)=k7_relat_1(C_294, D_295) | ~m1_subset_1(C_294, k1_zfmisc_1(k2_zfmisc_1(A_292, B_293))) | ~v1_funct_1(C_294))), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.81/2.78  tff(c_363, plain, (![D_295]: (k2_partfun1('#skF_7', '#skF_5', '#skF_9', D_295)=k7_relat_1('#skF_9', D_295) | ~v1_funct_1('#skF_9'))), inference(resolution, [status(thm)], [c_48, c_359])).
% 8.81/2.78  tff(c_369, plain, (![D_295]: (k2_partfun1('#skF_7', '#skF_5', '#skF_9', D_295)=k7_relat_1('#skF_9', D_295))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_363])).
% 8.81/2.78  tff(c_361, plain, (![D_295]: (k2_partfun1('#skF_6', '#skF_5', '#skF_8', D_295)=k7_relat_1('#skF_8', D_295) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_54, c_359])).
% 8.81/2.78  tff(c_366, plain, (![D_295]: (k2_partfun1('#skF_6', '#skF_5', '#skF_8', D_295)=k7_relat_1('#skF_8', D_295))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_361])).
% 8.81/2.78  tff(c_262, plain, (![A_275, B_276, C_277]: (k9_subset_1(A_275, B_276, C_277)=k3_xboole_0(B_276, C_277) | ~m1_subset_1(C_277, k1_zfmisc_1(A_275)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.81/2.78  tff(c_274, plain, (![B_276]: (k9_subset_1('#skF_4', B_276, '#skF_7')=k3_xboole_0(B_276, '#skF_7'))), inference(resolution, [status(thm)], [c_62, c_262])).
% 8.81/2.78  tff(c_46, plain, (k2_partfun1(k4_subset_1('#skF_4', '#skF_6', '#skF_7'), '#skF_5', k1_tmap_1('#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_7')!='#skF_9' | k2_partfun1(k4_subset_1('#skF_4', '#skF_6', '#skF_7'), '#skF_5', k1_tmap_1('#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_6')!='#skF_8' | k2_partfun1('#skF_7', '#skF_5', '#skF_9', k9_subset_1('#skF_4', '#skF_6', '#skF_7'))!=k2_partfun1('#skF_6', '#skF_5', '#skF_8', k9_subset_1('#skF_4', '#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.81/2.78  tff(c_93, plain, (k2_partfun1('#skF_7', '#skF_5', '#skF_9', k9_subset_1('#skF_4', '#skF_6', '#skF_7'))!=k2_partfun1('#skF_6', '#skF_5', '#skF_8', k9_subset_1('#skF_4', '#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_46])).
% 8.81/2.78  tff(c_284, plain, (k2_partfun1('#skF_7', '#skF_5', '#skF_9', k3_xboole_0('#skF_6', '#skF_7'))!=k2_partfun1('#skF_6', '#skF_5', '#skF_8', k3_xboole_0('#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_274, c_274, c_93])).
% 8.81/2.78  tff(c_389, plain, (k7_relat_1('#skF_9', k3_xboole_0('#skF_6', '#skF_7'))!=k7_relat_1('#skF_8', k3_xboole_0('#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_369, c_366, c_284])).
% 8.81/2.78  tff(c_392, plain, (k7_relat_1('#skF_8', k3_xboole_0('#skF_6', '#skF_7'))!=k1_xboole_0 | ~r1_xboole_0('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_256, c_389])).
% 8.81/2.78  tff(c_393, plain, (~r1_xboole_0('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_392])).
% 8.81/2.78  tff(c_399, plain, (~r1_subset_1('#skF_6', '#skF_7') | v1_xboole_0('#skF_7') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_28, c_393])).
% 8.81/2.78  tff(c_411, plain, (v1_xboole_0('#skF_7') | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_399])).
% 8.81/2.78  tff(c_413, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_64, c_411])).
% 8.81/2.78  tff(c_415, plain, (r1_xboole_0('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_392])).
% 8.81/2.78  tff(c_127, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_54, c_120])).
% 8.81/2.78  tff(c_257, plain, (![A_274]: (k7_relat_1('#skF_8', A_274)=k1_xboole_0 | ~v1_xboole_0(A_274))), inference(resolution, [status(thm)], [c_127, c_245])).
% 8.81/2.78  tff(c_261, plain, (![A_245, B_246]: (k7_relat_1('#skF_8', k3_xboole_0(A_245, B_246))=k1_xboole_0 | ~r1_xboole_0(A_245, B_246))), inference(resolution, [status(thm)], [c_144, c_257])).
% 8.81/2.78  tff(c_414, plain, (k7_relat_1('#skF_8', k3_xboole_0('#skF_6', '#skF_7'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_392])).
% 8.81/2.78  tff(c_456, plain, (~r1_xboole_0('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_261, c_414])).
% 8.81/2.78  tff(c_460, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_415, c_456])).
% 8.81/2.78  tff(c_462, plain, (k2_partfun1('#skF_7', '#skF_5', '#skF_9', k9_subset_1('#skF_4', '#skF_6', '#skF_7'))=k2_partfun1('#skF_6', '#skF_5', '#skF_8', k9_subset_1('#skF_4', '#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_46])).
% 8.81/2.78  tff(c_3373, plain, (k2_partfun1('#skF_7', '#skF_5', '#skF_9', k3_xboole_0('#skF_6', '#skF_7'))=k2_partfun1('#skF_6', '#skF_5', '#skF_8', k3_xboole_0('#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_3363, c_3363, c_462])).
% 8.81/2.78  tff(c_3578, plain, (k2_partfun1('#skF_7', '#skF_5', '#skF_9', k3_xboole_0('#skF_6', '#skF_7'))=k7_relat_1('#skF_8', k3_xboole_0('#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_3574, c_3373])).
% 8.81/2.78  tff(c_3571, plain, (![D_671]: (k2_partfun1('#skF_7', '#skF_5', '#skF_9', D_671)=k7_relat_1('#skF_9', D_671) | ~v1_funct_1('#skF_9'))), inference(resolution, [status(thm)], [c_48, c_3567])).
% 8.81/2.78  tff(c_3577, plain, (![D_671]: (k2_partfun1('#skF_7', '#skF_5', '#skF_9', D_671)=k7_relat_1('#skF_9', D_671))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_3571])).
% 8.81/2.78  tff(c_3600, plain, (k7_relat_1('#skF_9', k3_xboole_0('#skF_6', '#skF_7'))=k7_relat_1('#skF_8', k3_xboole_0('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_3578, c_3577])).
% 8.81/2.78  tff(c_56, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.81/2.78  tff(c_70, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.81/2.78  tff(c_50, plain, (v1_funct_2('#skF_9', '#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.81/2.78  tff(c_3648, plain, (![E_687, B_686, D_684, F_688, A_685, C_689]: (v1_funct_1(k1_tmap_1(A_685, B_686, C_689, D_684, E_687, F_688)) | ~m1_subset_1(F_688, k1_zfmisc_1(k2_zfmisc_1(D_684, B_686))) | ~v1_funct_2(F_688, D_684, B_686) | ~v1_funct_1(F_688) | ~m1_subset_1(E_687, k1_zfmisc_1(k2_zfmisc_1(C_689, B_686))) | ~v1_funct_2(E_687, C_689, B_686) | ~v1_funct_1(E_687) | ~m1_subset_1(D_684, k1_zfmisc_1(A_685)) | v1_xboole_0(D_684) | ~m1_subset_1(C_689, k1_zfmisc_1(A_685)) | v1_xboole_0(C_689) | v1_xboole_0(B_686) | v1_xboole_0(A_685))), inference(cnfTransformation, [status(thm)], [f_189])).
% 8.81/2.78  tff(c_3652, plain, (![A_685, C_689, E_687]: (v1_funct_1(k1_tmap_1(A_685, '#skF_5', C_689, '#skF_7', E_687, '#skF_9')) | ~v1_funct_2('#skF_9', '#skF_7', '#skF_5') | ~v1_funct_1('#skF_9') | ~m1_subset_1(E_687, k1_zfmisc_1(k2_zfmisc_1(C_689, '#skF_5'))) | ~v1_funct_2(E_687, C_689, '#skF_5') | ~v1_funct_1(E_687) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_685)) | v1_xboole_0('#skF_7') | ~m1_subset_1(C_689, k1_zfmisc_1(A_685)) | v1_xboole_0(C_689) | v1_xboole_0('#skF_5') | v1_xboole_0(A_685))), inference(resolution, [status(thm)], [c_48, c_3648])).
% 8.81/2.78  tff(c_3659, plain, (![A_685, C_689, E_687]: (v1_funct_1(k1_tmap_1(A_685, '#skF_5', C_689, '#skF_7', E_687, '#skF_9')) | ~m1_subset_1(E_687, k1_zfmisc_1(k2_zfmisc_1(C_689, '#skF_5'))) | ~v1_funct_2(E_687, C_689, '#skF_5') | ~v1_funct_1(E_687) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_685)) | v1_xboole_0('#skF_7') | ~m1_subset_1(C_689, k1_zfmisc_1(A_685)) | v1_xboole_0(C_689) | v1_xboole_0('#skF_5') | v1_xboole_0(A_685))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_3652])).
% 8.81/2.78  tff(c_3730, plain, (![A_698, C_699, E_700]: (v1_funct_1(k1_tmap_1(A_698, '#skF_5', C_699, '#skF_7', E_700, '#skF_9')) | ~m1_subset_1(E_700, k1_zfmisc_1(k2_zfmisc_1(C_699, '#skF_5'))) | ~v1_funct_2(E_700, C_699, '#skF_5') | ~v1_funct_1(E_700) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_698)) | ~m1_subset_1(C_699, k1_zfmisc_1(A_698)) | v1_xboole_0(C_699) | v1_xboole_0(A_698))), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_3659])).
% 8.81/2.78  tff(c_3732, plain, (![A_698]: (v1_funct_1(k1_tmap_1(A_698, '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_5') | ~v1_funct_1('#skF_8') | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_698)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_698)) | v1_xboole_0('#skF_6') | v1_xboole_0(A_698))), inference(resolution, [status(thm)], [c_54, c_3730])).
% 8.81/2.78  tff(c_3737, plain, (![A_698]: (v1_funct_1(k1_tmap_1(A_698, '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_698)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_698)) | v1_xboole_0('#skF_6') | v1_xboole_0(A_698))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_3732])).
% 8.81/2.78  tff(c_3751, plain, (![A_702]: (v1_funct_1(k1_tmap_1(A_702, '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_702)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_702)) | v1_xboole_0(A_702))), inference(negUnitSimplification, [status(thm)], [c_68, c_3737])).
% 8.81/2.78  tff(c_3754, plain, (v1_funct_1(k1_tmap_1('#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_62, c_3751])).
% 8.81/2.78  tff(c_3757, plain, (v1_funct_1(k1_tmap_1('#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')) | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_3754])).
% 8.81/2.78  tff(c_3758, plain, (v1_funct_1(k1_tmap_1('#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_72, c_3757])).
% 8.81/2.78  tff(c_42, plain, (![C_166, D_167, E_168, A_164, B_165, F_169]: (v1_funct_2(k1_tmap_1(A_164, B_165, C_166, D_167, E_168, F_169), k4_subset_1(A_164, C_166, D_167), B_165) | ~m1_subset_1(F_169, k1_zfmisc_1(k2_zfmisc_1(D_167, B_165))) | ~v1_funct_2(F_169, D_167, B_165) | ~v1_funct_1(F_169) | ~m1_subset_1(E_168, k1_zfmisc_1(k2_zfmisc_1(C_166, B_165))) | ~v1_funct_2(E_168, C_166, B_165) | ~v1_funct_1(E_168) | ~m1_subset_1(D_167, k1_zfmisc_1(A_164)) | v1_xboole_0(D_167) | ~m1_subset_1(C_166, k1_zfmisc_1(A_164)) | v1_xboole_0(C_166) | v1_xboole_0(B_165) | v1_xboole_0(A_164))), inference(cnfTransformation, [status(thm)], [f_189])).
% 8.81/2.78  tff(c_40, plain, (![C_166, D_167, E_168, A_164, B_165, F_169]: (m1_subset_1(k1_tmap_1(A_164, B_165, C_166, D_167, E_168, F_169), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_164, C_166, D_167), B_165))) | ~m1_subset_1(F_169, k1_zfmisc_1(k2_zfmisc_1(D_167, B_165))) | ~v1_funct_2(F_169, D_167, B_165) | ~v1_funct_1(F_169) | ~m1_subset_1(E_168, k1_zfmisc_1(k2_zfmisc_1(C_166, B_165))) | ~v1_funct_2(E_168, C_166, B_165) | ~v1_funct_1(E_168) | ~m1_subset_1(D_167, k1_zfmisc_1(A_164)) | v1_xboole_0(D_167) | ~m1_subset_1(C_166, k1_zfmisc_1(A_164)) | v1_xboole_0(C_166) | v1_xboole_0(B_165) | v1_xboole_0(A_164))), inference(cnfTransformation, [status(thm)], [f_189])).
% 8.81/2.78  tff(c_3989, plain, (![C_739, F_740, B_741, D_743, E_742, A_738]: (k2_partfun1(k4_subset_1(A_738, C_739, D_743), B_741, k1_tmap_1(A_738, B_741, C_739, D_743, E_742, F_740), C_739)=E_742 | ~m1_subset_1(k1_tmap_1(A_738, B_741, C_739, D_743, E_742, F_740), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_738, C_739, D_743), B_741))) | ~v1_funct_2(k1_tmap_1(A_738, B_741, C_739, D_743, E_742, F_740), k4_subset_1(A_738, C_739, D_743), B_741) | ~v1_funct_1(k1_tmap_1(A_738, B_741, C_739, D_743, E_742, F_740)) | k2_partfun1(D_743, B_741, F_740, k9_subset_1(A_738, C_739, D_743))!=k2_partfun1(C_739, B_741, E_742, k9_subset_1(A_738, C_739, D_743)) | ~m1_subset_1(F_740, k1_zfmisc_1(k2_zfmisc_1(D_743, B_741))) | ~v1_funct_2(F_740, D_743, B_741) | ~v1_funct_1(F_740) | ~m1_subset_1(E_742, k1_zfmisc_1(k2_zfmisc_1(C_739, B_741))) | ~v1_funct_2(E_742, C_739, B_741) | ~v1_funct_1(E_742) | ~m1_subset_1(D_743, k1_zfmisc_1(A_738)) | v1_xboole_0(D_743) | ~m1_subset_1(C_739, k1_zfmisc_1(A_738)) | v1_xboole_0(C_739) | v1_xboole_0(B_741) | v1_xboole_0(A_738))), inference(cnfTransformation, [status(thm)], [f_155])).
% 8.81/2.78  tff(c_5064, plain, (![D_835, C_840, F_839, E_838, A_836, B_837]: (k2_partfun1(k4_subset_1(A_836, C_840, D_835), B_837, k1_tmap_1(A_836, B_837, C_840, D_835, E_838, F_839), C_840)=E_838 | ~v1_funct_2(k1_tmap_1(A_836, B_837, C_840, D_835, E_838, F_839), k4_subset_1(A_836, C_840, D_835), B_837) | ~v1_funct_1(k1_tmap_1(A_836, B_837, C_840, D_835, E_838, F_839)) | k2_partfun1(D_835, B_837, F_839, k9_subset_1(A_836, C_840, D_835))!=k2_partfun1(C_840, B_837, E_838, k9_subset_1(A_836, C_840, D_835)) | ~m1_subset_1(F_839, k1_zfmisc_1(k2_zfmisc_1(D_835, B_837))) | ~v1_funct_2(F_839, D_835, B_837) | ~v1_funct_1(F_839) | ~m1_subset_1(E_838, k1_zfmisc_1(k2_zfmisc_1(C_840, B_837))) | ~v1_funct_2(E_838, C_840, B_837) | ~v1_funct_1(E_838) | ~m1_subset_1(D_835, k1_zfmisc_1(A_836)) | v1_xboole_0(D_835) | ~m1_subset_1(C_840, k1_zfmisc_1(A_836)) | v1_xboole_0(C_840) | v1_xboole_0(B_837) | v1_xboole_0(A_836))), inference(resolution, [status(thm)], [c_40, c_3989])).
% 8.81/2.78  tff(c_5318, plain, (![B_862, A_861, F_864, E_863, C_865, D_860]: (k2_partfun1(k4_subset_1(A_861, C_865, D_860), B_862, k1_tmap_1(A_861, B_862, C_865, D_860, E_863, F_864), C_865)=E_863 | ~v1_funct_1(k1_tmap_1(A_861, B_862, C_865, D_860, E_863, F_864)) | k2_partfun1(D_860, B_862, F_864, k9_subset_1(A_861, C_865, D_860))!=k2_partfun1(C_865, B_862, E_863, k9_subset_1(A_861, C_865, D_860)) | ~m1_subset_1(F_864, k1_zfmisc_1(k2_zfmisc_1(D_860, B_862))) | ~v1_funct_2(F_864, D_860, B_862) | ~v1_funct_1(F_864) | ~m1_subset_1(E_863, k1_zfmisc_1(k2_zfmisc_1(C_865, B_862))) | ~v1_funct_2(E_863, C_865, B_862) | ~v1_funct_1(E_863) | ~m1_subset_1(D_860, k1_zfmisc_1(A_861)) | v1_xboole_0(D_860) | ~m1_subset_1(C_865, k1_zfmisc_1(A_861)) | v1_xboole_0(C_865) | v1_xboole_0(B_862) | v1_xboole_0(A_861))), inference(resolution, [status(thm)], [c_42, c_5064])).
% 8.81/2.78  tff(c_5324, plain, (![A_861, C_865, E_863]: (k2_partfun1(k4_subset_1(A_861, C_865, '#skF_7'), '#skF_5', k1_tmap_1(A_861, '#skF_5', C_865, '#skF_7', E_863, '#skF_9'), C_865)=E_863 | ~v1_funct_1(k1_tmap_1(A_861, '#skF_5', C_865, '#skF_7', E_863, '#skF_9')) | k2_partfun1(C_865, '#skF_5', E_863, k9_subset_1(A_861, C_865, '#skF_7'))!=k2_partfun1('#skF_7', '#skF_5', '#skF_9', k9_subset_1(A_861, C_865, '#skF_7')) | ~v1_funct_2('#skF_9', '#skF_7', '#skF_5') | ~v1_funct_1('#skF_9') | ~m1_subset_1(E_863, k1_zfmisc_1(k2_zfmisc_1(C_865, '#skF_5'))) | ~v1_funct_2(E_863, C_865, '#skF_5') | ~v1_funct_1(E_863) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_861)) | v1_xboole_0('#skF_7') | ~m1_subset_1(C_865, k1_zfmisc_1(A_861)) | v1_xboole_0(C_865) | v1_xboole_0('#skF_5') | v1_xboole_0(A_861))), inference(resolution, [status(thm)], [c_48, c_5318])).
% 8.81/2.78  tff(c_5332, plain, (![A_861, C_865, E_863]: (k2_partfun1(k4_subset_1(A_861, C_865, '#skF_7'), '#skF_5', k1_tmap_1(A_861, '#skF_5', C_865, '#skF_7', E_863, '#skF_9'), C_865)=E_863 | ~v1_funct_1(k1_tmap_1(A_861, '#skF_5', C_865, '#skF_7', E_863, '#skF_9')) | k2_partfun1(C_865, '#skF_5', E_863, k9_subset_1(A_861, C_865, '#skF_7'))!=k7_relat_1('#skF_9', k9_subset_1(A_861, C_865, '#skF_7')) | ~m1_subset_1(E_863, k1_zfmisc_1(k2_zfmisc_1(C_865, '#skF_5'))) | ~v1_funct_2(E_863, C_865, '#skF_5') | ~v1_funct_1(E_863) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_861)) | v1_xboole_0('#skF_7') | ~m1_subset_1(C_865, k1_zfmisc_1(A_861)) | v1_xboole_0(C_865) | v1_xboole_0('#skF_5') | v1_xboole_0(A_861))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_3577, c_5324])).
% 8.81/2.78  tff(c_5481, plain, (![A_876, C_877, E_878]: (k2_partfun1(k4_subset_1(A_876, C_877, '#skF_7'), '#skF_5', k1_tmap_1(A_876, '#skF_5', C_877, '#skF_7', E_878, '#skF_9'), C_877)=E_878 | ~v1_funct_1(k1_tmap_1(A_876, '#skF_5', C_877, '#skF_7', E_878, '#skF_9')) | k2_partfun1(C_877, '#skF_5', E_878, k9_subset_1(A_876, C_877, '#skF_7'))!=k7_relat_1('#skF_9', k9_subset_1(A_876, C_877, '#skF_7')) | ~m1_subset_1(E_878, k1_zfmisc_1(k2_zfmisc_1(C_877, '#skF_5'))) | ~v1_funct_2(E_878, C_877, '#skF_5') | ~v1_funct_1(E_878) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_876)) | ~m1_subset_1(C_877, k1_zfmisc_1(A_876)) | v1_xboole_0(C_877) | v1_xboole_0(A_876))), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_5332])).
% 8.81/2.78  tff(c_5486, plain, (![A_876]: (k2_partfun1(k4_subset_1(A_876, '#skF_6', '#skF_7'), '#skF_5', k1_tmap_1(A_876, '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_876, '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')) | k2_partfun1('#skF_6', '#skF_5', '#skF_8', k9_subset_1(A_876, '#skF_6', '#skF_7'))!=k7_relat_1('#skF_9', k9_subset_1(A_876, '#skF_6', '#skF_7')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_5') | ~v1_funct_1('#skF_8') | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_876)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_876)) | v1_xboole_0('#skF_6') | v1_xboole_0(A_876))), inference(resolution, [status(thm)], [c_54, c_5481])).
% 8.81/2.78  tff(c_5494, plain, (![A_876]: (k2_partfun1(k4_subset_1(A_876, '#skF_6', '#skF_7'), '#skF_5', k1_tmap_1(A_876, '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_876, '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')) | k7_relat_1('#skF_9', k9_subset_1(A_876, '#skF_6', '#skF_7'))!=k7_relat_1('#skF_8', k9_subset_1(A_876, '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_876)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_876)) | v1_xboole_0('#skF_6') | v1_xboole_0(A_876))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_3574, c_5486])).
% 8.81/2.78  tff(c_5723, plain, (![A_892]: (k2_partfun1(k4_subset_1(A_892, '#skF_6', '#skF_7'), '#skF_5', k1_tmap_1(A_892, '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_892, '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')) | k7_relat_1('#skF_9', k9_subset_1(A_892, '#skF_6', '#skF_7'))!=k7_relat_1('#skF_8', k9_subset_1(A_892, '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_892)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_892)) | v1_xboole_0(A_892))), inference(negUnitSimplification, [status(thm)], [c_68, c_5494])).
% 8.81/2.78  tff(c_854, plain, (![A_376, B_377, C_378, D_379]: (k2_partfun1(A_376, B_377, C_378, D_379)=k7_relat_1(C_378, D_379) | ~m1_subset_1(C_378, k1_zfmisc_1(k2_zfmisc_1(A_376, B_377))) | ~v1_funct_1(C_378))), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.81/2.78  tff(c_856, plain, (![D_379]: (k2_partfun1('#skF_6', '#skF_5', '#skF_8', D_379)=k7_relat_1('#skF_8', D_379) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_54, c_854])).
% 8.81/2.78  tff(c_861, plain, (![D_379]: (k2_partfun1('#skF_6', '#skF_5', '#skF_8', D_379)=k7_relat_1('#skF_8', D_379))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_856])).
% 8.81/2.78  tff(c_650, plain, (![A_345, B_346, C_347]: (k9_subset_1(A_345, B_346, C_347)=k3_xboole_0(B_346, C_347) | ~m1_subset_1(C_347, k1_zfmisc_1(A_345)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.81/2.78  tff(c_662, plain, (![B_346]: (k9_subset_1('#skF_4', B_346, '#skF_7')=k3_xboole_0(B_346, '#skF_7'))), inference(resolution, [status(thm)], [c_62, c_650])).
% 8.81/2.78  tff(c_677, plain, (k2_partfun1('#skF_7', '#skF_5', '#skF_9', k3_xboole_0('#skF_6', '#skF_7'))=k2_partfun1('#skF_6', '#skF_5', '#skF_8', k3_xboole_0('#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_662, c_662, c_462])).
% 8.81/2.78  tff(c_865, plain, (k2_partfun1('#skF_7', '#skF_5', '#skF_9', k3_xboole_0('#skF_6', '#skF_7'))=k7_relat_1('#skF_8', k3_xboole_0('#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_861, c_677])).
% 8.81/2.78  tff(c_858, plain, (![D_379]: (k2_partfun1('#skF_7', '#skF_5', '#skF_9', D_379)=k7_relat_1('#skF_9', D_379) | ~v1_funct_1('#skF_9'))), inference(resolution, [status(thm)], [c_48, c_854])).
% 8.81/2.78  tff(c_864, plain, (![D_379]: (k2_partfun1('#skF_7', '#skF_5', '#skF_9', D_379)=k7_relat_1('#skF_9', D_379))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_858])).
% 8.81/2.78  tff(c_887, plain, (k7_relat_1('#skF_9', k3_xboole_0('#skF_6', '#skF_7'))=k7_relat_1('#skF_8', k3_xboole_0('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_865, c_864])).
% 8.81/2.78  tff(c_950, plain, (![A_390, E_392, F_393, B_391, C_394, D_389]: (v1_funct_1(k1_tmap_1(A_390, B_391, C_394, D_389, E_392, F_393)) | ~m1_subset_1(F_393, k1_zfmisc_1(k2_zfmisc_1(D_389, B_391))) | ~v1_funct_2(F_393, D_389, B_391) | ~v1_funct_1(F_393) | ~m1_subset_1(E_392, k1_zfmisc_1(k2_zfmisc_1(C_394, B_391))) | ~v1_funct_2(E_392, C_394, B_391) | ~v1_funct_1(E_392) | ~m1_subset_1(D_389, k1_zfmisc_1(A_390)) | v1_xboole_0(D_389) | ~m1_subset_1(C_394, k1_zfmisc_1(A_390)) | v1_xboole_0(C_394) | v1_xboole_0(B_391) | v1_xboole_0(A_390))), inference(cnfTransformation, [status(thm)], [f_189])).
% 8.81/2.78  tff(c_954, plain, (![A_390, C_394, E_392]: (v1_funct_1(k1_tmap_1(A_390, '#skF_5', C_394, '#skF_7', E_392, '#skF_9')) | ~v1_funct_2('#skF_9', '#skF_7', '#skF_5') | ~v1_funct_1('#skF_9') | ~m1_subset_1(E_392, k1_zfmisc_1(k2_zfmisc_1(C_394, '#skF_5'))) | ~v1_funct_2(E_392, C_394, '#skF_5') | ~v1_funct_1(E_392) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_390)) | v1_xboole_0('#skF_7') | ~m1_subset_1(C_394, k1_zfmisc_1(A_390)) | v1_xboole_0(C_394) | v1_xboole_0('#skF_5') | v1_xboole_0(A_390))), inference(resolution, [status(thm)], [c_48, c_950])).
% 8.81/2.78  tff(c_961, plain, (![A_390, C_394, E_392]: (v1_funct_1(k1_tmap_1(A_390, '#skF_5', C_394, '#skF_7', E_392, '#skF_9')) | ~m1_subset_1(E_392, k1_zfmisc_1(k2_zfmisc_1(C_394, '#skF_5'))) | ~v1_funct_2(E_392, C_394, '#skF_5') | ~v1_funct_1(E_392) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_390)) | v1_xboole_0('#skF_7') | ~m1_subset_1(C_394, k1_zfmisc_1(A_390)) | v1_xboole_0(C_394) | v1_xboole_0('#skF_5') | v1_xboole_0(A_390))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_954])).
% 8.81/2.78  tff(c_1108, plain, (![A_421, C_422, E_423]: (v1_funct_1(k1_tmap_1(A_421, '#skF_5', C_422, '#skF_7', E_423, '#skF_9')) | ~m1_subset_1(E_423, k1_zfmisc_1(k2_zfmisc_1(C_422, '#skF_5'))) | ~v1_funct_2(E_423, C_422, '#skF_5') | ~v1_funct_1(E_423) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_421)) | ~m1_subset_1(C_422, k1_zfmisc_1(A_421)) | v1_xboole_0(C_422) | v1_xboole_0(A_421))), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_961])).
% 8.81/2.78  tff(c_1110, plain, (![A_421]: (v1_funct_1(k1_tmap_1(A_421, '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_5') | ~v1_funct_1('#skF_8') | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_421)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_421)) | v1_xboole_0('#skF_6') | v1_xboole_0(A_421))), inference(resolution, [status(thm)], [c_54, c_1108])).
% 8.81/2.78  tff(c_1115, plain, (![A_421]: (v1_funct_1(k1_tmap_1(A_421, '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_421)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_421)) | v1_xboole_0('#skF_6') | v1_xboole_0(A_421))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_1110])).
% 8.81/2.78  tff(c_1128, plain, (![A_425]: (v1_funct_1(k1_tmap_1(A_425, '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_425)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_425)) | v1_xboole_0(A_425))), inference(negUnitSimplification, [status(thm)], [c_68, c_1115])).
% 8.81/2.78  tff(c_1131, plain, (v1_funct_1(k1_tmap_1('#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_62, c_1128])).
% 8.81/2.78  tff(c_1134, plain, (v1_funct_1(k1_tmap_1('#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')) | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1131])).
% 8.81/2.78  tff(c_1135, plain, (v1_funct_1(k1_tmap_1('#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_72, c_1134])).
% 8.81/2.78  tff(c_1299, plain, (![B_451, A_448, E_452, F_450, D_453, C_449]: (k2_partfun1(k4_subset_1(A_448, C_449, D_453), B_451, k1_tmap_1(A_448, B_451, C_449, D_453, E_452, F_450), D_453)=F_450 | ~m1_subset_1(k1_tmap_1(A_448, B_451, C_449, D_453, E_452, F_450), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_448, C_449, D_453), B_451))) | ~v1_funct_2(k1_tmap_1(A_448, B_451, C_449, D_453, E_452, F_450), k4_subset_1(A_448, C_449, D_453), B_451) | ~v1_funct_1(k1_tmap_1(A_448, B_451, C_449, D_453, E_452, F_450)) | k2_partfun1(D_453, B_451, F_450, k9_subset_1(A_448, C_449, D_453))!=k2_partfun1(C_449, B_451, E_452, k9_subset_1(A_448, C_449, D_453)) | ~m1_subset_1(F_450, k1_zfmisc_1(k2_zfmisc_1(D_453, B_451))) | ~v1_funct_2(F_450, D_453, B_451) | ~v1_funct_1(F_450) | ~m1_subset_1(E_452, k1_zfmisc_1(k2_zfmisc_1(C_449, B_451))) | ~v1_funct_2(E_452, C_449, B_451) | ~v1_funct_1(E_452) | ~m1_subset_1(D_453, k1_zfmisc_1(A_448)) | v1_xboole_0(D_453) | ~m1_subset_1(C_449, k1_zfmisc_1(A_448)) | v1_xboole_0(C_449) | v1_xboole_0(B_451) | v1_xboole_0(A_448))), inference(cnfTransformation, [status(thm)], [f_155])).
% 8.81/2.78  tff(c_2107, plain, (![E_536, D_533, F_537, A_534, B_535, C_538]: (k2_partfun1(k4_subset_1(A_534, C_538, D_533), B_535, k1_tmap_1(A_534, B_535, C_538, D_533, E_536, F_537), D_533)=F_537 | ~v1_funct_2(k1_tmap_1(A_534, B_535, C_538, D_533, E_536, F_537), k4_subset_1(A_534, C_538, D_533), B_535) | ~v1_funct_1(k1_tmap_1(A_534, B_535, C_538, D_533, E_536, F_537)) | k2_partfun1(D_533, B_535, F_537, k9_subset_1(A_534, C_538, D_533))!=k2_partfun1(C_538, B_535, E_536, k9_subset_1(A_534, C_538, D_533)) | ~m1_subset_1(F_537, k1_zfmisc_1(k2_zfmisc_1(D_533, B_535))) | ~v1_funct_2(F_537, D_533, B_535) | ~v1_funct_1(F_537) | ~m1_subset_1(E_536, k1_zfmisc_1(k2_zfmisc_1(C_538, B_535))) | ~v1_funct_2(E_536, C_538, B_535) | ~v1_funct_1(E_536) | ~m1_subset_1(D_533, k1_zfmisc_1(A_534)) | v1_xboole_0(D_533) | ~m1_subset_1(C_538, k1_zfmisc_1(A_534)) | v1_xboole_0(C_538) | v1_xboole_0(B_535) | v1_xboole_0(A_534))), inference(resolution, [status(thm)], [c_40, c_1299])).
% 8.81/2.78  tff(c_2746, plain, (![E_583, A_581, F_584, C_585, D_580, B_582]: (k2_partfun1(k4_subset_1(A_581, C_585, D_580), B_582, k1_tmap_1(A_581, B_582, C_585, D_580, E_583, F_584), D_580)=F_584 | ~v1_funct_1(k1_tmap_1(A_581, B_582, C_585, D_580, E_583, F_584)) | k2_partfun1(D_580, B_582, F_584, k9_subset_1(A_581, C_585, D_580))!=k2_partfun1(C_585, B_582, E_583, k9_subset_1(A_581, C_585, D_580)) | ~m1_subset_1(F_584, k1_zfmisc_1(k2_zfmisc_1(D_580, B_582))) | ~v1_funct_2(F_584, D_580, B_582) | ~v1_funct_1(F_584) | ~m1_subset_1(E_583, k1_zfmisc_1(k2_zfmisc_1(C_585, B_582))) | ~v1_funct_2(E_583, C_585, B_582) | ~v1_funct_1(E_583) | ~m1_subset_1(D_580, k1_zfmisc_1(A_581)) | v1_xboole_0(D_580) | ~m1_subset_1(C_585, k1_zfmisc_1(A_581)) | v1_xboole_0(C_585) | v1_xboole_0(B_582) | v1_xboole_0(A_581))), inference(resolution, [status(thm)], [c_42, c_2107])).
% 8.81/2.78  tff(c_2752, plain, (![A_581, C_585, E_583]: (k2_partfun1(k4_subset_1(A_581, C_585, '#skF_7'), '#skF_5', k1_tmap_1(A_581, '#skF_5', C_585, '#skF_7', E_583, '#skF_9'), '#skF_7')='#skF_9' | ~v1_funct_1(k1_tmap_1(A_581, '#skF_5', C_585, '#skF_7', E_583, '#skF_9')) | k2_partfun1(C_585, '#skF_5', E_583, k9_subset_1(A_581, C_585, '#skF_7'))!=k2_partfun1('#skF_7', '#skF_5', '#skF_9', k9_subset_1(A_581, C_585, '#skF_7')) | ~v1_funct_2('#skF_9', '#skF_7', '#skF_5') | ~v1_funct_1('#skF_9') | ~m1_subset_1(E_583, k1_zfmisc_1(k2_zfmisc_1(C_585, '#skF_5'))) | ~v1_funct_2(E_583, C_585, '#skF_5') | ~v1_funct_1(E_583) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_581)) | v1_xboole_0('#skF_7') | ~m1_subset_1(C_585, k1_zfmisc_1(A_581)) | v1_xboole_0(C_585) | v1_xboole_0('#skF_5') | v1_xboole_0(A_581))), inference(resolution, [status(thm)], [c_48, c_2746])).
% 8.81/2.78  tff(c_2760, plain, (![A_581, C_585, E_583]: (k2_partfun1(k4_subset_1(A_581, C_585, '#skF_7'), '#skF_5', k1_tmap_1(A_581, '#skF_5', C_585, '#skF_7', E_583, '#skF_9'), '#skF_7')='#skF_9' | ~v1_funct_1(k1_tmap_1(A_581, '#skF_5', C_585, '#skF_7', E_583, '#skF_9')) | k2_partfun1(C_585, '#skF_5', E_583, k9_subset_1(A_581, C_585, '#skF_7'))!=k7_relat_1('#skF_9', k9_subset_1(A_581, C_585, '#skF_7')) | ~m1_subset_1(E_583, k1_zfmisc_1(k2_zfmisc_1(C_585, '#skF_5'))) | ~v1_funct_2(E_583, C_585, '#skF_5') | ~v1_funct_1(E_583) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_581)) | v1_xboole_0('#skF_7') | ~m1_subset_1(C_585, k1_zfmisc_1(A_581)) | v1_xboole_0(C_585) | v1_xboole_0('#skF_5') | v1_xboole_0(A_581))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_864, c_2752])).
% 8.81/2.78  tff(c_3241, plain, (![A_621, C_622, E_623]: (k2_partfun1(k4_subset_1(A_621, C_622, '#skF_7'), '#skF_5', k1_tmap_1(A_621, '#skF_5', C_622, '#skF_7', E_623, '#skF_9'), '#skF_7')='#skF_9' | ~v1_funct_1(k1_tmap_1(A_621, '#skF_5', C_622, '#skF_7', E_623, '#skF_9')) | k2_partfun1(C_622, '#skF_5', E_623, k9_subset_1(A_621, C_622, '#skF_7'))!=k7_relat_1('#skF_9', k9_subset_1(A_621, C_622, '#skF_7')) | ~m1_subset_1(E_623, k1_zfmisc_1(k2_zfmisc_1(C_622, '#skF_5'))) | ~v1_funct_2(E_623, C_622, '#skF_5') | ~v1_funct_1(E_623) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_621)) | ~m1_subset_1(C_622, k1_zfmisc_1(A_621)) | v1_xboole_0(C_622) | v1_xboole_0(A_621))), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_2760])).
% 8.81/2.78  tff(c_3246, plain, (![A_621]: (k2_partfun1(k4_subset_1(A_621, '#skF_6', '#skF_7'), '#skF_5', k1_tmap_1(A_621, '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_7')='#skF_9' | ~v1_funct_1(k1_tmap_1(A_621, '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')) | k2_partfun1('#skF_6', '#skF_5', '#skF_8', k9_subset_1(A_621, '#skF_6', '#skF_7'))!=k7_relat_1('#skF_9', k9_subset_1(A_621, '#skF_6', '#skF_7')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_5') | ~v1_funct_1('#skF_8') | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_621)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_621)) | v1_xboole_0('#skF_6') | v1_xboole_0(A_621))), inference(resolution, [status(thm)], [c_54, c_3241])).
% 8.81/2.78  tff(c_3254, plain, (![A_621]: (k2_partfun1(k4_subset_1(A_621, '#skF_6', '#skF_7'), '#skF_5', k1_tmap_1(A_621, '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_7')='#skF_9' | ~v1_funct_1(k1_tmap_1(A_621, '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')) | k7_relat_1('#skF_9', k9_subset_1(A_621, '#skF_6', '#skF_7'))!=k7_relat_1('#skF_8', k9_subset_1(A_621, '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_621)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_621)) | v1_xboole_0('#skF_6') | v1_xboole_0(A_621))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_861, c_3246])).
% 8.81/2.78  tff(c_3260, plain, (![A_624]: (k2_partfun1(k4_subset_1(A_624, '#skF_6', '#skF_7'), '#skF_5', k1_tmap_1(A_624, '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_7')='#skF_9' | ~v1_funct_1(k1_tmap_1(A_624, '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')) | k7_relat_1('#skF_9', k9_subset_1(A_624, '#skF_6', '#skF_7'))!=k7_relat_1('#skF_8', k9_subset_1(A_624, '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_624)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_624)) | v1_xboole_0(A_624))), inference(negUnitSimplification, [status(thm)], [c_68, c_3254])).
% 8.81/2.78  tff(c_461, plain, (k2_partfun1(k4_subset_1('#skF_4', '#skF_6', '#skF_7'), '#skF_5', k1_tmap_1('#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_6')!='#skF_8' | k2_partfun1(k4_subset_1('#skF_4', '#skF_6', '#skF_7'), '#skF_5', k1_tmap_1('#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_7')!='#skF_9'), inference(splitRight, [status(thm)], [c_46])).
% 8.81/2.78  tff(c_605, plain, (k2_partfun1(k4_subset_1('#skF_4', '#skF_6', '#skF_7'), '#skF_5', k1_tmap_1('#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_7')!='#skF_9'), inference(splitLeft, [status(thm)], [c_461])).
% 8.81/2.78  tff(c_3271, plain, (~v1_funct_1(k1_tmap_1('#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')) | k7_relat_1('#skF_9', k9_subset_1('#skF_4', '#skF_6', '#skF_7'))!=k7_relat_1('#skF_8', k9_subset_1('#skF_4', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4')) | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3260, c_605])).
% 8.81/2.78  tff(c_3285, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_887, c_662, c_662, c_1135, c_3271])).
% 8.81/2.78  tff(c_3287, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_3285])).
% 8.81/2.78  tff(c_3288, plain, (k2_partfun1(k4_subset_1('#skF_4', '#skF_6', '#skF_7'), '#skF_5', k1_tmap_1('#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_6')!='#skF_8'), inference(splitRight, [status(thm)], [c_461])).
% 8.81/2.78  tff(c_5732, plain, (~v1_funct_1(k1_tmap_1('#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')) | k7_relat_1('#skF_9', k9_subset_1('#skF_4', '#skF_6', '#skF_7'))!=k7_relat_1('#skF_8', k9_subset_1('#skF_4', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4')) | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5723, c_3288])).
% 8.81/2.78  tff(c_5743, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_3600, c_3363, c_3363, c_3758, c_5732])).
% 8.81/2.78  tff(c_5745, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_5743])).
% 8.81/2.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.81/2.78  
% 8.81/2.78  Inference rules
% 8.81/2.78  ----------------------
% 8.81/2.78  #Ref     : 0
% 8.81/2.78  #Sup     : 1334
% 8.81/2.78  #Fact    : 0
% 8.81/2.78  #Define  : 0
% 8.81/2.78  #Split   : 7
% 8.81/2.78  #Chain   : 0
% 8.81/2.78  #Close   : 0
% 8.81/2.78  
% 8.81/2.78  Ordering : KBO
% 8.81/2.78  
% 8.81/2.78  Simplification rules
% 8.81/2.78  ----------------------
% 8.81/2.78  #Subsume      : 78
% 8.81/2.78  #Demod        : 1612
% 8.81/2.78  #Tautology    : 741
% 8.81/2.78  #SimpNegUnit  : 121
% 8.81/2.78  #BackRed      : 5
% 8.81/2.78  
% 8.81/2.78  #Partial instantiations: 0
% 8.81/2.78  #Strategies tried      : 1
% 8.81/2.78  
% 8.81/2.78  Timing (in seconds)
% 8.81/2.78  ----------------------
% 8.81/2.78  Preprocessing        : 0.41
% 8.81/2.78  Parsing              : 0.20
% 8.81/2.78  CNF conversion       : 0.06
% 8.81/2.78  Main loop            : 1.61
% 8.81/2.78  Inferencing          : 0.57
% 8.81/2.78  Reduction            : 0.60
% 8.81/2.78  Demodulation         : 0.49
% 8.81/2.78  BG Simplification    : 0.07
% 8.81/2.78  Subsumption          : 0.29
% 8.81/2.78  Abstraction          : 0.10
% 8.81/2.78  MUC search           : 0.00
% 8.81/2.78  Cooper               : 0.00
% 8.81/2.78  Total                : 2.07
% 8.81/2.78  Index Insertion      : 0.00
% 8.81/2.78  Index Deletion       : 0.00
% 8.81/2.78  Index Matching       : 0.00
% 8.81/2.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
