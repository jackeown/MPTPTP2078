%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1697+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:15 EST 2020

% Result     : Theorem 15.12s
% Output     : CNFRefutation 15.40s
% Verified   : 
% Statistics : Number of formulae       :  223 (1921 expanded)
%              Number of leaves         :   39 ( 723 expanded)
%              Depth                    :   23
%              Number of atoms          :  812 (10868 expanded)
%              Number of equality atoms :  140 (2046 expanded)
%              Maximal formula depth    :   24 (   5 average)
%              Maximal term depth       :    4 (   2 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tmap_1)).

tff(f_124,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_173,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_169,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_148,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
       => r1_subset_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_subset_1)).

tff(f_138,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_150,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_128,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_123,axiom,(
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

tff(f_85,axiom,(
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

tff(c_76,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_72,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_70,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_24,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_77,plain,(
    ! [A_216] :
      ( k1_xboole_0 = A_216
      | ~ v1_xboole_0(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_81,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_77])).

tff(c_82,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_24])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_60,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_967,plain,(
    ! [B_351,A_352,D_353,C_354] :
      ( k1_xboole_0 = B_351
      | v1_funct_1(k2_partfun1(A_352,B_351,D_353,C_354))
      | ~ r1_tarski(C_354,A_352)
      | ~ m1_subset_1(D_353,k1_zfmisc_1(k2_zfmisc_1(A_352,B_351)))
      | ~ v1_funct_2(D_353,A_352,B_351)
      | ~ v1_funct_1(D_353) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_969,plain,(
    ! [C_354] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_1(k2_partfun1('#skF_3','#skF_2','#skF_5',C_354))
      | ~ r1_tarski(C_354,'#skF_3')
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_58,c_967])).

tff(c_974,plain,(
    ! [C_354] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_1(k2_partfun1('#skF_3','#skF_2','#skF_5',C_354))
      | ~ r1_tarski(C_354,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_969])).

tff(c_978,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_974])).

tff(c_991,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_978,c_82])).

tff(c_995,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_991])).

tff(c_997,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_974])).

tff(c_64,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_720,plain,(
    ! [B_317,A_318] :
      ( r1_subset_1(B_317,A_318)
      | ~ r1_subset_1(A_318,B_317)
      | v1_xboole_0(B_317)
      | v1_xboole_0(A_318) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_722,plain,
    ( r1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_720])).

tff(c_725,plain,(
    r1_subset_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_68,c_722])).

tff(c_740,plain,(
    ! [A_322,B_323] :
      ( r1_xboole_0(A_322,B_323)
      | ~ r1_subset_1(A_322,B_323)
      | v1_xboole_0(B_323)
      | v1_xboole_0(A_322) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_14,plain,(
    ! [A_137,B_138] :
      ( k3_xboole_0(A_137,B_138) = k1_xboole_0
      | ~ r1_xboole_0(A_137,B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_915,plain,(
    ! [A_342,B_343] :
      ( k3_xboole_0(A_342,B_343) = k1_xboole_0
      | ~ r1_subset_1(A_342,B_343)
      | v1_xboole_0(B_343)
      | v1_xboole_0(A_342) ) ),
    inference(resolution,[status(thm)],[c_740,c_14])).

tff(c_921,plain,
    ( k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_725,c_915])).

tff(c_928,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_72,c_921])).

tff(c_93,plain,(
    ! [B_219,A_220] : k3_xboole_0(B_219,A_220) = k3_xboole_0(A_220,B_219) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_34,plain,(
    ! [A_152,B_153] : r1_tarski(k3_xboole_0(A_152,B_153),A_152) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_108,plain,(
    ! [B_219,A_220] : r1_tarski(k3_xboole_0(B_219,A_220),A_220) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_34])).

tff(c_935,plain,(
    r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_928,c_108])).

tff(c_4,plain,(
    ! [B_6,A_5] : k3_xboole_0(B_6,A_5) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_755,plain,(
    ! [A_326,B_327,C_328] :
      ( k9_subset_1(A_326,B_327,C_328) = k3_xboole_0(B_327,C_328)
      | ~ m1_subset_1(C_328,k1_zfmisc_1(A_326)) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_766,plain,(
    ! [B_327] : k9_subset_1('#skF_1',B_327,'#skF_4') = k3_xboole_0(B_327,'#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_755])).

tff(c_172,plain,(
    ! [B_234,A_235] :
      ( r1_subset_1(B_234,A_235)
      | ~ r1_subset_1(A_235,B_234)
      | v1_xboole_0(B_234)
      | v1_xboole_0(A_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_174,plain,
    ( r1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_172])).

tff(c_177,plain,(
    r1_subset_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_68,c_174])).

tff(c_163,plain,(
    ! [A_232,B_233] :
      ( r1_xboole_0(A_232,B_233)
      | ~ r1_subset_1(A_232,B_233)
      | v1_xboole_0(B_233)
      | v1_xboole_0(A_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_339,plain,(
    ! [A_250,B_251] :
      ( k3_xboole_0(A_250,B_251) = k1_xboole_0
      | ~ r1_subset_1(A_250,B_251)
      | v1_xboole_0(B_251)
      | v1_xboole_0(A_250) ) ),
    inference(resolution,[status(thm)],[c_163,c_14])).

tff(c_342,plain,
    ( k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_177,c_339])).

tff(c_348,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_72,c_342])).

tff(c_355,plain,(
    r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_108])).

tff(c_391,plain,(
    ! [B_261,A_262,D_263,C_264] :
      ( k1_xboole_0 = B_261
      | v1_funct_1(k2_partfun1(A_262,B_261,D_263,C_264))
      | ~ r1_tarski(C_264,A_262)
      | ~ m1_subset_1(D_263,k1_zfmisc_1(k2_zfmisc_1(A_262,B_261)))
      | ~ v1_funct_2(D_263,A_262,B_261)
      | ~ v1_funct_1(D_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_393,plain,(
    ! [C_264] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_1(k2_partfun1('#skF_3','#skF_2','#skF_5',C_264))
      | ~ r1_tarski(C_264,'#skF_3')
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_58,c_391])).

tff(c_398,plain,(
    ! [C_264] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_1(k2_partfun1('#skF_3','#skF_2','#skF_5',C_264))
      | ~ r1_tarski(C_264,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_393])).

tff(c_402,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_398])).

tff(c_415,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_82])).

tff(c_419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_415])).

tff(c_421,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_398])).

tff(c_471,plain,(
    ! [B_282,A_283,D_284,C_285] :
      ( k1_xboole_0 = B_282
      | m1_subset_1(k2_partfun1(A_283,B_282,D_284,C_285),k1_zfmisc_1(k2_zfmisc_1(C_285,B_282)))
      | ~ r1_tarski(C_285,A_283)
      | ~ m1_subset_1(D_284,k1_zfmisc_1(k2_zfmisc_1(A_283,B_282)))
      | ~ v1_funct_2(D_284,A_283,B_282)
      | ~ v1_funct_1(D_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( v1_xboole_0(C_4)
      | ~ m1_subset_1(C_4,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_500,plain,(
    ! [A_286,B_287,D_288,C_289] :
      ( v1_xboole_0(k2_partfun1(A_286,B_287,D_288,C_289))
      | ~ v1_xboole_0(C_289)
      | k1_xboole_0 = B_287
      | ~ r1_tarski(C_289,A_286)
      | ~ m1_subset_1(D_288,k1_zfmisc_1(k2_zfmisc_1(A_286,B_287)))
      | ~ v1_funct_2(D_288,A_286,B_287)
      | ~ v1_funct_1(D_288) ) ),
    inference(resolution,[status(thm)],[c_471,c_2])).

tff(c_506,plain,(
    ! [C_289] :
      ( v1_xboole_0(k2_partfun1('#skF_3','#skF_2','#skF_5',C_289))
      | ~ v1_xboole_0(C_289)
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(C_289,'#skF_3')
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_58,c_500])).

tff(c_513,plain,(
    ! [C_289] :
      ( v1_xboole_0(k2_partfun1('#skF_3','#skF_2','#skF_5',C_289))
      | ~ v1_xboole_0(C_289)
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(C_289,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_506])).

tff(c_519,plain,(
    ! [C_290] :
      ( v1_xboole_0(k2_partfun1('#skF_3','#skF_2','#skF_5',C_290))
      | ~ v1_xboole_0(C_290)
      | ~ r1_tarski(C_290,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_421,c_513])).

tff(c_48,plain,(
    ! [A_158] :
      ( k1_xboole_0 = A_158
      | ~ v1_xboole_0(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_548,plain,(
    ! [C_298] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',C_298) = k1_xboole_0
      | ~ v1_xboole_0(C_298)
      | ~ r1_tarski(C_298,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_519,c_48])).

tff(c_551,plain,
    ( k2_partfun1('#skF_3','#skF_2','#skF_5',k1_xboole_0) = k1_xboole_0
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_355,c_548])).

tff(c_562,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_551])).

tff(c_183,plain,(
    ! [A_236,B_237,C_238] :
      ( k9_subset_1(A_236,B_237,C_238) = k3_xboole_0(B_237,C_238)
      | ~ m1_subset_1(C_238,k1_zfmisc_1(A_236)) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_194,plain,(
    ! [B_237] : k9_subset_1('#skF_1',B_237,'#skF_4') = k3_xboole_0(B_237,'#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_183])).

tff(c_50,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_132,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_196,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_194,c_132])).

tff(c_197,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_4','#skF_3')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_196])).

tff(c_390,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k1_xboole_0) != k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_348,c_197])).

tff(c_565,plain,(
    k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_562,c_390])).

tff(c_358,plain,(
    r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_34])).

tff(c_56,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_54,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_508,plain,(
    ! [C_289] :
      ( v1_xboole_0(k2_partfun1('#skF_4','#skF_2','#skF_6',C_289))
      | ~ v1_xboole_0(C_289)
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(C_289,'#skF_4')
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_52,c_500])).

tff(c_517,plain,(
    ! [C_289] :
      ( v1_xboole_0(k2_partfun1('#skF_4','#skF_2','#skF_6',C_289))
      | ~ v1_xboole_0(C_289)
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(C_289,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_508])).

tff(c_543,plain,(
    ! [C_297] :
      ( v1_xboole_0(k2_partfun1('#skF_4','#skF_2','#skF_6',C_297))
      | ~ v1_xboole_0(C_297)
      | ~ r1_tarski(C_297,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_421,c_517])).

tff(c_681,plain,(
    ! [C_310] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',C_310) = k1_xboole_0
      | ~ v1_xboole_0(C_310)
      | ~ r1_tarski(C_310,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_543,c_48])).

tff(c_684,plain,
    ( k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0) = k1_xboole_0
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_358,c_681])).

tff(c_695,plain,(
    k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_684])).

tff(c_697,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_565,c_695])).

tff(c_699,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_768,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_766,c_766,c_699])).

tff(c_769,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_4','#skF_3')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_768])).

tff(c_961,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k1_xboole_0) = k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_928,c_928,c_769])).

tff(c_1057,plain,(
    ! [B_372,A_373,D_374,C_375] :
      ( k1_xboole_0 = B_372
      | m1_subset_1(k2_partfun1(A_373,B_372,D_374,C_375),k1_zfmisc_1(k2_zfmisc_1(C_375,B_372)))
      | ~ r1_tarski(C_375,A_373)
      | ~ m1_subset_1(D_374,k1_zfmisc_1(k2_zfmisc_1(A_373,B_372)))
      | ~ v1_funct_2(D_374,A_373,B_372)
      | ~ v1_funct_1(D_374) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_1080,plain,
    ( k1_xboole_0 = '#skF_2'
    | m1_subset_1(k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2')))
    | ~ r1_tarski(k1_xboole_0,'#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_961,c_1057])).

tff(c_1090,plain,
    ( k1_xboole_0 = '#skF_2'
    | m1_subset_1(k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_935,c_1080])).

tff(c_1091,plain,(
    m1_subset_1(k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_997,c_1090])).

tff(c_1108,plain,
    ( v1_xboole_0(k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1091,c_2])).

tff(c_1130,plain,(
    v1_xboole_0(k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1108])).

tff(c_1134,plain,(
    k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1130,c_48])).

tff(c_1139,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1134,c_961])).

tff(c_767,plain,(
    ! [B_327] : k9_subset_1('#skF_1',B_327,'#skF_3') = k3_xboole_0(B_327,'#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_755])).

tff(c_806,plain,(
    ! [A_333,C_334,B_335] :
      ( k9_subset_1(A_333,C_334,B_335) = k9_subset_1(A_333,B_335,C_334)
      | ~ m1_subset_1(C_334,k1_zfmisc_1(A_333)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_814,plain,(
    ! [B_335] : k9_subset_1('#skF_1',B_335,'#skF_3') = k9_subset_1('#skF_1','#skF_3',B_335) ),
    inference(resolution,[status(thm)],[c_70,c_806])).

tff(c_822,plain,(
    ! [B_335] : k9_subset_1('#skF_1','#skF_3',B_335) = k3_xboole_0(B_335,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_767,c_814])).

tff(c_1195,plain,(
    ! [C_381,E_379,F_376,B_378,D_380,A_377] :
      ( v1_funct_1(k1_tmap_1(A_377,B_378,C_381,D_380,E_379,F_376))
      | ~ m1_subset_1(F_376,k1_zfmisc_1(k2_zfmisc_1(D_380,B_378)))
      | ~ v1_funct_2(F_376,D_380,B_378)
      | ~ v1_funct_1(F_376)
      | ~ m1_subset_1(E_379,k1_zfmisc_1(k2_zfmisc_1(C_381,B_378)))
      | ~ v1_funct_2(E_379,C_381,B_378)
      | ~ v1_funct_1(E_379)
      | ~ m1_subset_1(D_380,k1_zfmisc_1(A_377))
      | v1_xboole_0(D_380)
      | ~ m1_subset_1(C_381,k1_zfmisc_1(A_377))
      | v1_xboole_0(C_381)
      | v1_xboole_0(B_378)
      | v1_xboole_0(A_377) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1205,plain,(
    ! [A_377,C_381,E_379] :
      ( v1_funct_1(k1_tmap_1(A_377,'#skF_2',C_381,'#skF_4',E_379,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_379,k1_zfmisc_1(k2_zfmisc_1(C_381,'#skF_2')))
      | ~ v1_funct_2(E_379,C_381,'#skF_2')
      | ~ v1_funct_1(E_379)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_377))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_381,k1_zfmisc_1(A_377))
      | v1_xboole_0(C_381)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_377) ) ),
    inference(resolution,[status(thm)],[c_52,c_1195])).

tff(c_1218,plain,(
    ! [A_377,C_381,E_379] :
      ( v1_funct_1(k1_tmap_1(A_377,'#skF_2',C_381,'#skF_4',E_379,'#skF_6'))
      | ~ m1_subset_1(E_379,k1_zfmisc_1(k2_zfmisc_1(C_381,'#skF_2')))
      | ~ v1_funct_2(E_379,C_381,'#skF_2')
      | ~ v1_funct_1(E_379)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_377))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_381,k1_zfmisc_1(A_377))
      | v1_xboole_0(C_381)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_377) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_1205])).

tff(c_1398,plain,(
    ! [A_409,C_410,E_411] :
      ( v1_funct_1(k1_tmap_1(A_409,'#skF_2',C_410,'#skF_4',E_411,'#skF_6'))
      | ~ m1_subset_1(E_411,k1_zfmisc_1(k2_zfmisc_1(C_410,'#skF_2')))
      | ~ v1_funct_2(E_411,C_410,'#skF_2')
      | ~ v1_funct_1(E_411)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_409))
      | ~ m1_subset_1(C_410,k1_zfmisc_1(A_409))
      | v1_xboole_0(C_410)
      | v1_xboole_0(A_409) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_1218])).

tff(c_1411,plain,(
    ! [A_409] :
      ( v1_funct_1(k1_tmap_1(A_409,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_409))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_409))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_409) ) ),
    inference(resolution,[status(thm)],[c_58,c_1398])).

tff(c_1426,plain,(
    ! [A_409] :
      ( v1_funct_1(k1_tmap_1(A_409,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_409))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_409))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_409) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1411])).

tff(c_1452,plain,(
    ! [A_419] :
      ( v1_funct_1(k1_tmap_1(A_419,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_419))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_419))
      | v1_xboole_0(A_419) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1426])).

tff(c_1455,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_1452])).

tff(c_1458,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1455])).

tff(c_1459,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1458])).

tff(c_20,plain,(
    ! [B_140,E_143,D_142,A_139,C_141,F_144] :
      ( v1_funct_2(k1_tmap_1(A_139,B_140,C_141,D_142,E_143,F_144),k4_subset_1(A_139,C_141,D_142),B_140)
      | ~ m1_subset_1(F_144,k1_zfmisc_1(k2_zfmisc_1(D_142,B_140)))
      | ~ v1_funct_2(F_144,D_142,B_140)
      | ~ v1_funct_1(F_144)
      | ~ m1_subset_1(E_143,k1_zfmisc_1(k2_zfmisc_1(C_141,B_140)))
      | ~ v1_funct_2(E_143,C_141,B_140)
      | ~ v1_funct_1(E_143)
      | ~ m1_subset_1(D_142,k1_zfmisc_1(A_139))
      | v1_xboole_0(D_142)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(A_139))
      | v1_xboole_0(C_141)
      | v1_xboole_0(B_140)
      | v1_xboole_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_18,plain,(
    ! [B_140,E_143,D_142,A_139,C_141,F_144] :
      ( m1_subset_1(k1_tmap_1(A_139,B_140,C_141,D_142,E_143,F_144),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_139,C_141,D_142),B_140)))
      | ~ m1_subset_1(F_144,k1_zfmisc_1(k2_zfmisc_1(D_142,B_140)))
      | ~ v1_funct_2(F_144,D_142,B_140)
      | ~ v1_funct_1(F_144)
      | ~ m1_subset_1(E_143,k1_zfmisc_1(k2_zfmisc_1(C_141,B_140)))
      | ~ v1_funct_2(E_143,C_141,B_140)
      | ~ v1_funct_1(E_143)
      | ~ m1_subset_1(D_142,k1_zfmisc_1(A_139))
      | v1_xboole_0(D_142)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(A_139))
      | v1_xboole_0(C_141)
      | v1_xboole_0(B_140)
      | v1_xboole_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1526,plain,(
    ! [C_432,B_429,F_431,A_430,E_427,D_428] :
      ( k2_partfun1(k4_subset_1(A_430,C_432,D_428),B_429,k1_tmap_1(A_430,B_429,C_432,D_428,E_427,F_431),D_428) = F_431
      | ~ m1_subset_1(k1_tmap_1(A_430,B_429,C_432,D_428,E_427,F_431),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_430,C_432,D_428),B_429)))
      | ~ v1_funct_2(k1_tmap_1(A_430,B_429,C_432,D_428,E_427,F_431),k4_subset_1(A_430,C_432,D_428),B_429)
      | ~ v1_funct_1(k1_tmap_1(A_430,B_429,C_432,D_428,E_427,F_431))
      | k2_partfun1(D_428,B_429,F_431,k9_subset_1(A_430,C_432,D_428)) != k2_partfun1(C_432,B_429,E_427,k9_subset_1(A_430,C_432,D_428))
      | ~ m1_subset_1(F_431,k1_zfmisc_1(k2_zfmisc_1(D_428,B_429)))
      | ~ v1_funct_2(F_431,D_428,B_429)
      | ~ v1_funct_1(F_431)
      | ~ m1_subset_1(E_427,k1_zfmisc_1(k2_zfmisc_1(C_432,B_429)))
      | ~ v1_funct_2(E_427,C_432,B_429)
      | ~ v1_funct_1(E_427)
      | ~ m1_subset_1(D_428,k1_zfmisc_1(A_430))
      | v1_xboole_0(D_428)
      | ~ m1_subset_1(C_432,k1_zfmisc_1(A_430))
      | v1_xboole_0(C_432)
      | v1_xboole_0(B_429)
      | v1_xboole_0(A_430) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_4524,plain,(
    ! [B_736,C_739,F_734,E_737,D_738,A_735] :
      ( k2_partfun1(k4_subset_1(A_735,C_739,D_738),B_736,k1_tmap_1(A_735,B_736,C_739,D_738,E_737,F_734),D_738) = F_734
      | ~ v1_funct_2(k1_tmap_1(A_735,B_736,C_739,D_738,E_737,F_734),k4_subset_1(A_735,C_739,D_738),B_736)
      | ~ v1_funct_1(k1_tmap_1(A_735,B_736,C_739,D_738,E_737,F_734))
      | k2_partfun1(D_738,B_736,F_734,k9_subset_1(A_735,C_739,D_738)) != k2_partfun1(C_739,B_736,E_737,k9_subset_1(A_735,C_739,D_738))
      | ~ m1_subset_1(F_734,k1_zfmisc_1(k2_zfmisc_1(D_738,B_736)))
      | ~ v1_funct_2(F_734,D_738,B_736)
      | ~ v1_funct_1(F_734)
      | ~ m1_subset_1(E_737,k1_zfmisc_1(k2_zfmisc_1(C_739,B_736)))
      | ~ v1_funct_2(E_737,C_739,B_736)
      | ~ v1_funct_1(E_737)
      | ~ m1_subset_1(D_738,k1_zfmisc_1(A_735))
      | v1_xboole_0(D_738)
      | ~ m1_subset_1(C_739,k1_zfmisc_1(A_735))
      | v1_xboole_0(C_739)
      | v1_xboole_0(B_736)
      | v1_xboole_0(A_735) ) ),
    inference(resolution,[status(thm)],[c_18,c_1526])).

tff(c_14480,plain,(
    ! [B_1075,A_1074,F_1073,E_1076,D_1077,C_1078] :
      ( k2_partfun1(k4_subset_1(A_1074,C_1078,D_1077),B_1075,k1_tmap_1(A_1074,B_1075,C_1078,D_1077,E_1076,F_1073),D_1077) = F_1073
      | ~ v1_funct_1(k1_tmap_1(A_1074,B_1075,C_1078,D_1077,E_1076,F_1073))
      | k2_partfun1(D_1077,B_1075,F_1073,k9_subset_1(A_1074,C_1078,D_1077)) != k2_partfun1(C_1078,B_1075,E_1076,k9_subset_1(A_1074,C_1078,D_1077))
      | ~ m1_subset_1(F_1073,k1_zfmisc_1(k2_zfmisc_1(D_1077,B_1075)))
      | ~ v1_funct_2(F_1073,D_1077,B_1075)
      | ~ v1_funct_1(F_1073)
      | ~ m1_subset_1(E_1076,k1_zfmisc_1(k2_zfmisc_1(C_1078,B_1075)))
      | ~ v1_funct_2(E_1076,C_1078,B_1075)
      | ~ v1_funct_1(E_1076)
      | ~ m1_subset_1(D_1077,k1_zfmisc_1(A_1074))
      | v1_xboole_0(D_1077)
      | ~ m1_subset_1(C_1078,k1_zfmisc_1(A_1074))
      | v1_xboole_0(C_1078)
      | v1_xboole_0(B_1075)
      | v1_xboole_0(A_1074) ) ),
    inference(resolution,[status(thm)],[c_20,c_4524])).

tff(c_14498,plain,(
    ! [A_1074,C_1078,E_1076] :
      ( k2_partfun1(k4_subset_1(A_1074,C_1078,'#skF_4'),'#skF_2',k1_tmap_1(A_1074,'#skF_2',C_1078,'#skF_4',E_1076,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1074,'#skF_2',C_1078,'#skF_4',E_1076,'#skF_6'))
      | k2_partfun1(C_1078,'#skF_2',E_1076,k9_subset_1(A_1074,C_1078,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_1074,C_1078,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1076,k1_zfmisc_1(k2_zfmisc_1(C_1078,'#skF_2')))
      | ~ v1_funct_2(E_1076,C_1078,'#skF_2')
      | ~ v1_funct_1(E_1076)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1074))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1078,k1_zfmisc_1(A_1074))
      | v1_xboole_0(C_1078)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1074) ) ),
    inference(resolution,[status(thm)],[c_52,c_14480])).

tff(c_14524,plain,(
    ! [A_1074,C_1078,E_1076] :
      ( k2_partfun1(k4_subset_1(A_1074,C_1078,'#skF_4'),'#skF_2',k1_tmap_1(A_1074,'#skF_2',C_1078,'#skF_4',E_1076,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1074,'#skF_2',C_1078,'#skF_4',E_1076,'#skF_6'))
      | k2_partfun1(C_1078,'#skF_2',E_1076,k9_subset_1(A_1074,C_1078,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_1074,C_1078,'#skF_4'))
      | ~ m1_subset_1(E_1076,k1_zfmisc_1(k2_zfmisc_1(C_1078,'#skF_2')))
      | ~ v1_funct_2(E_1076,C_1078,'#skF_2')
      | ~ v1_funct_1(E_1076)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1074))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1078,k1_zfmisc_1(A_1074))
      | v1_xboole_0(C_1078)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1074) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_14498])).

tff(c_15730,plain,(
    ! [A_1114,C_1115,E_1116] :
      ( k2_partfun1(k4_subset_1(A_1114,C_1115,'#skF_4'),'#skF_2',k1_tmap_1(A_1114,'#skF_2',C_1115,'#skF_4',E_1116,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1114,'#skF_2',C_1115,'#skF_4',E_1116,'#skF_6'))
      | k2_partfun1(C_1115,'#skF_2',E_1116,k9_subset_1(A_1114,C_1115,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_1114,C_1115,'#skF_4'))
      | ~ m1_subset_1(E_1116,k1_zfmisc_1(k2_zfmisc_1(C_1115,'#skF_2')))
      | ~ v1_funct_2(E_1116,C_1115,'#skF_2')
      | ~ v1_funct_1(E_1116)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1114))
      | ~ m1_subset_1(C_1115,k1_zfmisc_1(A_1114))
      | v1_xboole_0(C_1115)
      | v1_xboole_0(A_1114) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_14524])).

tff(c_15749,plain,(
    ! [A_1114] :
      ( k2_partfun1(k4_subset_1(A_1114,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1114,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1114,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1114,'#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_1114,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1114))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1114))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1114) ) ),
    inference(resolution,[status(thm)],[c_58,c_15730])).

tff(c_15773,plain,(
    ! [A_1114] :
      ( k2_partfun1(k4_subset_1(A_1114,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1114,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1114,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1114,'#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_1114,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1114))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1114))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_15749])).

tff(c_15869,plain,(
    ! [A_1125] :
      ( k2_partfun1(k4_subset_1(A_1125,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1125,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1125,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1125,'#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_1125,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1125))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1125))
      | v1_xboole_0(A_1125) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_15773])).

tff(c_698,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_754,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_698])).

tff(c_15916,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_15869,c_754])).

tff(c_15948,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_1139,c_1134,c_928,c_822,c_928,c_822,c_1459,c_15916])).

tff(c_15950,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_15948])).

tff(c_15951,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_698])).

tff(c_16169,plain,(
    ! [B_1151,A_1152,D_1153,C_1154] :
      ( k1_xboole_0 = B_1151
      | v1_funct_1(k2_partfun1(A_1152,B_1151,D_1153,C_1154))
      | ~ r1_tarski(C_1154,A_1152)
      | ~ m1_subset_1(D_1153,k1_zfmisc_1(k2_zfmisc_1(A_1152,B_1151)))
      | ~ v1_funct_2(D_1153,A_1152,B_1151)
      | ~ v1_funct_1(D_1153) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_16171,plain,(
    ! [C_1154] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_1(k2_partfun1('#skF_3','#skF_2','#skF_5',C_1154))
      | ~ r1_tarski(C_1154,'#skF_3')
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_58,c_16169])).

tff(c_16176,plain,(
    ! [C_1154] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_1(k2_partfun1('#skF_3','#skF_2','#skF_5',C_1154))
      | ~ r1_tarski(C_1154,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_16171])).

tff(c_16180,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_16176])).

tff(c_16193,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16180,c_82])).

tff(c_16197,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_16193])).

tff(c_16199,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_16176])).

tff(c_16113,plain,(
    ! [A_1142,B_1143] :
      ( k3_xboole_0(A_1142,B_1143) = k1_xboole_0
      | ~ r1_subset_1(A_1142,B_1143)
      | v1_xboole_0(B_1143)
      | v1_xboole_0(A_1142) ) ),
    inference(resolution,[status(thm)],[c_740,c_14])).

tff(c_16119,plain,
    ( k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_725,c_16113])).

tff(c_16126,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_72,c_16119])).

tff(c_16133,plain,(
    r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16126,c_108])).

tff(c_15953,plain,(
    ! [A_1126,B_1127,C_1128] :
      ( k9_subset_1(A_1126,B_1127,C_1128) = k3_xboole_0(B_1127,C_1128)
      | ~ m1_subset_1(C_1128,k1_zfmisc_1(A_1126)) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_15964,plain,(
    ! [B_1127] : k9_subset_1('#skF_1',B_1127,'#skF_4') = k3_xboole_0(B_1127,'#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_15953])).

tff(c_15966,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15964,c_15964,c_699])).

tff(c_15967,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_4','#skF_3')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_15966])).

tff(c_16163,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k1_xboole_0) = k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16126,c_16126,c_15967])).

tff(c_16258,plain,(
    ! [B_1171,A_1172,D_1173,C_1174] :
      ( k1_xboole_0 = B_1171
      | m1_subset_1(k2_partfun1(A_1172,B_1171,D_1173,C_1174),k1_zfmisc_1(k2_zfmisc_1(C_1174,B_1171)))
      | ~ r1_tarski(C_1174,A_1172)
      | ~ m1_subset_1(D_1173,k1_zfmisc_1(k2_zfmisc_1(A_1172,B_1171)))
      | ~ v1_funct_2(D_1173,A_1172,B_1171)
      | ~ v1_funct_1(D_1173) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_16281,plain,
    ( k1_xboole_0 = '#skF_2'
    | m1_subset_1(k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2')))
    | ~ r1_tarski(k1_xboole_0,'#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_16163,c_16258])).

tff(c_16294,plain,
    ( k1_xboole_0 = '#skF_2'
    | m1_subset_1(k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_16133,c_16281])).

tff(c_16295,plain,(
    m1_subset_1(k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_16199,c_16294])).

tff(c_16314,plain,
    ( v1_xboole_0(k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16295,c_2])).

tff(c_16336,plain,(
    v1_xboole_0(k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_16314])).

tff(c_16340,plain,(
    k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16336,c_48])).

tff(c_15965,plain,(
    ! [B_1127] : k9_subset_1('#skF_1',B_1127,'#skF_3') = k3_xboole_0(B_1127,'#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_15953])).

tff(c_16004,plain,(
    ! [A_1133,C_1134,B_1135] :
      ( k9_subset_1(A_1133,C_1134,B_1135) = k9_subset_1(A_1133,B_1135,C_1134)
      | ~ m1_subset_1(C_1134,k1_zfmisc_1(A_1133)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16012,plain,(
    ! [B_1135] : k9_subset_1('#skF_1',B_1135,'#skF_3') = k9_subset_1('#skF_1','#skF_3',B_1135) ),
    inference(resolution,[status(thm)],[c_70,c_16004])).

tff(c_16020,plain,(
    ! [B_1135] : k9_subset_1('#skF_1','#skF_3',B_1135) = k3_xboole_0(B_1135,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15965,c_16012])).

tff(c_16345,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16340,c_16163])).

tff(c_16390,plain,(
    ! [C_1181,E_1179,A_1177,F_1176,D_1180,B_1178] :
      ( v1_funct_1(k1_tmap_1(A_1177,B_1178,C_1181,D_1180,E_1179,F_1176))
      | ~ m1_subset_1(F_1176,k1_zfmisc_1(k2_zfmisc_1(D_1180,B_1178)))
      | ~ v1_funct_2(F_1176,D_1180,B_1178)
      | ~ v1_funct_1(F_1176)
      | ~ m1_subset_1(E_1179,k1_zfmisc_1(k2_zfmisc_1(C_1181,B_1178)))
      | ~ v1_funct_2(E_1179,C_1181,B_1178)
      | ~ v1_funct_1(E_1179)
      | ~ m1_subset_1(D_1180,k1_zfmisc_1(A_1177))
      | v1_xboole_0(D_1180)
      | ~ m1_subset_1(C_1181,k1_zfmisc_1(A_1177))
      | v1_xboole_0(C_1181)
      | v1_xboole_0(B_1178)
      | v1_xboole_0(A_1177) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_16398,plain,(
    ! [A_1177,C_1181,E_1179] :
      ( v1_funct_1(k1_tmap_1(A_1177,'#skF_2',C_1181,'#skF_4',E_1179,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1179,k1_zfmisc_1(k2_zfmisc_1(C_1181,'#skF_2')))
      | ~ v1_funct_2(E_1179,C_1181,'#skF_2')
      | ~ v1_funct_1(E_1179)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1177))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1181,k1_zfmisc_1(A_1177))
      | v1_xboole_0(C_1181)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1177) ) ),
    inference(resolution,[status(thm)],[c_52,c_16390])).

tff(c_16407,plain,(
    ! [A_1177,C_1181,E_1179] :
      ( v1_funct_1(k1_tmap_1(A_1177,'#skF_2',C_1181,'#skF_4',E_1179,'#skF_6'))
      | ~ m1_subset_1(E_1179,k1_zfmisc_1(k2_zfmisc_1(C_1181,'#skF_2')))
      | ~ v1_funct_2(E_1179,C_1181,'#skF_2')
      | ~ v1_funct_1(E_1179)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1177))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1181,k1_zfmisc_1(A_1177))
      | v1_xboole_0(C_1181)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1177) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_16398])).

tff(c_16646,plain,(
    ! [A_1219,C_1220,E_1221] :
      ( v1_funct_1(k1_tmap_1(A_1219,'#skF_2',C_1220,'#skF_4',E_1221,'#skF_6'))
      | ~ m1_subset_1(E_1221,k1_zfmisc_1(k2_zfmisc_1(C_1220,'#skF_2')))
      | ~ v1_funct_2(E_1221,C_1220,'#skF_2')
      | ~ v1_funct_1(E_1221)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1219))
      | ~ m1_subset_1(C_1220,k1_zfmisc_1(A_1219))
      | v1_xboole_0(C_1220)
      | v1_xboole_0(A_1219) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_16407])).

tff(c_16659,plain,(
    ! [A_1219] :
      ( v1_funct_1(k1_tmap_1(A_1219,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1219))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1219))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1219) ) ),
    inference(resolution,[status(thm)],[c_58,c_16646])).

tff(c_16674,plain,(
    ! [A_1219] :
      ( v1_funct_1(k1_tmap_1(A_1219,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1219))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1219))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1219) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_16659])).

tff(c_16847,plain,(
    ! [A_1246] :
      ( v1_funct_1(k1_tmap_1(A_1246,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1246))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1246))
      | v1_xboole_0(A_1246) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_16674])).

tff(c_16850,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_16847])).

tff(c_16853,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_16850])).

tff(c_16854,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_16853])).

tff(c_16564,plain,(
    ! [A_1202,F_1201,E_1204,B_1203,C_1206,D_1205] :
      ( m1_subset_1(k1_tmap_1(A_1202,B_1203,C_1206,D_1205,E_1204,F_1201),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1202,C_1206,D_1205),B_1203)))
      | ~ m1_subset_1(F_1201,k1_zfmisc_1(k2_zfmisc_1(D_1205,B_1203)))
      | ~ v1_funct_2(F_1201,D_1205,B_1203)
      | ~ v1_funct_1(F_1201)
      | ~ m1_subset_1(E_1204,k1_zfmisc_1(k2_zfmisc_1(C_1206,B_1203)))
      | ~ v1_funct_2(E_1204,C_1206,B_1203)
      | ~ v1_funct_1(E_1204)
      | ~ m1_subset_1(D_1205,k1_zfmisc_1(A_1202))
      | v1_xboole_0(D_1205)
      | ~ m1_subset_1(C_1206,k1_zfmisc_1(A_1202))
      | v1_xboole_0(C_1206)
      | v1_xboole_0(B_1203)
      | v1_xboole_0(A_1202) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_46,plain,(
    ! [B_155,A_154,D_157,C_156] :
      ( k1_xboole_0 = B_155
      | v1_funct_1(k2_partfun1(A_154,B_155,D_157,C_156))
      | ~ r1_tarski(C_156,A_154)
      | ~ m1_subset_1(D_157,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155)))
      | ~ v1_funct_2(D_157,A_154,B_155)
      | ~ v1_funct_1(D_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_19128,plain,(
    ! [B_1436,C_1442,D_1441,F_1437,A_1439,C_1440,E_1438] :
      ( k1_xboole_0 = B_1436
      | v1_funct_1(k2_partfun1(k4_subset_1(A_1439,C_1442,D_1441),B_1436,k1_tmap_1(A_1439,B_1436,C_1442,D_1441,E_1438,F_1437),C_1440))
      | ~ r1_tarski(C_1440,k4_subset_1(A_1439,C_1442,D_1441))
      | ~ v1_funct_2(k1_tmap_1(A_1439,B_1436,C_1442,D_1441,E_1438,F_1437),k4_subset_1(A_1439,C_1442,D_1441),B_1436)
      | ~ v1_funct_1(k1_tmap_1(A_1439,B_1436,C_1442,D_1441,E_1438,F_1437))
      | ~ m1_subset_1(F_1437,k1_zfmisc_1(k2_zfmisc_1(D_1441,B_1436)))
      | ~ v1_funct_2(F_1437,D_1441,B_1436)
      | ~ v1_funct_1(F_1437)
      | ~ m1_subset_1(E_1438,k1_zfmisc_1(k2_zfmisc_1(C_1442,B_1436)))
      | ~ v1_funct_2(E_1438,C_1442,B_1436)
      | ~ v1_funct_1(E_1438)
      | ~ m1_subset_1(D_1441,k1_zfmisc_1(A_1439))
      | v1_xboole_0(D_1441)
      | ~ m1_subset_1(C_1442,k1_zfmisc_1(A_1439))
      | v1_xboole_0(C_1442)
      | v1_xboole_0(B_1436)
      | v1_xboole_0(A_1439) ) ),
    inference(resolution,[status(thm)],[c_16564,c_46])).

tff(c_15952,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_698])).

tff(c_16823,plain,(
    ! [B_1242,D_1241,G_1240,C_1244,A_1243] :
      ( k1_tmap_1(A_1243,B_1242,C_1244,D_1241,k2_partfun1(k4_subset_1(A_1243,C_1244,D_1241),B_1242,G_1240,C_1244),k2_partfun1(k4_subset_1(A_1243,C_1244,D_1241),B_1242,G_1240,D_1241)) = G_1240
      | ~ m1_subset_1(G_1240,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1243,C_1244,D_1241),B_1242)))
      | ~ v1_funct_2(G_1240,k4_subset_1(A_1243,C_1244,D_1241),B_1242)
      | ~ v1_funct_1(G_1240)
      | k2_partfun1(D_1241,B_1242,k2_partfun1(k4_subset_1(A_1243,C_1244,D_1241),B_1242,G_1240,D_1241),k9_subset_1(A_1243,C_1244,D_1241)) != k2_partfun1(C_1244,B_1242,k2_partfun1(k4_subset_1(A_1243,C_1244,D_1241),B_1242,G_1240,C_1244),k9_subset_1(A_1243,C_1244,D_1241))
      | ~ m1_subset_1(k2_partfun1(k4_subset_1(A_1243,C_1244,D_1241),B_1242,G_1240,D_1241),k1_zfmisc_1(k2_zfmisc_1(D_1241,B_1242)))
      | ~ v1_funct_2(k2_partfun1(k4_subset_1(A_1243,C_1244,D_1241),B_1242,G_1240,D_1241),D_1241,B_1242)
      | ~ v1_funct_1(k2_partfun1(k4_subset_1(A_1243,C_1244,D_1241),B_1242,G_1240,D_1241))
      | ~ m1_subset_1(k2_partfun1(k4_subset_1(A_1243,C_1244,D_1241),B_1242,G_1240,C_1244),k1_zfmisc_1(k2_zfmisc_1(C_1244,B_1242)))
      | ~ v1_funct_2(k2_partfun1(k4_subset_1(A_1243,C_1244,D_1241),B_1242,G_1240,C_1244),C_1244,B_1242)
      | ~ v1_funct_1(k2_partfun1(k4_subset_1(A_1243,C_1244,D_1241),B_1242,G_1240,C_1244))
      | ~ m1_subset_1(D_1241,k1_zfmisc_1(A_1243))
      | v1_xboole_0(D_1241)
      | ~ m1_subset_1(C_1244,k1_zfmisc_1(A_1243))
      | v1_xboole_0(C_1244)
      | v1_xboole_0(B_1242)
      | v1_xboole_0(A_1243) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_16828,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_15952,c_16823])).

tff(c_16831,plain,
    ( k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_6') = k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')))
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k2_partfun1('#skF_3','#skF_2',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_xboole_0) != k1_xboole_0
    | ~ m1_subset_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'))
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_56,c_15952,c_54,c_15952,c_52,c_16340,c_16126,c_16020,c_16126,c_16020,c_15952,c_15952,c_16828])).

tff(c_16832,plain,
    ( k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_6') = k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')))
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k2_partfun1('#skF_3','#skF_2',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_xboole_0) != k1_xboole_0
    | ~ m1_subset_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_74,c_72,c_68,c_16831])).

tff(c_17658,plain,
    ( k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_6') = k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')))
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | k2_partfun1('#skF_3','#skF_2',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_xboole_0) != k1_xboole_0
    | ~ m1_subset_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16854,c_16832])).

tff(c_17659,plain,(
    ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_17658])).

tff(c_19131,plain,
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
    inference(resolution,[status(thm)],[c_19128,c_17659])).

tff(c_19137,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_3',k4_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_62,c_60,c_58,c_56,c_54,c_52,c_16854,c_19131])).

tff(c_19138,plain,
    ( ~ r1_tarski('#skF_3',k4_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_74,c_72,c_68,c_16199,c_19137])).

tff(c_19178,plain,(
    ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_19138])).

tff(c_19181,plain,
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
    inference(resolution,[status(thm)],[c_20,c_19178])).

tff(c_19184,plain,
    ( v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_62,c_60,c_58,c_56,c_54,c_52,c_19181])).

tff(c_19186,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_74,c_72,c_68,c_19184])).

tff(c_19188,plain,(
    v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_19138])).

tff(c_16612,plain,(
    ! [C_1214,B_1211,F_1213,A_1212,E_1209,D_1210] :
      ( k2_partfun1(k4_subset_1(A_1212,C_1214,D_1210),B_1211,k1_tmap_1(A_1212,B_1211,C_1214,D_1210,E_1209,F_1213),C_1214) = E_1209
      | ~ m1_subset_1(k1_tmap_1(A_1212,B_1211,C_1214,D_1210,E_1209,F_1213),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1212,C_1214,D_1210),B_1211)))
      | ~ v1_funct_2(k1_tmap_1(A_1212,B_1211,C_1214,D_1210,E_1209,F_1213),k4_subset_1(A_1212,C_1214,D_1210),B_1211)
      | ~ v1_funct_1(k1_tmap_1(A_1212,B_1211,C_1214,D_1210,E_1209,F_1213))
      | k2_partfun1(D_1210,B_1211,F_1213,k9_subset_1(A_1212,C_1214,D_1210)) != k2_partfun1(C_1214,B_1211,E_1209,k9_subset_1(A_1212,C_1214,D_1210))
      | ~ m1_subset_1(F_1213,k1_zfmisc_1(k2_zfmisc_1(D_1210,B_1211)))
      | ~ v1_funct_2(F_1213,D_1210,B_1211)
      | ~ v1_funct_1(F_1213)
      | ~ m1_subset_1(E_1209,k1_zfmisc_1(k2_zfmisc_1(C_1214,B_1211)))
      | ~ v1_funct_2(E_1209,C_1214,B_1211)
      | ~ v1_funct_1(E_1209)
      | ~ m1_subset_1(D_1210,k1_zfmisc_1(A_1212))
      | v1_xboole_0(D_1210)
      | ~ m1_subset_1(C_1214,k1_zfmisc_1(A_1212))
      | v1_xboole_0(C_1214)
      | v1_xboole_0(B_1211)
      | v1_xboole_0(A_1212) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_19719,plain,(
    ! [D_1503,A_1500,B_1501,E_1502,F_1499,C_1504] :
      ( k2_partfun1(k4_subset_1(A_1500,C_1504,D_1503),B_1501,k1_tmap_1(A_1500,B_1501,C_1504,D_1503,E_1502,F_1499),C_1504) = E_1502
      | ~ v1_funct_2(k1_tmap_1(A_1500,B_1501,C_1504,D_1503,E_1502,F_1499),k4_subset_1(A_1500,C_1504,D_1503),B_1501)
      | ~ v1_funct_1(k1_tmap_1(A_1500,B_1501,C_1504,D_1503,E_1502,F_1499))
      | k2_partfun1(D_1503,B_1501,F_1499,k9_subset_1(A_1500,C_1504,D_1503)) != k2_partfun1(C_1504,B_1501,E_1502,k9_subset_1(A_1500,C_1504,D_1503))
      | ~ m1_subset_1(F_1499,k1_zfmisc_1(k2_zfmisc_1(D_1503,B_1501)))
      | ~ v1_funct_2(F_1499,D_1503,B_1501)
      | ~ v1_funct_1(F_1499)
      | ~ m1_subset_1(E_1502,k1_zfmisc_1(k2_zfmisc_1(C_1504,B_1501)))
      | ~ v1_funct_2(E_1502,C_1504,B_1501)
      | ~ v1_funct_1(E_1502)
      | ~ m1_subset_1(D_1503,k1_zfmisc_1(A_1500))
      | v1_xboole_0(D_1503)
      | ~ m1_subset_1(C_1504,k1_zfmisc_1(A_1500))
      | v1_xboole_0(C_1504)
      | v1_xboole_0(B_1501)
      | v1_xboole_0(A_1500) ) ),
    inference(resolution,[status(thm)],[c_18,c_16612])).

tff(c_19721,plain,
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
    inference(resolution,[status(thm)],[c_19188,c_19719])).

tff(c_19726,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_62,c_60,c_58,c_56,c_54,c_52,c_16340,c_16126,c_16020,c_16345,c_16126,c_16020,c_16854,c_19721])).

tff(c_19728,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_74,c_72,c_68,c_15951,c_19726])).

%------------------------------------------------------------------------------
