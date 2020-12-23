%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1699+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:15 EST 2020

% Result     : Theorem 4.74s
% Output     : CNFRefutation 4.74s
% Verified   : 
% Statistics : Number of formulae       :  121 (10182 expanded)
%              Number of leaves         :   26 (3870 expanded)
%              Depth                    :   21
%              Number of atoms          :  650 (71378 expanded)
%              Number of equality atoms :   65 (6761 expanded)
%              Maximal formula depth    :   26 (   8 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > v1_funct_2 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(r1_funct_2,type,(
    r1_funct_2: ( $i * $i * $i * $i * $i * $i ) > $o )).

tff(k1_tmap_1,type,(
    k1_tmap_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_176,negated_conjecture,(
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
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,C,B)
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,B))) )
                       => ! [F] :
                            ( ( v1_funct_1(F)
                              & v1_funct_2(F,D,B)
                              & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(D,B))) )
                           => ( k2_partfun1(C,B,E,k9_subset_1(A,C,D)) = k2_partfun1(D,B,F,k9_subset_1(A,C,D))
                             => r1_funct_2(k4_subset_1(A,C,D),B,k4_subset_1(A,D,C),B,k1_tmap_1(A,B,C,D,E,F),k1_tmap_1(A,B,D,C,F,E)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_tmap_1)).

tff(f_116,axiom,(
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

tff(f_30,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k4_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_82,axiom,(
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

tff(f_138,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(B)
        & ~ v1_xboole_0(D)
        & v1_funct_1(E)
        & v1_funct_2(E,A,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,C,D)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( r1_funct_2(A,B,C,D,E,F)
      <=> E = F ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_30,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_28,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_26,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_36,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_34,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_240,plain,(
    ! [E_234,F_235,A_233,B_232,D_237,C_236] :
      ( v1_funct_1(k1_tmap_1(A_233,B_232,C_236,D_237,E_234,F_235))
      | ~ m1_subset_1(F_235,k1_zfmisc_1(k2_zfmisc_1(D_237,B_232)))
      | ~ v1_funct_2(F_235,D_237,B_232)
      | ~ v1_funct_1(F_235)
      | ~ m1_subset_1(E_234,k1_zfmisc_1(k2_zfmisc_1(C_236,B_232)))
      | ~ v1_funct_2(E_234,C_236,B_232)
      | ~ v1_funct_1(E_234)
      | ~ m1_subset_1(D_237,k1_zfmisc_1(A_233))
      | v1_xboole_0(D_237)
      | ~ m1_subset_1(C_236,k1_zfmisc_1(A_233))
      | v1_xboole_0(C_236)
      | v1_xboole_0(B_232)
      | v1_xboole_0(A_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_244,plain,(
    ! [A_233,C_236,E_234] :
      ( v1_funct_1(k1_tmap_1(A_233,'#skF_2',C_236,'#skF_3',E_234,'#skF_5'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_234,k1_zfmisc_1(k2_zfmisc_1(C_236,'#skF_2')))
      | ~ v1_funct_2(E_234,C_236,'#skF_2')
      | ~ v1_funct_1(E_234)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_233))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(C_236,k1_zfmisc_1(A_233))
      | v1_xboole_0(C_236)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_233) ) ),
    inference(resolution,[status(thm)],[c_32,c_240])).

tff(c_251,plain,(
    ! [A_233,C_236,E_234] :
      ( v1_funct_1(k1_tmap_1(A_233,'#skF_2',C_236,'#skF_3',E_234,'#skF_5'))
      | ~ m1_subset_1(E_234,k1_zfmisc_1(k2_zfmisc_1(C_236,'#skF_2')))
      | ~ v1_funct_2(E_234,C_236,'#skF_2')
      | ~ v1_funct_1(E_234)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_233))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(C_236,k1_zfmisc_1(A_233))
      | v1_xboole_0(C_236)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_233) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_244])).

tff(c_288,plain,(
    ! [A_249,C_250,E_251] :
      ( v1_funct_1(k1_tmap_1(A_249,'#skF_2',C_250,'#skF_3',E_251,'#skF_5'))
      | ~ m1_subset_1(E_251,k1_zfmisc_1(k2_zfmisc_1(C_250,'#skF_2')))
      | ~ v1_funct_2(E_251,C_250,'#skF_2')
      | ~ v1_funct_1(E_251)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_249))
      | ~ m1_subset_1(C_250,k1_zfmisc_1(A_249))
      | v1_xboole_0(C_250)
      | v1_xboole_0(A_249) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_251])).

tff(c_290,plain,(
    ! [A_249] :
      ( v1_funct_1(k1_tmap_1(A_249,'#skF_2','#skF_4','#skF_3','#skF_6','#skF_5'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_249))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_249))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_249) ) ),
    inference(resolution,[status(thm)],[c_26,c_288])).

tff(c_295,plain,(
    ! [A_249] :
      ( v1_funct_1(k1_tmap_1(A_249,'#skF_2','#skF_4','#skF_3','#skF_6','#skF_5'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_249))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_249))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_249) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_290])).

tff(c_308,plain,(
    ! [A_253] :
      ( v1_funct_1(k1_tmap_1(A_253,'#skF_2','#skF_4','#skF_3','#skF_6','#skF_5'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_253))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_253))
      | v1_xboole_0(A_253) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_295])).

tff(c_311,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6','#skF_5'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_308])).

tff(c_314,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6','#skF_5'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_311])).

tff(c_315,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_314])).

tff(c_145,plain,(
    ! [A_210,C_211,B_212] :
      ( k4_subset_1(A_210,C_211,B_212) = k4_subset_1(A_210,B_212,C_211)
      | ~ m1_subset_1(C_211,k1_zfmisc_1(A_210))
      | ~ m1_subset_1(B_212,k1_zfmisc_1(A_210)) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_158,plain,(
    ! [B_213] :
      ( k4_subset_1('#skF_1',B_213,'#skF_3') = k4_subset_1('#skF_1','#skF_3',B_213)
      | ~ m1_subset_1(B_213,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_42,c_145])).

tff(c_167,plain,(
    k4_subset_1('#skF_1','#skF_3','#skF_4') = k4_subset_1('#skF_1','#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_158])).

tff(c_317,plain,(
    ! [A_258,F_260,E_259,C_261,D_262,B_257] :
      ( m1_subset_1(k1_tmap_1(A_258,B_257,C_261,D_262,E_259,F_260),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_258,C_261,D_262),B_257)))
      | ~ m1_subset_1(F_260,k1_zfmisc_1(k2_zfmisc_1(D_262,B_257)))
      | ~ v1_funct_2(F_260,D_262,B_257)
      | ~ v1_funct_1(F_260)
      | ~ m1_subset_1(E_259,k1_zfmisc_1(k2_zfmisc_1(C_261,B_257)))
      | ~ v1_funct_2(E_259,C_261,B_257)
      | ~ v1_funct_1(E_259)
      | ~ m1_subset_1(D_262,k1_zfmisc_1(A_258))
      | v1_xboole_0(D_262)
      | ~ m1_subset_1(C_261,k1_zfmisc_1(A_258))
      | v1_xboole_0(C_261)
      | v1_xboole_0(B_257)
      | v1_xboole_0(A_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_334,plain,(
    ! [B_257,E_259,F_260] :
      ( m1_subset_1(k1_tmap_1('#skF_1',B_257,'#skF_3','#skF_4',E_259,F_260),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_4','#skF_3'),B_257)))
      | ~ m1_subset_1(F_260,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_257)))
      | ~ v1_funct_2(F_260,'#skF_4',B_257)
      | ~ v1_funct_1(F_260)
      | ~ m1_subset_1(E_259,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_257)))
      | ~ v1_funct_2(E_259,'#skF_3',B_257)
      | ~ v1_funct_1(E_259)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(B_257)
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_317])).

tff(c_346,plain,(
    ! [B_257,E_259,F_260] :
      ( m1_subset_1(k1_tmap_1('#skF_1',B_257,'#skF_3','#skF_4',E_259,F_260),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_4','#skF_3'),B_257)))
      | ~ m1_subset_1(F_260,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_257)))
      | ~ v1_funct_2(F_260,'#skF_4',B_257)
      | ~ v1_funct_1(F_260)
      | ~ m1_subset_1(E_259,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_257)))
      | ~ v1_funct_2(E_259,'#skF_3',B_257)
      | ~ v1_funct_1(E_259)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(B_257)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_334])).

tff(c_347,plain,(
    ! [B_257,E_259,F_260] :
      ( m1_subset_1(k1_tmap_1('#skF_1',B_257,'#skF_3','#skF_4',E_259,F_260),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_4','#skF_3'),B_257)))
      | ~ m1_subset_1(F_260,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_257)))
      | ~ v1_funct_2(F_260,'#skF_4',B_257)
      | ~ v1_funct_1(F_260)
      | ~ m1_subset_1(E_259,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_257)))
      | ~ v1_funct_2(E_259,'#skF_3',B_257)
      | ~ v1_funct_1(E_259)
      | v1_xboole_0(B_257) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_44,c_40,c_346])).

tff(c_273,plain,(
    ! [E_244,A_243,D_247,C_246,F_245,B_242] :
      ( v1_funct_2(k1_tmap_1(A_243,B_242,C_246,D_247,E_244,F_245),k4_subset_1(A_243,C_246,D_247),B_242)
      | ~ m1_subset_1(F_245,k1_zfmisc_1(k2_zfmisc_1(D_247,B_242)))
      | ~ v1_funct_2(F_245,D_247,B_242)
      | ~ v1_funct_1(F_245)
      | ~ m1_subset_1(E_244,k1_zfmisc_1(k2_zfmisc_1(C_246,B_242)))
      | ~ v1_funct_2(E_244,C_246,B_242)
      | ~ v1_funct_1(E_244)
      | ~ m1_subset_1(D_247,k1_zfmisc_1(A_243))
      | v1_xboole_0(D_247)
      | ~ m1_subset_1(C_246,k1_zfmisc_1(A_243))
      | v1_xboole_0(C_246)
      | v1_xboole_0(B_242)
      | v1_xboole_0(A_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_276,plain,(
    ! [B_242,E_244,F_245] :
      ( v1_funct_2(k1_tmap_1('#skF_1',B_242,'#skF_3','#skF_4',E_244,F_245),k4_subset_1('#skF_1','#skF_4','#skF_3'),B_242)
      | ~ m1_subset_1(F_245,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_242)))
      | ~ v1_funct_2(F_245,'#skF_4',B_242)
      | ~ v1_funct_1(F_245)
      | ~ m1_subset_1(E_244,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_242)))
      | ~ v1_funct_2(E_244,'#skF_3',B_242)
      | ~ v1_funct_1(E_244)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(B_242)
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_273])).

tff(c_278,plain,(
    ! [B_242,E_244,F_245] :
      ( v1_funct_2(k1_tmap_1('#skF_1',B_242,'#skF_3','#skF_4',E_244,F_245),k4_subset_1('#skF_1','#skF_4','#skF_3'),B_242)
      | ~ m1_subset_1(F_245,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_242)))
      | ~ v1_funct_2(F_245,'#skF_4',B_242)
      | ~ v1_funct_1(F_245)
      | ~ m1_subset_1(E_244,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_242)))
      | ~ v1_funct_2(E_244,'#skF_3',B_242)
      | ~ v1_funct_1(E_244)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(B_242)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_276])).

tff(c_279,plain,(
    ! [B_242,E_244,F_245] :
      ( v1_funct_2(k1_tmap_1('#skF_1',B_242,'#skF_3','#skF_4',E_244,F_245),k4_subset_1('#skF_1','#skF_4','#skF_3'),B_242)
      | ~ m1_subset_1(F_245,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_242)))
      | ~ v1_funct_2(F_245,'#skF_4',B_242)
      | ~ v1_funct_1(F_245)
      | ~ m1_subset_1(E_244,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_242)))
      | ~ v1_funct_2(E_244,'#skF_3',B_242)
      | ~ v1_funct_1(E_244)
      | v1_xboole_0(B_242) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_44,c_40,c_278])).

tff(c_49,plain,(
    ! [A_203,C_204,B_205] :
      ( k9_subset_1(A_203,C_204,B_205) = k9_subset_1(A_203,B_205,C_204)
      | ~ m1_subset_1(C_204,k1_zfmisc_1(A_203)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_60,plain,(
    ! [B_205] : k9_subset_1('#skF_1',B_205,'#skF_3') = k9_subset_1('#skF_1','#skF_3',B_205) ),
    inference(resolution,[status(thm)],[c_42,c_49])).

tff(c_24,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_106,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_4','#skF_3')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_60,c_24])).

tff(c_242,plain,(
    ! [A_233,C_236,E_234] :
      ( v1_funct_1(k1_tmap_1(A_233,'#skF_2',C_236,'#skF_4',E_234,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_234,k1_zfmisc_1(k2_zfmisc_1(C_236,'#skF_2')))
      | ~ v1_funct_2(E_234,C_236,'#skF_2')
      | ~ v1_funct_1(E_234)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_233))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_236,k1_zfmisc_1(A_233))
      | v1_xboole_0(C_236)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_233) ) ),
    inference(resolution,[status(thm)],[c_26,c_240])).

tff(c_247,plain,(
    ! [A_233,C_236,E_234] :
      ( v1_funct_1(k1_tmap_1(A_233,'#skF_2',C_236,'#skF_4',E_234,'#skF_6'))
      | ~ m1_subset_1(E_234,k1_zfmisc_1(k2_zfmisc_1(C_236,'#skF_2')))
      | ~ v1_funct_2(E_234,C_236,'#skF_2')
      | ~ v1_funct_1(E_234)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_233))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_236,k1_zfmisc_1(A_233))
      | v1_xboole_0(C_236)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_233) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_242])).

tff(c_253,plain,(
    ! [A_238,C_239,E_240] :
      ( v1_funct_1(k1_tmap_1(A_238,'#skF_2',C_239,'#skF_4',E_240,'#skF_6'))
      | ~ m1_subset_1(E_240,k1_zfmisc_1(k2_zfmisc_1(C_239,'#skF_2')))
      | ~ v1_funct_2(E_240,C_239,'#skF_2')
      | ~ v1_funct_1(E_240)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_238))
      | ~ m1_subset_1(C_239,k1_zfmisc_1(A_238))
      | v1_xboole_0(C_239)
      | v1_xboole_0(A_238) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_40,c_247])).

tff(c_257,plain,(
    ! [A_238] :
      ( v1_funct_1(k1_tmap_1(A_238,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_238))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_238))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_238) ) ),
    inference(resolution,[status(thm)],[c_32,c_253])).

tff(c_264,plain,(
    ! [A_238] :
      ( v1_funct_1(k1_tmap_1(A_238,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_238))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_238))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_238) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_257])).

tff(c_280,plain,(
    ! [A_248] :
      ( v1_funct_1(k1_tmap_1(A_248,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_248))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_248))
      | v1_xboole_0(A_248) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_264])).

tff(c_283,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_280])).

tff(c_286,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_283])).

tff(c_287,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_286])).

tff(c_12,plain,(
    ! [A_134,E_138,C_136,D_137,F_139,B_135] :
      ( m1_subset_1(k1_tmap_1(A_134,B_135,C_136,D_137,E_138,F_139),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_134,C_136,D_137),B_135)))
      | ~ m1_subset_1(F_139,k1_zfmisc_1(k2_zfmisc_1(D_137,B_135)))
      | ~ v1_funct_2(F_139,D_137,B_135)
      | ~ v1_funct_1(F_139)
      | ~ m1_subset_1(E_138,k1_zfmisc_1(k2_zfmisc_1(C_136,B_135)))
      | ~ v1_funct_2(E_138,C_136,B_135)
      | ~ v1_funct_1(E_138)
      | ~ m1_subset_1(D_137,k1_zfmisc_1(A_134))
      | v1_xboole_0(D_137)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(A_134))
      | v1_xboole_0(C_136)
      | v1_xboole_0(B_135)
      | v1_xboole_0(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_682,plain,(
    ! [E_328,A_325,C_327,F_324,D_323,B_326] :
      ( k2_partfun1(k4_subset_1(A_325,C_327,D_323),B_326,k1_tmap_1(A_325,B_326,C_327,D_323,E_328,F_324),D_323) = F_324
      | ~ m1_subset_1(k1_tmap_1(A_325,B_326,C_327,D_323,E_328,F_324),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_325,C_327,D_323),B_326)))
      | ~ v1_funct_2(k1_tmap_1(A_325,B_326,C_327,D_323,E_328,F_324),k4_subset_1(A_325,C_327,D_323),B_326)
      | ~ v1_funct_1(k1_tmap_1(A_325,B_326,C_327,D_323,E_328,F_324))
      | k2_partfun1(D_323,B_326,F_324,k9_subset_1(A_325,C_327,D_323)) != k2_partfun1(C_327,B_326,E_328,k9_subset_1(A_325,C_327,D_323))
      | ~ m1_subset_1(F_324,k1_zfmisc_1(k2_zfmisc_1(D_323,B_326)))
      | ~ v1_funct_2(F_324,D_323,B_326)
      | ~ v1_funct_1(F_324)
      | ~ m1_subset_1(E_328,k1_zfmisc_1(k2_zfmisc_1(C_327,B_326)))
      | ~ v1_funct_2(E_328,C_327,B_326)
      | ~ v1_funct_1(E_328)
      | ~ m1_subset_1(D_323,k1_zfmisc_1(A_325))
      | v1_xboole_0(D_323)
      | ~ m1_subset_1(C_327,k1_zfmisc_1(A_325))
      | v1_xboole_0(C_327)
      | v1_xboole_0(B_326)
      | v1_xboole_0(A_325) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_738,plain,(
    ! [C_338,B_334,D_339,F_337,E_336,A_335] :
      ( k2_partfun1(k4_subset_1(A_335,C_338,D_339),B_334,k1_tmap_1(A_335,B_334,C_338,D_339,E_336,F_337),D_339) = F_337
      | ~ v1_funct_2(k1_tmap_1(A_335,B_334,C_338,D_339,E_336,F_337),k4_subset_1(A_335,C_338,D_339),B_334)
      | ~ v1_funct_1(k1_tmap_1(A_335,B_334,C_338,D_339,E_336,F_337))
      | k2_partfun1(D_339,B_334,F_337,k9_subset_1(A_335,C_338,D_339)) != k2_partfun1(C_338,B_334,E_336,k9_subset_1(A_335,C_338,D_339))
      | ~ m1_subset_1(F_337,k1_zfmisc_1(k2_zfmisc_1(D_339,B_334)))
      | ~ v1_funct_2(F_337,D_339,B_334)
      | ~ v1_funct_1(F_337)
      | ~ m1_subset_1(E_336,k1_zfmisc_1(k2_zfmisc_1(C_338,B_334)))
      | ~ v1_funct_2(E_336,C_338,B_334)
      | ~ v1_funct_1(E_336)
      | ~ m1_subset_1(D_339,k1_zfmisc_1(A_335))
      | v1_xboole_0(D_339)
      | ~ m1_subset_1(C_338,k1_zfmisc_1(A_335))
      | v1_xboole_0(C_338)
      | v1_xboole_0(B_334)
      | v1_xboole_0(A_335) ) ),
    inference(resolution,[status(thm)],[c_12,c_682])).

tff(c_746,plain,(
    ! [B_334,E_336,F_337] :
      ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),B_334,k1_tmap_1('#skF_1',B_334,'#skF_3','#skF_4',E_336,F_337),'#skF_4') = F_337
      | ~ v1_funct_2(k1_tmap_1('#skF_1',B_334,'#skF_3','#skF_4',E_336,F_337),k4_subset_1('#skF_1','#skF_4','#skF_3'),B_334)
      | ~ v1_funct_1(k1_tmap_1('#skF_1',B_334,'#skF_3','#skF_4',E_336,F_337))
      | k2_partfun1('#skF_4',B_334,F_337,k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_3',B_334,E_336,k9_subset_1('#skF_1','#skF_3','#skF_4'))
      | ~ m1_subset_1(F_337,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_334)))
      | ~ v1_funct_2(F_337,'#skF_4',B_334)
      | ~ v1_funct_1(F_337)
      | ~ m1_subset_1(E_336,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_334)))
      | ~ v1_funct_2(E_336,'#skF_3',B_334)
      | ~ v1_funct_1(E_336)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(B_334)
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_738])).

tff(c_749,plain,(
    ! [B_334,E_336,F_337] :
      ( k2_partfun1(k4_subset_1('#skF_1','#skF_4','#skF_3'),B_334,k1_tmap_1('#skF_1',B_334,'#skF_3','#skF_4',E_336,F_337),'#skF_4') = F_337
      | ~ v1_funct_2(k1_tmap_1('#skF_1',B_334,'#skF_3','#skF_4',E_336,F_337),k4_subset_1('#skF_1','#skF_4','#skF_3'),B_334)
      | ~ v1_funct_1(k1_tmap_1('#skF_1',B_334,'#skF_3','#skF_4',E_336,F_337))
      | k2_partfun1('#skF_4',B_334,F_337,k9_subset_1('#skF_1','#skF_4','#skF_3')) != k2_partfun1('#skF_3',B_334,E_336,k9_subset_1('#skF_1','#skF_4','#skF_3'))
      | ~ m1_subset_1(F_337,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_334)))
      | ~ v1_funct_2(F_337,'#skF_4',B_334)
      | ~ v1_funct_1(F_337)
      | ~ m1_subset_1(E_336,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_334)))
      | ~ v1_funct_2(E_336,'#skF_3',B_334)
      | ~ v1_funct_1(E_336)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(B_334)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_60,c_60,c_167,c_746])).

tff(c_751,plain,(
    ! [B_340,E_341,F_342] :
      ( k2_partfun1(k4_subset_1('#skF_1','#skF_4','#skF_3'),B_340,k1_tmap_1('#skF_1',B_340,'#skF_3','#skF_4',E_341,F_342),'#skF_4') = F_342
      | ~ v1_funct_2(k1_tmap_1('#skF_1',B_340,'#skF_3','#skF_4',E_341,F_342),k4_subset_1('#skF_1','#skF_4','#skF_3'),B_340)
      | ~ v1_funct_1(k1_tmap_1('#skF_1',B_340,'#skF_3','#skF_4',E_341,F_342))
      | k2_partfun1('#skF_4',B_340,F_342,k9_subset_1('#skF_1','#skF_4','#skF_3')) != k2_partfun1('#skF_3',B_340,E_341,k9_subset_1('#skF_1','#skF_4','#skF_3'))
      | ~ m1_subset_1(F_342,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_340)))
      | ~ v1_funct_2(F_342,'#skF_4',B_340)
      | ~ v1_funct_1(F_342)
      | ~ m1_subset_1(E_341,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_340)))
      | ~ v1_funct_2(E_341,'#skF_3',B_340)
      | ~ v1_funct_1(E_341)
      | v1_xboole_0(B_340) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_44,c_40,c_749])).

tff(c_756,plain,(
    ! [B_343,E_344,F_345] :
      ( k2_partfun1(k4_subset_1('#skF_1','#skF_4','#skF_3'),B_343,k1_tmap_1('#skF_1',B_343,'#skF_3','#skF_4',E_344,F_345),'#skF_4') = F_345
      | ~ v1_funct_1(k1_tmap_1('#skF_1',B_343,'#skF_3','#skF_4',E_344,F_345))
      | k2_partfun1('#skF_4',B_343,F_345,k9_subset_1('#skF_1','#skF_4','#skF_3')) != k2_partfun1('#skF_3',B_343,E_344,k9_subset_1('#skF_1','#skF_4','#skF_3'))
      | ~ m1_subset_1(F_345,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_343)))
      | ~ v1_funct_2(F_345,'#skF_4',B_343)
      | ~ v1_funct_1(F_345)
      | ~ m1_subset_1(E_344,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_343)))
      | ~ v1_funct_2(E_344,'#skF_3',B_343)
      | ~ v1_funct_1(E_344)
      | v1_xboole_0(B_343) ) ),
    inference(resolution,[status(thm)],[c_279,c_751])).

tff(c_758,plain,(
    ! [E_344] :
      ( k2_partfun1(k4_subset_1('#skF_1','#skF_4','#skF_3'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_344,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_344,'#skF_6'))
      | k2_partfun1('#skF_3','#skF_2',E_344,k9_subset_1('#skF_1','#skF_4','#skF_3')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_4','#skF_3'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_344,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
      | ~ v1_funct_2(E_344,'#skF_3','#skF_2')
      | ~ v1_funct_1(E_344)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_756])).

tff(c_761,plain,(
    ! [E_344] :
      ( k2_partfun1(k4_subset_1('#skF_1','#skF_4','#skF_3'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_344,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_344,'#skF_6'))
      | k2_partfun1('#skF_3','#skF_2',E_344,k9_subset_1('#skF_1','#skF_4','#skF_3')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_4','#skF_3'))
      | ~ m1_subset_1(E_344,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
      | ~ v1_funct_2(E_344,'#skF_3','#skF_2')
      | ~ v1_funct_1(E_344)
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_758])).

tff(c_763,plain,(
    ! [E_346] :
      ( k2_partfun1(k4_subset_1('#skF_1','#skF_4','#skF_3'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_346,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_346,'#skF_6'))
      | k2_partfun1('#skF_3','#skF_2',E_346,k9_subset_1('#skF_1','#skF_4','#skF_3')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_4','#skF_3'))
      | ~ m1_subset_1(E_346,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
      | ~ v1_funct_2(E_346,'#skF_3','#skF_2')
      | ~ v1_funct_1(E_346) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_761])).

tff(c_766,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_4','#skF_3'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
    | ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_4','#skF_3')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_4','#skF_3'))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_763])).

tff(c_769,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_4','#skF_3'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_106,c_287,c_766])).

tff(c_564,plain,(
    ! [B_296,C_297,E_298,A_295,D_293,F_294] :
      ( k2_partfun1(k4_subset_1(A_295,C_297,D_293),B_296,k1_tmap_1(A_295,B_296,C_297,D_293,E_298,F_294),C_297) = E_298
      | ~ m1_subset_1(k1_tmap_1(A_295,B_296,C_297,D_293,E_298,F_294),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_295,C_297,D_293),B_296)))
      | ~ v1_funct_2(k1_tmap_1(A_295,B_296,C_297,D_293,E_298,F_294),k4_subset_1(A_295,C_297,D_293),B_296)
      | ~ v1_funct_1(k1_tmap_1(A_295,B_296,C_297,D_293,E_298,F_294))
      | k2_partfun1(D_293,B_296,F_294,k9_subset_1(A_295,C_297,D_293)) != k2_partfun1(C_297,B_296,E_298,k9_subset_1(A_295,C_297,D_293))
      | ~ m1_subset_1(F_294,k1_zfmisc_1(k2_zfmisc_1(D_293,B_296)))
      | ~ v1_funct_2(F_294,D_293,B_296)
      | ~ v1_funct_1(F_294)
      | ~ m1_subset_1(E_298,k1_zfmisc_1(k2_zfmisc_1(C_297,B_296)))
      | ~ v1_funct_2(E_298,C_297,B_296)
      | ~ v1_funct_1(E_298)
      | ~ m1_subset_1(D_293,k1_zfmisc_1(A_295))
      | v1_xboole_0(D_293)
      | ~ m1_subset_1(C_297,k1_zfmisc_1(A_295))
      | v1_xboole_0(C_297)
      | v1_xboole_0(B_296)
      | v1_xboole_0(A_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_577,plain,(
    ! [E_301,D_304,A_300,F_302,C_303,B_299] :
      ( k2_partfun1(k4_subset_1(A_300,C_303,D_304),B_299,k1_tmap_1(A_300,B_299,C_303,D_304,E_301,F_302),C_303) = E_301
      | ~ v1_funct_2(k1_tmap_1(A_300,B_299,C_303,D_304,E_301,F_302),k4_subset_1(A_300,C_303,D_304),B_299)
      | ~ v1_funct_1(k1_tmap_1(A_300,B_299,C_303,D_304,E_301,F_302))
      | k2_partfun1(D_304,B_299,F_302,k9_subset_1(A_300,C_303,D_304)) != k2_partfun1(C_303,B_299,E_301,k9_subset_1(A_300,C_303,D_304))
      | ~ m1_subset_1(F_302,k1_zfmisc_1(k2_zfmisc_1(D_304,B_299)))
      | ~ v1_funct_2(F_302,D_304,B_299)
      | ~ v1_funct_1(F_302)
      | ~ m1_subset_1(E_301,k1_zfmisc_1(k2_zfmisc_1(C_303,B_299)))
      | ~ v1_funct_2(E_301,C_303,B_299)
      | ~ v1_funct_1(E_301)
      | ~ m1_subset_1(D_304,k1_zfmisc_1(A_300))
      | v1_xboole_0(D_304)
      | ~ m1_subset_1(C_303,k1_zfmisc_1(A_300))
      | v1_xboole_0(C_303)
      | v1_xboole_0(B_299)
      | v1_xboole_0(A_300) ) ),
    inference(resolution,[status(thm)],[c_12,c_564])).

tff(c_585,plain,(
    ! [B_299,E_301,F_302] :
      ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),B_299,k1_tmap_1('#skF_1',B_299,'#skF_3','#skF_4',E_301,F_302),'#skF_3') = E_301
      | ~ v1_funct_2(k1_tmap_1('#skF_1',B_299,'#skF_3','#skF_4',E_301,F_302),k4_subset_1('#skF_1','#skF_4','#skF_3'),B_299)
      | ~ v1_funct_1(k1_tmap_1('#skF_1',B_299,'#skF_3','#skF_4',E_301,F_302))
      | k2_partfun1('#skF_4',B_299,F_302,k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_3',B_299,E_301,k9_subset_1('#skF_1','#skF_3','#skF_4'))
      | ~ m1_subset_1(F_302,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_299)))
      | ~ v1_funct_2(F_302,'#skF_4',B_299)
      | ~ v1_funct_1(F_302)
      | ~ m1_subset_1(E_301,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_299)))
      | ~ v1_funct_2(E_301,'#skF_3',B_299)
      | ~ v1_funct_1(E_301)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(B_299)
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_577])).

tff(c_588,plain,(
    ! [B_299,E_301,F_302] :
      ( k2_partfun1(k4_subset_1('#skF_1','#skF_4','#skF_3'),B_299,k1_tmap_1('#skF_1',B_299,'#skF_3','#skF_4',E_301,F_302),'#skF_3') = E_301
      | ~ v1_funct_2(k1_tmap_1('#skF_1',B_299,'#skF_3','#skF_4',E_301,F_302),k4_subset_1('#skF_1','#skF_4','#skF_3'),B_299)
      | ~ v1_funct_1(k1_tmap_1('#skF_1',B_299,'#skF_3','#skF_4',E_301,F_302))
      | k2_partfun1('#skF_4',B_299,F_302,k9_subset_1('#skF_1','#skF_4','#skF_3')) != k2_partfun1('#skF_3',B_299,E_301,k9_subset_1('#skF_1','#skF_4','#skF_3'))
      | ~ m1_subset_1(F_302,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_299)))
      | ~ v1_funct_2(F_302,'#skF_4',B_299)
      | ~ v1_funct_1(F_302)
      | ~ m1_subset_1(E_301,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_299)))
      | ~ v1_funct_2(E_301,'#skF_3',B_299)
      | ~ v1_funct_1(E_301)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(B_299)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_60,c_60,c_167,c_585])).

tff(c_590,plain,(
    ! [B_305,E_306,F_307] :
      ( k2_partfun1(k4_subset_1('#skF_1','#skF_4','#skF_3'),B_305,k1_tmap_1('#skF_1',B_305,'#skF_3','#skF_4',E_306,F_307),'#skF_3') = E_306
      | ~ v1_funct_2(k1_tmap_1('#skF_1',B_305,'#skF_3','#skF_4',E_306,F_307),k4_subset_1('#skF_1','#skF_4','#skF_3'),B_305)
      | ~ v1_funct_1(k1_tmap_1('#skF_1',B_305,'#skF_3','#skF_4',E_306,F_307))
      | k2_partfun1('#skF_4',B_305,F_307,k9_subset_1('#skF_1','#skF_4','#skF_3')) != k2_partfun1('#skF_3',B_305,E_306,k9_subset_1('#skF_1','#skF_4','#skF_3'))
      | ~ m1_subset_1(F_307,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_305)))
      | ~ v1_funct_2(F_307,'#skF_4',B_305)
      | ~ v1_funct_1(F_307)
      | ~ m1_subset_1(E_306,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_305)))
      | ~ v1_funct_2(E_306,'#skF_3',B_305)
      | ~ v1_funct_1(E_306)
      | v1_xboole_0(B_305) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_44,c_40,c_588])).

tff(c_595,plain,(
    ! [B_308,E_309,F_310] :
      ( k2_partfun1(k4_subset_1('#skF_1','#skF_4','#skF_3'),B_308,k1_tmap_1('#skF_1',B_308,'#skF_3','#skF_4',E_309,F_310),'#skF_3') = E_309
      | ~ v1_funct_1(k1_tmap_1('#skF_1',B_308,'#skF_3','#skF_4',E_309,F_310))
      | k2_partfun1('#skF_4',B_308,F_310,k9_subset_1('#skF_1','#skF_4','#skF_3')) != k2_partfun1('#skF_3',B_308,E_309,k9_subset_1('#skF_1','#skF_4','#skF_3'))
      | ~ m1_subset_1(F_310,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_308)))
      | ~ v1_funct_2(F_310,'#skF_4',B_308)
      | ~ v1_funct_1(F_310)
      | ~ m1_subset_1(E_309,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_308)))
      | ~ v1_funct_2(E_309,'#skF_3',B_308)
      | ~ v1_funct_1(E_309)
      | v1_xboole_0(B_308) ) ),
    inference(resolution,[status(thm)],[c_279,c_590])).

tff(c_597,plain,(
    ! [E_309] :
      ( k2_partfun1(k4_subset_1('#skF_1','#skF_4','#skF_3'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_309,'#skF_6'),'#skF_3') = E_309
      | ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_309,'#skF_6'))
      | k2_partfun1('#skF_3','#skF_2',E_309,k9_subset_1('#skF_1','#skF_4','#skF_3')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_4','#skF_3'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_309,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
      | ~ v1_funct_2(E_309,'#skF_3','#skF_2')
      | ~ v1_funct_1(E_309)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_595])).

tff(c_600,plain,(
    ! [E_309] :
      ( k2_partfun1(k4_subset_1('#skF_1','#skF_4','#skF_3'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_309,'#skF_6'),'#skF_3') = E_309
      | ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_309,'#skF_6'))
      | k2_partfun1('#skF_3','#skF_2',E_309,k9_subset_1('#skF_1','#skF_4','#skF_3')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_4','#skF_3'))
      | ~ m1_subset_1(E_309,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
      | ~ v1_funct_2(E_309,'#skF_3','#skF_2')
      | ~ v1_funct_1(E_309)
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_597])).

tff(c_602,plain,(
    ! [E_311] :
      ( k2_partfun1(k4_subset_1('#skF_1','#skF_4','#skF_3'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_311,'#skF_6'),'#skF_3') = E_311
      | ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_311,'#skF_6'))
      | k2_partfun1('#skF_3','#skF_2',E_311,k9_subset_1('#skF_1','#skF_4','#skF_3')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_4','#skF_3'))
      | ~ m1_subset_1(E_311,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
      | ~ v1_funct_2(E_311,'#skF_3','#skF_2')
      | ~ v1_funct_1(E_311) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_600])).

tff(c_605,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_4','#skF_3'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
    | ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_4','#skF_3')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_4','#skF_3'))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_602])).

tff(c_608,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_4','#skF_3'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_106,c_287,c_605])).

tff(c_774,plain,(
    ! [G_349,B_350,A_348,C_351,D_347] :
      ( k1_tmap_1(A_348,B_350,C_351,D_347,k2_partfun1(k4_subset_1(A_348,C_351,D_347),B_350,G_349,C_351),k2_partfun1(k4_subset_1(A_348,C_351,D_347),B_350,G_349,D_347)) = G_349
      | ~ m1_subset_1(G_349,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_348,C_351,D_347),B_350)))
      | ~ v1_funct_2(G_349,k4_subset_1(A_348,C_351,D_347),B_350)
      | ~ v1_funct_1(G_349)
      | k2_partfun1(D_347,B_350,k2_partfun1(k4_subset_1(A_348,C_351,D_347),B_350,G_349,D_347),k9_subset_1(A_348,C_351,D_347)) != k2_partfun1(C_351,B_350,k2_partfun1(k4_subset_1(A_348,C_351,D_347),B_350,G_349,C_351),k9_subset_1(A_348,C_351,D_347))
      | ~ m1_subset_1(k2_partfun1(k4_subset_1(A_348,C_351,D_347),B_350,G_349,D_347),k1_zfmisc_1(k2_zfmisc_1(D_347,B_350)))
      | ~ v1_funct_2(k2_partfun1(k4_subset_1(A_348,C_351,D_347),B_350,G_349,D_347),D_347,B_350)
      | ~ v1_funct_1(k2_partfun1(k4_subset_1(A_348,C_351,D_347),B_350,G_349,D_347))
      | ~ m1_subset_1(k2_partfun1(k4_subset_1(A_348,C_351,D_347),B_350,G_349,C_351),k1_zfmisc_1(k2_zfmisc_1(C_351,B_350)))
      | ~ v1_funct_2(k2_partfun1(k4_subset_1(A_348,C_351,D_347),B_350,G_349,C_351),C_351,B_350)
      | ~ v1_funct_1(k2_partfun1(k4_subset_1(A_348,C_351,D_347),B_350,G_349,C_351))
      | ~ m1_subset_1(D_347,k1_zfmisc_1(A_348))
      | v1_xboole_0(D_347)
      | ~ m1_subset_1(C_351,k1_zfmisc_1(A_348))
      | v1_xboole_0(C_351)
      | v1_xboole_0(B_350)
      | v1_xboole_0(A_348) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_780,plain,
    ( k1_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',k2_partfun1(k4_subset_1('#skF_1','#skF_4','#skF_3'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4'),k2_partfun1(k4_subset_1('#skF_1','#skF_4','#skF_3'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3')) = k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_4','#skF_3'),'#skF_2')))
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_4','#skF_3'),'#skF_2')
    | ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k2_partfun1('#skF_3','#skF_2',k2_partfun1(k4_subset_1('#skF_1','#skF_4','#skF_3'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k9_subset_1('#skF_1','#skF_4','#skF_3')) != k2_partfun1('#skF_4','#skF_2',k2_partfun1(k4_subset_1('#skF_1','#skF_4','#skF_3'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4'),k9_subset_1('#skF_1','#skF_4','#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_1','#skF_4','#skF_3'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_1','#skF_4','#skF_3'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'))
    | ~ m1_subset_1(k2_partfun1(k4_subset_1('#skF_1','#skF_4','#skF_3'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_1','#skF_4','#skF_3'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4'),'#skF_4','#skF_2')
    | ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_1','#skF_4','#skF_3'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_608,c_774])).

tff(c_796,plain,
    ( k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') = k1_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6','#skF_5')
    | ~ m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_4','#skF_3'),'#skF_2')))
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_4','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_42,c_30,c_769,c_28,c_769,c_26,c_769,c_36,c_608,c_34,c_608,c_32,c_769,c_106,c_608,c_287,c_769,c_608,c_780])).

tff(c_797,plain,
    ( k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') = k1_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6','#skF_5')
    | ~ m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_4','#skF_3'),'#skF_2')))
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_4','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_46,c_40,c_44,c_796])).

tff(c_801,plain,(
    ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_4','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_797])).

tff(c_804,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_279,c_801])).

tff(c_807,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_28,c_26,c_804])).

tff(c_809,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_807])).

tff(c_810,plain,
    ( ~ m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_4','#skF_3'),'#skF_2')))
    | k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') = k1_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_797])).

tff(c_812,plain,(
    ~ m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_4','#skF_3'),'#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_810])).

tff(c_815,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_347,c_812])).

tff(c_818,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_28,c_26,c_815])).

tff(c_820,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_818])).

tff(c_821,plain,(
    k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') = k1_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_810])).

tff(c_811,plain,(
    v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_4','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_797])).

tff(c_823,plain,(
    v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6','#skF_5'),k4_subset_1('#skF_1','#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_821,c_811])).

tff(c_822,plain,(
    m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_4','#skF_3'),'#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_810])).

tff(c_941,plain,(
    m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_4','#skF_3'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_821,c_822])).

tff(c_18,plain,(
    ! [F_145,D_143,B_141,C_142,A_140] :
      ( r1_funct_2(A_140,B_141,C_142,D_143,F_145,F_145)
      | ~ m1_subset_1(F_145,k1_zfmisc_1(k2_zfmisc_1(C_142,D_143)))
      | ~ v1_funct_2(F_145,C_142,D_143)
      | ~ m1_subset_1(F_145,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141)))
      | ~ v1_funct_2(F_145,A_140,B_141)
      | ~ v1_funct_1(F_145)
      | v1_xboole_0(D_143)
      | v1_xboole_0(B_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_342,plain,(
    ! [A_258,F_260,E_259,C_261,D_262,B_141,B_257,A_140] :
      ( r1_funct_2(A_140,B_141,k4_subset_1(A_258,C_261,D_262),B_257,k1_tmap_1(A_258,B_257,C_261,D_262,E_259,F_260),k1_tmap_1(A_258,B_257,C_261,D_262,E_259,F_260))
      | ~ v1_funct_2(k1_tmap_1(A_258,B_257,C_261,D_262,E_259,F_260),k4_subset_1(A_258,C_261,D_262),B_257)
      | ~ m1_subset_1(k1_tmap_1(A_258,B_257,C_261,D_262,E_259,F_260),k1_zfmisc_1(k2_zfmisc_1(A_140,B_141)))
      | ~ v1_funct_2(k1_tmap_1(A_258,B_257,C_261,D_262,E_259,F_260),A_140,B_141)
      | ~ v1_funct_1(k1_tmap_1(A_258,B_257,C_261,D_262,E_259,F_260))
      | v1_xboole_0(B_141)
      | ~ m1_subset_1(F_260,k1_zfmisc_1(k2_zfmisc_1(D_262,B_257)))
      | ~ v1_funct_2(F_260,D_262,B_257)
      | ~ v1_funct_1(F_260)
      | ~ m1_subset_1(E_259,k1_zfmisc_1(k2_zfmisc_1(C_261,B_257)))
      | ~ v1_funct_2(E_259,C_261,B_257)
      | ~ v1_funct_1(E_259)
      | ~ m1_subset_1(D_262,k1_zfmisc_1(A_258))
      | v1_xboole_0(D_262)
      | ~ m1_subset_1(C_261,k1_zfmisc_1(A_258))
      | v1_xboole_0(C_261)
      | v1_xboole_0(B_257)
      | v1_xboole_0(A_258) ) ),
    inference(resolution,[status(thm)],[c_317,c_18])).

tff(c_22,plain,(
    ~ r1_funct_2(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k4_subset_1('#skF_1','#skF_4','#skF_3'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_168,plain,(
    ~ r1_funct_2(k4_subset_1('#skF_1','#skF_4','#skF_3'),'#skF_2',k4_subset_1('#skF_1','#skF_4','#skF_3'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_22])).

tff(c_827,plain,(
    ~ r1_funct_2(k4_subset_1('#skF_1','#skF_4','#skF_3'),'#skF_2',k4_subset_1('#skF_1','#skF_4','#skF_3'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6','#skF_5'),k1_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_821,c_168])).

tff(c_1030,plain,
    ( ~ m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_4','#skF_3'),'#skF_2')))
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6','#skF_5'),k4_subset_1('#skF_1','#skF_4','#skF_3'),'#skF_2')
    | ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_342,c_827])).

tff(c_1033,plain,
    ( v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_42,c_30,c_28,c_26,c_36,c_34,c_32,c_315,c_823,c_941,c_1030])).

tff(c_1035,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_46,c_40,c_44,c_1033])).

%------------------------------------------------------------------------------
