%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1762+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:21 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :  139 (1268 expanded)
%              Number of leaves         :   38 ( 480 expanded)
%              Depth                    :   19
%              Number of atoms          :  460 (11710 expanded)
%              Number of equality atoms :   52 ( 857 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_204,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(D),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                       => ( m1_pre_topc(C,D)
                         => ! [F] :
                              ( ( v1_funct_1(F)
                                & v1_funct_2(F,u1_struct_0(C),u1_struct_0(B))
                                & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                             => ( ! [G] :
                                    ( m1_subset_1(G,u1_struct_0(D))
                                   => ( r2_hidden(G,u1_struct_0(C))
                                     => k3_funct_2(u1_struct_0(D),u1_struct_0(B),E,G) = k1_funct_1(F,G) ) )
                               => r2_funct_2(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,D,C,E),F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_tmap_1)).

tff(f_108,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_144,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,A,B)
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
             => ! [D] :
                  ( ( ~ v1_xboole_0(D)
                    & m1_subset_1(D,k1_zfmisc_1(A)) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,D,B)
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(D,B))) )
                     => ( ! [F] :
                            ( m1_subset_1(F,A)
                           => ( r2_hidden(F,D)
                             => k3_funct_2(A,B,C,F) = k1_funct_1(E,F) ) )
                       => k2_partfun1(A,B,C,D) = E ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_funct_2)).

tff(f_75,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_151,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ( m1_pre_topc(D,C)
                       => k3_tmap_1(A,B,C,D,E) = k2_partfun1(u1_struct_0(C),u1_struct_0(B),E,u1_struct_0(D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

tff(c_32,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_30,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_28,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_131,plain,(
    ! [A_252,B_253,C_254,D_255] :
      ( r2_funct_2(A_252,B_253,C_254,C_254)
      | ~ m1_subset_1(D_255,k1_zfmisc_1(k2_zfmisc_1(A_252,B_253)))
      | ~ v1_funct_2(D_255,A_252,B_253)
      | ~ v1_funct_1(D_255)
      | ~ m1_subset_1(C_254,k1_zfmisc_1(k2_zfmisc_1(A_252,B_253)))
      | ~ v1_funct_2(C_254,A_252,B_253)
      | ~ v1_funct_1(C_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_133,plain,(
    ! [C_254] :
      ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_254,C_254)
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(C_254,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_254,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_254) ) ),
    inference(resolution,[status(thm)],[c_28,c_131])).

tff(c_142,plain,(
    ! [C_256] :
      ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_256,C_256)
      | ~ m1_subset_1(C_256,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_256,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_256) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_133])).

tff(c_144,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_7','#skF_7')
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_28,c_142])).

tff(c_147,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_144])).

tff(c_56,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_42,plain,(
    m1_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_63,plain,(
    ! [B_237,A_238] :
      ( l1_pre_topc(B_237)
      | ~ m1_pre_topc(B_237,A_238)
      | ~ l1_pre_topc(A_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_66,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_63])).

tff(c_75,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_66])).

tff(c_4,plain,(
    ! [A_32] :
      ( l1_struct_0(A_32)
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_50,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_40,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_38,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_36,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_154,plain,(
    ! [D_260,E_262,C_259,A_261,B_258] :
      ( r2_hidden('#skF_1'(B_258,C_259,D_260,A_261,E_262),D_260)
      | k2_partfun1(A_261,B_258,C_259,D_260) = E_262
      | ~ m1_subset_1(E_262,k1_zfmisc_1(k2_zfmisc_1(D_260,B_258)))
      | ~ v1_funct_2(E_262,D_260,B_258)
      | ~ v1_funct_1(E_262)
      | ~ m1_subset_1(D_260,k1_zfmisc_1(A_261))
      | v1_xboole_0(D_260)
      | ~ m1_subset_1(C_259,k1_zfmisc_1(k2_zfmisc_1(A_261,B_258)))
      | ~ v1_funct_2(C_259,A_261,B_258)
      | ~ v1_funct_1(C_259)
      | v1_xboole_0(B_258)
      | v1_xboole_0(A_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_158,plain,(
    ! [C_259,A_261] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_3'),C_259,u1_struct_0('#skF_5'),A_261,'#skF_6'),u1_struct_0('#skF_5'))
      | k2_partfun1(A_261,u1_struct_0('#skF_3'),C_259,u1_struct_0('#skF_5')) = '#skF_6'
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_261))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_259,k1_zfmisc_1(k2_zfmisc_1(A_261,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_259,A_261,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_259)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(A_261) ) ),
    inference(resolution,[status(thm)],[c_36,c_154])).

tff(c_164,plain,(
    ! [C_259,A_261] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_3'),C_259,u1_struct_0('#skF_5'),A_261,'#skF_6'),u1_struct_0('#skF_5'))
      | k2_partfun1(A_261,u1_struct_0('#skF_3'),C_259,u1_struct_0('#skF_5')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_261))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_259,k1_zfmisc_1(k2_zfmisc_1(A_261,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_259,A_261,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_259)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(A_261) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_158])).

tff(c_168,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_164])).

tff(c_8,plain,(
    ! [A_36] :
      ( ~ v1_xboole_0(u1_struct_0(A_36))
      | ~ l1_struct_0(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_171,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_168,c_8])).

tff(c_174,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_171])).

tff(c_177,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_174])).

tff(c_181,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_177])).

tff(c_183,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_184,plain,(
    ! [B_267,E_271,C_268,D_269,A_270] :
      ( m1_subset_1('#skF_1'(B_267,C_268,D_269,A_270,E_271),A_270)
      | k2_partfun1(A_270,B_267,C_268,D_269) = E_271
      | ~ m1_subset_1(E_271,k1_zfmisc_1(k2_zfmisc_1(D_269,B_267)))
      | ~ v1_funct_2(E_271,D_269,B_267)
      | ~ v1_funct_1(E_271)
      | ~ m1_subset_1(D_269,k1_zfmisc_1(A_270))
      | v1_xboole_0(D_269)
      | ~ m1_subset_1(C_268,k1_zfmisc_1(k2_zfmisc_1(A_270,B_267)))
      | ~ v1_funct_2(C_268,A_270,B_267)
      | ~ v1_funct_1(C_268)
      | v1_xboole_0(B_267)
      | v1_xboole_0(A_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_188,plain,(
    ! [C_268,A_270] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_3'),C_268,u1_struct_0('#skF_5'),A_270,'#skF_6'),A_270)
      | k2_partfun1(A_270,u1_struct_0('#skF_3'),C_268,u1_struct_0('#skF_5')) = '#skF_6'
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_270))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_268,k1_zfmisc_1(k2_zfmisc_1(A_270,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_268,A_270,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_268)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(A_270) ) ),
    inference(resolution,[status(thm)],[c_36,c_184])).

tff(c_195,plain,(
    ! [C_268,A_270] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_3'),C_268,u1_struct_0('#skF_5'),A_270,'#skF_6'),A_270)
      | k2_partfun1(A_270,u1_struct_0('#skF_3'),C_268,u1_struct_0('#skF_5')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_270))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_268,k1_zfmisc_1(k2_zfmisc_1(A_270,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_268,A_270,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_268)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(A_270) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_188])).

tff(c_196,plain,(
    ! [C_268,A_270] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_3'),C_268,u1_struct_0('#skF_5'),A_270,'#skF_6'),A_270)
      | k2_partfun1(A_270,u1_struct_0('#skF_3'),C_268,u1_struct_0('#skF_5')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_270))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_268,k1_zfmisc_1(k2_zfmisc_1(A_270,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_268,A_270,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_268)
      | v1_xboole_0(A_270) ) ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_195])).

tff(c_323,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_326,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_323,c_8])).

tff(c_329,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_326])).

tff(c_332,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_329])).

tff(c_336,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_332])).

tff(c_338,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_34,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_22,plain,(
    ! [B_113,A_111] :
      ( m1_subset_1(u1_struct_0(B_113),k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ m1_pre_topc(B_113,A_111)
      | ~ l1_pre_topc(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_46,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_69,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_63])).

tff(c_78,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_69])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_186,plain,(
    ! [C_268,A_270] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_3'),C_268,u1_struct_0('#skF_4'),A_270,'#skF_7'),A_270)
      | k2_partfun1(A_270,u1_struct_0('#skF_3'),C_268,u1_struct_0('#skF_4')) = '#skF_7'
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_270))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_268,k1_zfmisc_1(k2_zfmisc_1(A_270,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_268,A_270,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_268)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(A_270) ) ),
    inference(resolution,[status(thm)],[c_28,c_184])).

tff(c_191,plain,(
    ! [C_268,A_270] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_3'),C_268,u1_struct_0('#skF_4'),A_270,'#skF_7'),A_270)
      | k2_partfun1(A_270,u1_struct_0('#skF_3'),C_268,u1_struct_0('#skF_4')) = '#skF_7'
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_270))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_268,k1_zfmisc_1(k2_zfmisc_1(A_270,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_268,A_270,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_268)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(A_270) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_186])).

tff(c_192,plain,(
    ! [C_268,A_270] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_3'),C_268,u1_struct_0('#skF_4'),A_270,'#skF_7'),A_270)
      | k2_partfun1(A_270,u1_struct_0('#skF_3'),C_268,u1_struct_0('#skF_4')) = '#skF_7'
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_270))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_268,k1_zfmisc_1(k2_zfmisc_1(A_270,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_268,A_270,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_268)
      | v1_xboole_0(A_270) ) ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_191])).

tff(c_197,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_192])).

tff(c_200,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_197,c_8])).

tff(c_203,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_200])).

tff(c_206,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_203])).

tff(c_210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_206])).

tff(c_212,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_192])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_58,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_52,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_83,plain,(
    ! [A_241,B_242,C_243,D_244] :
      ( k2_partfun1(A_241,B_242,C_243,D_244) = k7_relat_1(C_243,D_244)
      | ~ m1_subset_1(C_243,k1_zfmisc_1(k2_zfmisc_1(A_241,B_242)))
      | ~ v1_funct_1(C_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_87,plain,(
    ! [D_244] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',D_244) = k7_relat_1('#skF_6',D_244)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_36,c_83])).

tff(c_93,plain,(
    ! [D_244] : k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',D_244) = k7_relat_1('#skF_6',D_244) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_87])).

tff(c_252,plain,(
    ! [C_275,E_278,A_277,D_274,B_276] :
      ( k3_tmap_1(A_277,B_276,C_275,D_274,E_278) = k2_partfun1(u1_struct_0(C_275),u1_struct_0(B_276),E_278,u1_struct_0(D_274))
      | ~ m1_pre_topc(D_274,C_275)
      | ~ m1_subset_1(E_278,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_275),u1_struct_0(B_276))))
      | ~ v1_funct_2(E_278,u1_struct_0(C_275),u1_struct_0(B_276))
      | ~ v1_funct_1(E_278)
      | ~ m1_pre_topc(D_274,A_277)
      | ~ m1_pre_topc(C_275,A_277)
      | ~ l1_pre_topc(B_276)
      | ~ v2_pre_topc(B_276)
      | v2_struct_0(B_276)
      | ~ l1_pre_topc(A_277)
      | ~ v2_pre_topc(A_277)
      | v2_struct_0(A_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_259,plain,(
    ! [A_277,D_274] :
      ( k3_tmap_1(A_277,'#skF_3','#skF_5',D_274,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_274))
      | ~ m1_pre_topc(D_274,'#skF_5')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_274,A_277)
      | ~ m1_pre_topc('#skF_5',A_277)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_277)
      | ~ v2_pre_topc(A_277)
      | v2_struct_0(A_277) ) ),
    inference(resolution,[status(thm)],[c_36,c_252])).

tff(c_267,plain,(
    ! [D_274,A_277] :
      ( k7_relat_1('#skF_6',u1_struct_0(D_274)) = k3_tmap_1(A_277,'#skF_3','#skF_5',D_274,'#skF_6')
      | ~ m1_pre_topc(D_274,'#skF_5')
      | ~ m1_pre_topc(D_274,A_277)
      | ~ m1_pre_topc('#skF_5',A_277)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_277)
      | ~ v2_pre_topc(A_277)
      | v2_struct_0(A_277) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_40,c_38,c_93,c_259])).

tff(c_290,plain,(
    ! [D_281,A_282] :
      ( k7_relat_1('#skF_6',u1_struct_0(D_281)) = k3_tmap_1(A_282,'#skF_3','#skF_5',D_281,'#skF_6')
      | ~ m1_pre_topc(D_281,'#skF_5')
      | ~ m1_pre_topc(D_281,A_282)
      | ~ m1_pre_topc('#skF_5',A_282)
      | ~ l1_pre_topc(A_282)
      | ~ v2_pre_topc(A_282)
      | v2_struct_0(A_282) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_267])).

tff(c_294,plain,
    ( k7_relat_1('#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_290])).

tff(c_303,plain,
    ( k7_relat_1('#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_42,c_34,c_294])).

tff(c_304,plain,(
    k7_relat_1('#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_303])).

tff(c_156,plain,(
    ! [C_259,A_261] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_3'),C_259,u1_struct_0('#skF_4'),A_261,'#skF_7'),u1_struct_0('#skF_4'))
      | k2_partfun1(A_261,u1_struct_0('#skF_3'),C_259,u1_struct_0('#skF_4')) = '#skF_7'
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_261))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_259,k1_zfmisc_1(k2_zfmisc_1(A_261,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_259,A_261,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_259)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(A_261) ) ),
    inference(resolution,[status(thm)],[c_28,c_154])).

tff(c_161,plain,(
    ! [C_259,A_261] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_3'),C_259,u1_struct_0('#skF_4'),A_261,'#skF_7'),u1_struct_0('#skF_4'))
      | k2_partfun1(A_261,u1_struct_0('#skF_3'),C_259,u1_struct_0('#skF_4')) = '#skF_7'
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_261))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_259,k1_zfmisc_1(k2_zfmisc_1(A_261,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_259,A_261,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_259)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(A_261) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_156])).

tff(c_213,plain,(
    ! [C_259,A_261] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_3'),C_259,u1_struct_0('#skF_4'),A_261,'#skF_7'),u1_struct_0('#skF_4'))
      | k2_partfun1(A_261,u1_struct_0('#skF_3'),C_259,u1_struct_0('#skF_4')) = '#skF_7'
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_261))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_259,k1_zfmisc_1(k2_zfmisc_1(A_261,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_259,A_261,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_259)
      | v1_xboole_0(A_261) ) ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_161])).

tff(c_214,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_213])).

tff(c_215,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_212,c_214])).

tff(c_216,plain,(
    ! [C_259,A_261] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_3'),C_259,u1_struct_0('#skF_4'),A_261,'#skF_7'),u1_struct_0('#skF_4'))
      | k2_partfun1(A_261,u1_struct_0('#skF_3'),C_259,u1_struct_0('#skF_4')) = '#skF_7'
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_261))
      | ~ m1_subset_1(C_259,k1_zfmisc_1(k2_zfmisc_1(A_261,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_259,A_261,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_259)
      | v1_xboole_0(A_261) ) ),
    inference(splitRight,[status(thm)],[c_213])).

tff(c_26,plain,(
    ! [G_234] :
      ( k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',G_234) = k1_funct_1('#skF_7',G_234)
      | ~ r2_hidden(G_234,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(G_234,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_314,plain,(
    ! [D_285,C_284,E_287,B_283,A_286] :
      ( k3_funct_2(A_286,B_283,C_284,'#skF_1'(B_283,C_284,D_285,A_286,E_287)) != k1_funct_1(E_287,'#skF_1'(B_283,C_284,D_285,A_286,E_287))
      | k2_partfun1(A_286,B_283,C_284,D_285) = E_287
      | ~ m1_subset_1(E_287,k1_zfmisc_1(k2_zfmisc_1(D_285,B_283)))
      | ~ v1_funct_2(E_287,D_285,B_283)
      | ~ v1_funct_1(E_287)
      | ~ m1_subset_1(D_285,k1_zfmisc_1(A_286))
      | v1_xboole_0(D_285)
      | ~ m1_subset_1(C_284,k1_zfmisc_1(k2_zfmisc_1(A_286,B_283)))
      | ~ v1_funct_2(C_284,A_286,B_283)
      | ~ v1_funct_1(C_284)
      | v1_xboole_0(B_283)
      | v1_xboole_0(A_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_317,plain,(
    ! [E_287,D_285] :
      ( k1_funct_1(E_287,'#skF_1'(u1_struct_0('#skF_3'),'#skF_6',D_285,u1_struct_0('#skF_5'),E_287)) != k1_funct_1('#skF_7','#skF_1'(u1_struct_0('#skF_3'),'#skF_6',D_285,u1_struct_0('#skF_5'),E_287))
      | k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',D_285) = E_287
      | ~ m1_subset_1(E_287,k1_zfmisc_1(k2_zfmisc_1(D_285,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(E_287,D_285,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_287)
      | ~ m1_subset_1(D_285,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v1_xboole_0(D_285)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_1'(u1_struct_0('#skF_3'),'#skF_6',D_285,u1_struct_0('#skF_5'),E_287),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_3'),'#skF_6',D_285,u1_struct_0('#skF_5'),E_287),u1_struct_0('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_314])).

tff(c_319,plain,(
    ! [E_287,D_285] :
      ( k1_funct_1(E_287,'#skF_1'(u1_struct_0('#skF_3'),'#skF_6',D_285,u1_struct_0('#skF_5'),E_287)) != k1_funct_1('#skF_7','#skF_1'(u1_struct_0('#skF_3'),'#skF_6',D_285,u1_struct_0('#skF_5'),E_287))
      | k7_relat_1('#skF_6',D_285) = E_287
      | ~ m1_subset_1(E_287,k1_zfmisc_1(k2_zfmisc_1(D_285,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(E_287,D_285,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_287)
      | ~ m1_subset_1(D_285,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v1_xboole_0(D_285)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_1'(u1_struct_0('#skF_3'),'#skF_6',D_285,u1_struct_0('#skF_5'),E_287),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_3'),'#skF_6',D_285,u1_struct_0('#skF_5'),E_287),u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_93,c_317])).

tff(c_320,plain,(
    ! [E_287,D_285] :
      ( k1_funct_1(E_287,'#skF_1'(u1_struct_0('#skF_3'),'#skF_6',D_285,u1_struct_0('#skF_5'),E_287)) != k1_funct_1('#skF_7','#skF_1'(u1_struct_0('#skF_3'),'#skF_6',D_285,u1_struct_0('#skF_5'),E_287))
      | k7_relat_1('#skF_6',D_285) = E_287
      | ~ m1_subset_1(E_287,k1_zfmisc_1(k2_zfmisc_1(D_285,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(E_287,D_285,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_287)
      | ~ m1_subset_1(D_285,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v1_xboole_0(D_285)
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_1'(u1_struct_0('#skF_3'),'#skF_6',D_285,u1_struct_0('#skF_5'),E_287),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_3'),'#skF_6',D_285,u1_struct_0('#skF_5'),E_287),u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_319])).

tff(c_379,plain,(
    ! [E_287,D_285] :
      ( k1_funct_1(E_287,'#skF_1'(u1_struct_0('#skF_3'),'#skF_6',D_285,u1_struct_0('#skF_5'),E_287)) != k1_funct_1('#skF_7','#skF_1'(u1_struct_0('#skF_3'),'#skF_6',D_285,u1_struct_0('#skF_5'),E_287))
      | k7_relat_1('#skF_6',D_285) = E_287
      | ~ m1_subset_1(E_287,k1_zfmisc_1(k2_zfmisc_1(D_285,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(E_287,D_285,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_287)
      | ~ m1_subset_1(D_285,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v1_xboole_0(D_285)
      | ~ r2_hidden('#skF_1'(u1_struct_0('#skF_3'),'#skF_6',D_285,u1_struct_0('#skF_5'),E_287),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_3'),'#skF_6',D_285,u1_struct_0('#skF_5'),E_287),u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_338,c_320])).

tff(c_382,plain,(
    ! [D_285] :
      ( k7_relat_1('#skF_6',D_285) = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(D_285,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_7',D_285,u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(D_285,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v1_xboole_0(D_285)
      | ~ r2_hidden('#skF_1'(u1_struct_0('#skF_3'),'#skF_6',D_285,u1_struct_0('#skF_5'),'#skF_7'),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_3'),'#skF_6',D_285,u1_struct_0('#skF_5'),'#skF_7'),u1_struct_0('#skF_5')) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_379])).

tff(c_386,plain,(
    ! [D_296] :
      ( k7_relat_1('#skF_6',D_296) = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(D_296,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_7',D_296,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(D_296,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v1_xboole_0(D_296)
      | ~ r2_hidden('#skF_1'(u1_struct_0('#skF_3'),'#skF_6',D_296,u1_struct_0('#skF_5'),'#skF_7'),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_3'),'#skF_6',D_296,u1_struct_0('#skF_5'),'#skF_7'),u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_382])).

tff(c_390,plain,
    ( k7_relat_1('#skF_6',u1_struct_0('#skF_4')) = '#skF_7'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_7'),u1_struct_0('#skF_5'))
    | k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_4')) = '#skF_7'
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_216,c_386])).

tff(c_393,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_7'),u1_struct_0('#skF_5'))
    | k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') = '#skF_7'
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_304,c_93,c_30,c_28,c_304,c_390])).

tff(c_394,plain,
    ( ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_7'),u1_struct_0('#skF_5'))
    | k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') = '#skF_7'
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_338,c_212,c_393])).

tff(c_395,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_394])).

tff(c_398,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_395])).

tff(c_402,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_34,c_398])).

tff(c_404,plain,(
    m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_394])).

tff(c_211,plain,(
    ! [C_268,A_270] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_3'),C_268,u1_struct_0('#skF_4'),A_270,'#skF_7'),A_270)
      | k2_partfun1(A_270,u1_struct_0('#skF_3'),C_268,u1_struct_0('#skF_4')) = '#skF_7'
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_270))
      | ~ m1_subset_1(C_268,k1_zfmisc_1(k2_zfmisc_1(A_270,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_268,A_270,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_268)
      | v1_xboole_0(A_270) ) ),
    inference(splitRight,[status(thm)],[c_192])).

tff(c_403,plain,
    ( ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_7'),u1_struct_0('#skF_5'))
    | k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_394])).

tff(c_429,plain,(
    ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_7'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_403])).

tff(c_432,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_4')) = '#skF_7'
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_211,c_429])).

tff(c_435,plain,
    ( k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') = '#skF_7'
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_404,c_304,c_93,c_432])).

tff(c_436,plain,(
    k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_338,c_435])).

tff(c_24,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_438,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_24])).

tff(c_441,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_438])).

tff(c_442,plain,(
    k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_403])).

tff(c_445,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_442,c_24])).

tff(c_448,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_445])).

%------------------------------------------------------------------------------
