%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:31 EST 2020

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 369 expanded)
%              Number of leaves         :   34 ( 160 expanded)
%              Depth                    :   13
%              Number of atoms          :  485 (3127 expanded)
%              Number of equality atoms :   31 ( 155 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

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

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_245,negated_conjecture,(
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
                  & m1_pre_topc(C,B) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,B) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(D),u1_struct_0(A))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(A)))) )
                       => ( ( v1_tsep_1(C,B)
                            & m1_pre_topc(C,B)
                            & m1_pre_topc(C,D) )
                         => ! [F] :
                              ( m1_subset_1(F,u1_struct_0(D))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(C))
                                 => ( F = G
                                   => ( r1_tmap_1(D,A,E,F)
                                    <=> r1_tmap_1(C,A,k3_tmap_1(B,A,D,C,E),G) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_tmap_1)).

tff(f_138,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_124,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_tsep_1(B,A)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
               => ( v1_tsep_1(B,C)
                  & m1_pre_topc(B,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tsep_1)).

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_100,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_180,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & v1_tsep_1(D,B)
                    & m1_pre_topc(D,B) )
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(D))
                         => ( E = F
                           => ( r1_tmap_1(B,A,C,E)
                            <=> r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tmap_1)).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_46,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_30,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_52,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_42,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_34,plain,(
    v1_tsep_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_385,plain,(
    ! [B_308,C_309,A_310] :
      ( r1_tarski(u1_struct_0(B_308),u1_struct_0(C_309))
      | ~ m1_pre_topc(B_308,C_309)
      | ~ m1_pre_topc(C_309,A_310)
      | ~ m1_pre_topc(B_308,A_310)
      | ~ l1_pre_topc(A_310)
      | ~ v2_pre_topc(A_310) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_389,plain,(
    ! [B_308] :
      ( r1_tarski(u1_struct_0(B_308),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_308,'#skF_4')
      | ~ m1_pre_topc(B_308,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_385])).

tff(c_397,plain,(
    ! [B_308] :
      ( r1_tarski(u1_struct_0(B_308),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_308,'#skF_4')
      | ~ m1_pre_topc(B_308,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_389])).

tff(c_437,plain,(
    ! [B_319,C_320,A_321] :
      ( v1_tsep_1(B_319,C_320)
      | ~ r1_tarski(u1_struct_0(B_319),u1_struct_0(C_320))
      | ~ m1_pre_topc(C_320,A_321)
      | v2_struct_0(C_320)
      | ~ m1_pre_topc(B_319,A_321)
      | ~ v1_tsep_1(B_319,A_321)
      | ~ l1_pre_topc(A_321)
      | ~ v2_pre_topc(A_321)
      | v2_struct_0(A_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_443,plain,(
    ! [B_308,A_321] :
      ( v1_tsep_1(B_308,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_321)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_308,A_321)
      | ~ v1_tsep_1(B_308,A_321)
      | ~ l1_pre_topc(A_321)
      | ~ v2_pre_topc(A_321)
      | v2_struct_0(A_321)
      | ~ m1_pre_topc(B_308,'#skF_4')
      | ~ m1_pre_topc(B_308,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_397,c_437])).

tff(c_460,plain,(
    ! [B_322,A_323] :
      ( v1_tsep_1(B_322,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_323)
      | ~ m1_pre_topc(B_322,A_323)
      | ~ v1_tsep_1(B_322,A_323)
      | ~ l1_pre_topc(A_323)
      | ~ v2_pre_topc(A_323)
      | v2_struct_0(A_323)
      | ~ m1_pre_topc(B_322,'#skF_4')
      | ~ m1_pre_topc(B_322,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_443])).

tff(c_462,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_460])).

tff(c_465,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_30,c_52,c_50,c_42,c_462])).

tff(c_466,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_465])).

tff(c_28,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_24,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_26,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_72,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_68,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_70,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_68])).

tff(c_143,plain,(
    r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_62,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_7')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_71,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_62])).

tff(c_145,plain,(
    ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_71])).

tff(c_58,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_56,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_96,plain,(
    ! [B_259,A_260] :
      ( v2_pre_topc(B_259)
      | ~ m1_pre_topc(B_259,A_260)
      | ~ l1_pre_topc(A_260)
      | ~ v2_pre_topc(A_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_99,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_96])).

tff(c_108,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_99])).

tff(c_77,plain,(
    ! [B_257,A_258] :
      ( l1_pre_topc(B_257)
      | ~ m1_pre_topc(B_257,A_258)
      | ~ l1_pre_topc(A_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_80,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_77])).

tff(c_89,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_80])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_38,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_167,plain,(
    ! [B_269,C_270,A_271] :
      ( r1_tarski(u1_struct_0(B_269),u1_struct_0(C_270))
      | ~ m1_pre_topc(B_269,C_270)
      | ~ m1_pre_topc(C_270,A_271)
      | ~ m1_pre_topc(B_269,A_271)
      | ~ l1_pre_topc(A_271)
      | ~ v2_pre_topc(A_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_171,plain,(
    ! [B_269] :
      ( r1_tarski(u1_struct_0(B_269),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_269,'#skF_4')
      | ~ m1_pre_topc(B_269,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_167])).

tff(c_179,plain,(
    ! [B_269] :
      ( r1_tarski(u1_struct_0(B_269),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_269,'#skF_4')
      | ~ m1_pre_topc(B_269,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_171])).

tff(c_226,plain,(
    ! [B_280,C_281,A_282] :
      ( v1_tsep_1(B_280,C_281)
      | ~ r1_tarski(u1_struct_0(B_280),u1_struct_0(C_281))
      | ~ m1_pre_topc(C_281,A_282)
      | v2_struct_0(C_281)
      | ~ m1_pre_topc(B_280,A_282)
      | ~ v1_tsep_1(B_280,A_282)
      | ~ l1_pre_topc(A_282)
      | ~ v2_pre_topc(A_282)
      | v2_struct_0(A_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_232,plain,(
    ! [B_269,A_282] :
      ( v1_tsep_1(B_269,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_282)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_269,A_282)
      | ~ v1_tsep_1(B_269,A_282)
      | ~ l1_pre_topc(A_282)
      | ~ v2_pre_topc(A_282)
      | v2_struct_0(A_282)
      | ~ m1_pre_topc(B_269,'#skF_4')
      | ~ m1_pre_topc(B_269,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_179,c_226])).

tff(c_242,plain,(
    ! [B_283,A_284] :
      ( v1_tsep_1(B_283,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_284)
      | ~ m1_pre_topc(B_283,A_284)
      | ~ v1_tsep_1(B_283,A_284)
      | ~ l1_pre_topc(A_284)
      | ~ v2_pre_topc(A_284)
      | v2_struct_0(A_284)
      | ~ m1_pre_topc(B_283,'#skF_4')
      | ~ m1_pre_topc(B_283,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_232])).

tff(c_244,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_242])).

tff(c_247,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_30,c_52,c_50,c_42,c_244])).

tff(c_248,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_247])).

tff(c_297,plain,(
    ! [B_296,E_297,D_294,A_295,C_298] :
      ( k3_tmap_1(A_295,B_296,C_298,D_294,E_297) = k2_partfun1(u1_struct_0(C_298),u1_struct_0(B_296),E_297,u1_struct_0(D_294))
      | ~ m1_pre_topc(D_294,C_298)
      | ~ m1_subset_1(E_297,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_298),u1_struct_0(B_296))))
      | ~ v1_funct_2(E_297,u1_struct_0(C_298),u1_struct_0(B_296))
      | ~ v1_funct_1(E_297)
      | ~ m1_pre_topc(D_294,A_295)
      | ~ m1_pre_topc(C_298,A_295)
      | ~ l1_pre_topc(B_296)
      | ~ v2_pre_topc(B_296)
      | v2_struct_0(B_296)
      | ~ l1_pre_topc(A_295)
      | ~ v2_pre_topc(A_295)
      | v2_struct_0(A_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_299,plain,(
    ! [A_295,D_294] :
      ( k3_tmap_1(A_295,'#skF_1','#skF_4',D_294,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_294))
      | ~ m1_pre_topc(D_294,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_294,A_295)
      | ~ m1_pre_topc('#skF_4',A_295)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_295)
      | ~ v2_pre_topc(A_295)
      | v2_struct_0(A_295) ) ),
    inference(resolution,[status(thm)],[c_36,c_297])).

tff(c_302,plain,(
    ! [A_295,D_294] :
      ( k3_tmap_1(A_295,'#skF_1','#skF_4',D_294,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_294))
      | ~ m1_pre_topc(D_294,'#skF_4')
      | ~ m1_pre_topc(D_294,A_295)
      | ~ m1_pre_topc('#skF_4',A_295)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_295)
      | ~ v2_pre_topc(A_295)
      | v2_struct_0(A_295) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_40,c_38,c_299])).

tff(c_304,plain,(
    ! [A_299,D_300] :
      ( k3_tmap_1(A_299,'#skF_1','#skF_4',D_300,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_300))
      | ~ m1_pre_topc(D_300,'#skF_4')
      | ~ m1_pre_topc(D_300,A_299)
      | ~ m1_pre_topc('#skF_4',A_299)
      | ~ l1_pre_topc(A_299)
      | ~ v2_pre_topc(A_299)
      | v2_struct_0(A_299) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_302])).

tff(c_310,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_304])).

tff(c_322,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_42,c_30,c_310])).

tff(c_323,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_322])).

tff(c_281,plain,(
    ! [A_289,B_290,C_291,D_292] :
      ( k2_partfun1(u1_struct_0(A_289),u1_struct_0(B_290),C_291,u1_struct_0(D_292)) = k2_tmap_1(A_289,B_290,C_291,D_292)
      | ~ m1_pre_topc(D_292,A_289)
      | ~ m1_subset_1(C_291,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_289),u1_struct_0(B_290))))
      | ~ v1_funct_2(C_291,u1_struct_0(A_289),u1_struct_0(B_290))
      | ~ v1_funct_1(C_291)
      | ~ l1_pre_topc(B_290)
      | ~ v2_pre_topc(B_290)
      | v2_struct_0(B_290)
      | ~ l1_pre_topc(A_289)
      | ~ v2_pre_topc(A_289)
      | v2_struct_0(A_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_283,plain,(
    ! [D_292] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_292)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_292)
      | ~ m1_pre_topc(D_292,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_281])).

tff(c_286,plain,(
    ! [D_292] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_292)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_292)
      | ~ m1_pre_topc(D_292,'#skF_4')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_89,c_58,c_56,c_40,c_38,c_283])).

tff(c_287,plain,(
    ! [D_292] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_292)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_292)
      | ~ m1_pre_topc(D_292,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_60,c_286])).

tff(c_332,plain,
    ( k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_287])).

tff(c_339,plain,(
    k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_332])).

tff(c_344,plain,(
    r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_143])).

tff(c_18,plain,(
    ! [C_115,F_129,D_123,B_99,A_67] :
      ( r1_tmap_1(B_99,A_67,C_115,F_129)
      | ~ r1_tmap_1(D_123,A_67,k2_tmap_1(B_99,A_67,C_115,D_123),F_129)
      | ~ m1_subset_1(F_129,u1_struct_0(D_123))
      | ~ m1_subset_1(F_129,u1_struct_0(B_99))
      | ~ m1_pre_topc(D_123,B_99)
      | ~ v1_tsep_1(D_123,B_99)
      | v2_struct_0(D_123)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_99),u1_struct_0(A_67))))
      | ~ v1_funct_2(C_115,u1_struct_0(B_99),u1_struct_0(A_67))
      | ~ v1_funct_1(C_115)
      | ~ l1_pre_topc(B_99)
      | ~ v2_pre_topc(B_99)
      | v2_struct_0(B_99)
      | ~ l1_pre_topc(A_67)
      | ~ v2_pre_topc(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_350,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_344,c_18])).

tff(c_353,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_108,c_89,c_40,c_38,c_36,c_248,c_30,c_28,c_72,c_350])).

tff(c_355,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_44,c_48,c_145,c_353])).

tff(c_356,plain,(
    r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_585,plain,(
    ! [A_342,F_344,C_343,D_341,B_340] :
      ( r1_tmap_1(D_341,A_342,k2_tmap_1(B_340,A_342,C_343,D_341),F_344)
      | ~ r1_tmap_1(B_340,A_342,C_343,F_344)
      | ~ m1_subset_1(F_344,u1_struct_0(D_341))
      | ~ m1_subset_1(F_344,u1_struct_0(B_340))
      | ~ m1_pre_topc(D_341,B_340)
      | ~ v1_tsep_1(D_341,B_340)
      | v2_struct_0(D_341)
      | ~ m1_subset_1(C_343,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_340),u1_struct_0(A_342))))
      | ~ v1_funct_2(C_343,u1_struct_0(B_340),u1_struct_0(A_342))
      | ~ v1_funct_1(C_343)
      | ~ l1_pre_topc(B_340)
      | ~ v2_pre_topc(B_340)
      | v2_struct_0(B_340)
      | ~ l1_pre_topc(A_342)
      | ~ v2_pre_topc(A_342)
      | v2_struct_0(A_342) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_587,plain,(
    ! [D_341,F_344] :
      ( r1_tmap_1(D_341,'#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5',D_341),F_344)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',F_344)
      | ~ m1_subset_1(F_344,u1_struct_0(D_341))
      | ~ m1_subset_1(F_344,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_341,'#skF_4')
      | ~ v1_tsep_1(D_341,'#skF_4')
      | v2_struct_0(D_341)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_585])).

tff(c_590,plain,(
    ! [D_341,F_344] :
      ( r1_tmap_1(D_341,'#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5',D_341),F_344)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',F_344)
      | ~ m1_subset_1(F_344,u1_struct_0(D_341))
      | ~ m1_subset_1(F_344,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_341,'#skF_4')
      | ~ v1_tsep_1(D_341,'#skF_4')
      | v2_struct_0(D_341)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_108,c_89,c_40,c_38,c_587])).

tff(c_601,plain,(
    ! [D_346,F_347] :
      ( r1_tmap_1(D_346,'#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5',D_346),F_347)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',F_347)
      | ~ m1_subset_1(F_347,u1_struct_0(D_346))
      | ~ m1_subset_1(F_347,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_346,'#skF_4')
      | ~ v1_tsep_1(D_346,'#skF_4')
      | v2_struct_0(D_346) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_44,c_590])).

tff(c_499,plain,(
    ! [A_328,B_329,C_330,D_331] :
      ( k2_partfun1(u1_struct_0(A_328),u1_struct_0(B_329),C_330,u1_struct_0(D_331)) = k2_tmap_1(A_328,B_329,C_330,D_331)
      | ~ m1_pre_topc(D_331,A_328)
      | ~ m1_subset_1(C_330,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_328),u1_struct_0(B_329))))
      | ~ v1_funct_2(C_330,u1_struct_0(A_328),u1_struct_0(B_329))
      | ~ v1_funct_1(C_330)
      | ~ l1_pre_topc(B_329)
      | ~ v2_pre_topc(B_329)
      | v2_struct_0(B_329)
      | ~ l1_pre_topc(A_328)
      | ~ v2_pre_topc(A_328)
      | v2_struct_0(A_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_501,plain,(
    ! [D_331] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_331)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_331)
      | ~ m1_pre_topc(D_331,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_499])).

tff(c_504,plain,(
    ! [D_331] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_331)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_331)
      | ~ m1_pre_topc(D_331,'#skF_4')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_89,c_58,c_56,c_40,c_38,c_501])).

tff(c_505,plain,(
    ! [D_331] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_331)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_331)
      | ~ m1_pre_topc(D_331,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_60,c_504])).

tff(c_506,plain,(
    ! [B_334,D_332,E_335,A_333,C_336] :
      ( k3_tmap_1(A_333,B_334,C_336,D_332,E_335) = k2_partfun1(u1_struct_0(C_336),u1_struct_0(B_334),E_335,u1_struct_0(D_332))
      | ~ m1_pre_topc(D_332,C_336)
      | ~ m1_subset_1(E_335,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_336),u1_struct_0(B_334))))
      | ~ v1_funct_2(E_335,u1_struct_0(C_336),u1_struct_0(B_334))
      | ~ v1_funct_1(E_335)
      | ~ m1_pre_topc(D_332,A_333)
      | ~ m1_pre_topc(C_336,A_333)
      | ~ l1_pre_topc(B_334)
      | ~ v2_pre_topc(B_334)
      | v2_struct_0(B_334)
      | ~ l1_pre_topc(A_333)
      | ~ v2_pre_topc(A_333)
      | v2_struct_0(A_333) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_508,plain,(
    ! [A_333,D_332] :
      ( k3_tmap_1(A_333,'#skF_1','#skF_4',D_332,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_332))
      | ~ m1_pre_topc(D_332,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_332,A_333)
      | ~ m1_pre_topc('#skF_4',A_333)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_333)
      | ~ v2_pre_topc(A_333)
      | v2_struct_0(A_333) ) ),
    inference(resolution,[status(thm)],[c_36,c_506])).

tff(c_511,plain,(
    ! [A_333,D_332] :
      ( k3_tmap_1(A_333,'#skF_1','#skF_4',D_332,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_332))
      | ~ m1_pre_topc(D_332,'#skF_4')
      | ~ m1_pre_topc(D_332,A_333)
      | ~ m1_pre_topc('#skF_4',A_333)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_333)
      | ~ v2_pre_topc(A_333)
      | v2_struct_0(A_333) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_40,c_38,c_508])).

tff(c_522,plain,(
    ! [A_338,D_339] :
      ( k3_tmap_1(A_338,'#skF_1','#skF_4',D_339,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_339))
      | ~ m1_pre_topc(D_339,'#skF_4')
      | ~ m1_pre_topc(D_339,A_338)
      | ~ m1_pre_topc('#skF_4',A_338)
      | ~ l1_pre_topc(A_338)
      | ~ v2_pre_topc(A_338)
      | v2_struct_0(A_338) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_511])).

tff(c_528,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_522])).

tff(c_540,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_42,c_30,c_528])).

tff(c_541,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_540])).

tff(c_553,plain,
    ( k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_541])).

tff(c_559,plain,(
    k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_553])).

tff(c_357,plain,(
    ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_563,plain,(
    ~ r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_559,c_357])).

tff(c_604,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_601,c_563])).

tff(c_607,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_30,c_28,c_72,c_356,c_604])).

tff(c_609,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_607])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:47:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.57/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.54  
% 3.61/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.54  %$ r1_tmap_1 > v1_funct_2 > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.61/1.54  
% 3.61/1.54  %Foreground sorts:
% 3.61/1.54  
% 3.61/1.54  
% 3.61/1.54  %Background operators:
% 3.61/1.54  
% 3.61/1.54  
% 3.61/1.54  %Foreground operators:
% 3.61/1.54  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.61/1.54  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.61/1.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.61/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.61/1.54  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.61/1.54  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.61/1.54  tff('#skF_7', type, '#skF_7': $i).
% 3.61/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.61/1.54  tff('#skF_5', type, '#skF_5': $i).
% 3.61/1.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.61/1.54  tff('#skF_6', type, '#skF_6': $i).
% 3.61/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.61/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.61/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.61/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.61/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.61/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.61/1.54  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.61/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.61/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.61/1.54  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.61/1.54  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.61/1.54  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.61/1.54  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.61/1.54  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.61/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.61/1.54  
% 3.61/1.57  tff(f_245, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(A))))) => (((v1_tsep_1(C, B) & m1_pre_topc(C, B)) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, A, E, F) <=> r1_tmap_1(C, A, k3_tmap_1(B, A, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_tmap_1)).
% 3.61/1.57  tff(f_138, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 3.61/1.57  tff(f_124, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) => (v1_tsep_1(B, C) & m1_pre_topc(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_tsep_1)).
% 3.61/1.57  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.61/1.57  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.61/1.57  tff(f_100, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 3.61/1.57  tff(f_68, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.61/1.57  tff(f_180, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_tmap_1)).
% 3.61/1.57  tff(c_48, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_245])).
% 3.61/1.57  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_245])).
% 3.61/1.57  tff(c_46, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_245])).
% 3.61/1.57  tff(c_30, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_245])).
% 3.61/1.57  tff(c_52, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_245])).
% 3.61/1.57  tff(c_50, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_245])).
% 3.61/1.57  tff(c_42, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_245])).
% 3.61/1.57  tff(c_34, plain, (v1_tsep_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_245])).
% 3.61/1.57  tff(c_44, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_245])).
% 3.61/1.57  tff(c_385, plain, (![B_308, C_309, A_310]: (r1_tarski(u1_struct_0(B_308), u1_struct_0(C_309)) | ~m1_pre_topc(B_308, C_309) | ~m1_pre_topc(C_309, A_310) | ~m1_pre_topc(B_308, A_310) | ~l1_pre_topc(A_310) | ~v2_pre_topc(A_310))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.61/1.57  tff(c_389, plain, (![B_308]: (r1_tarski(u1_struct_0(B_308), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_308, '#skF_4') | ~m1_pre_topc(B_308, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_385])).
% 3.61/1.57  tff(c_397, plain, (![B_308]: (r1_tarski(u1_struct_0(B_308), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_308, '#skF_4') | ~m1_pre_topc(B_308, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_389])).
% 3.61/1.57  tff(c_437, plain, (![B_319, C_320, A_321]: (v1_tsep_1(B_319, C_320) | ~r1_tarski(u1_struct_0(B_319), u1_struct_0(C_320)) | ~m1_pre_topc(C_320, A_321) | v2_struct_0(C_320) | ~m1_pre_topc(B_319, A_321) | ~v1_tsep_1(B_319, A_321) | ~l1_pre_topc(A_321) | ~v2_pre_topc(A_321) | v2_struct_0(A_321))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.61/1.57  tff(c_443, plain, (![B_308, A_321]: (v1_tsep_1(B_308, '#skF_4') | ~m1_pre_topc('#skF_4', A_321) | v2_struct_0('#skF_4') | ~m1_pre_topc(B_308, A_321) | ~v1_tsep_1(B_308, A_321) | ~l1_pre_topc(A_321) | ~v2_pre_topc(A_321) | v2_struct_0(A_321) | ~m1_pre_topc(B_308, '#skF_4') | ~m1_pre_topc(B_308, '#skF_2'))), inference(resolution, [status(thm)], [c_397, c_437])).
% 3.61/1.57  tff(c_460, plain, (![B_322, A_323]: (v1_tsep_1(B_322, '#skF_4') | ~m1_pre_topc('#skF_4', A_323) | ~m1_pre_topc(B_322, A_323) | ~v1_tsep_1(B_322, A_323) | ~l1_pre_topc(A_323) | ~v2_pre_topc(A_323) | v2_struct_0(A_323) | ~m1_pre_topc(B_322, '#skF_4') | ~m1_pre_topc(B_322, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_44, c_443])).
% 3.61/1.57  tff(c_462, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_460])).
% 3.61/1.57  tff(c_465, plain, (v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_30, c_52, c_50, c_42, c_462])).
% 3.61/1.57  tff(c_466, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_54, c_465])).
% 3.61/1.57  tff(c_28, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_245])).
% 3.61/1.57  tff(c_24, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_245])).
% 3.61/1.57  tff(c_26, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_245])).
% 3.61/1.57  tff(c_72, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26])).
% 3.61/1.57  tff(c_60, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_245])).
% 3.61/1.57  tff(c_68, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_245])).
% 3.61/1.57  tff(c_70, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_68])).
% 3.61/1.57  tff(c_143, plain, (r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_70])).
% 3.61/1.57  tff(c_62, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_7') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_245])).
% 3.61/1.57  tff(c_71, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_6') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_62])).
% 3.61/1.57  tff(c_145, plain, (~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_143, c_71])).
% 3.61/1.57  tff(c_58, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_245])).
% 3.61/1.57  tff(c_56, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_245])).
% 3.61/1.57  tff(c_96, plain, (![B_259, A_260]: (v2_pre_topc(B_259) | ~m1_pre_topc(B_259, A_260) | ~l1_pre_topc(A_260) | ~v2_pre_topc(A_260))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.61/1.57  tff(c_99, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_42, c_96])).
% 3.61/1.57  tff(c_108, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_99])).
% 3.61/1.57  tff(c_77, plain, (![B_257, A_258]: (l1_pre_topc(B_257) | ~m1_pre_topc(B_257, A_258) | ~l1_pre_topc(A_258))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.61/1.57  tff(c_80, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_42, c_77])).
% 3.61/1.57  tff(c_89, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_80])).
% 3.61/1.57  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_245])).
% 3.61/1.57  tff(c_38, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_245])).
% 3.61/1.57  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_245])).
% 3.61/1.57  tff(c_167, plain, (![B_269, C_270, A_271]: (r1_tarski(u1_struct_0(B_269), u1_struct_0(C_270)) | ~m1_pre_topc(B_269, C_270) | ~m1_pre_topc(C_270, A_271) | ~m1_pre_topc(B_269, A_271) | ~l1_pre_topc(A_271) | ~v2_pre_topc(A_271))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.61/1.57  tff(c_171, plain, (![B_269]: (r1_tarski(u1_struct_0(B_269), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_269, '#skF_4') | ~m1_pre_topc(B_269, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_167])).
% 3.61/1.57  tff(c_179, plain, (![B_269]: (r1_tarski(u1_struct_0(B_269), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_269, '#skF_4') | ~m1_pre_topc(B_269, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_171])).
% 3.61/1.57  tff(c_226, plain, (![B_280, C_281, A_282]: (v1_tsep_1(B_280, C_281) | ~r1_tarski(u1_struct_0(B_280), u1_struct_0(C_281)) | ~m1_pre_topc(C_281, A_282) | v2_struct_0(C_281) | ~m1_pre_topc(B_280, A_282) | ~v1_tsep_1(B_280, A_282) | ~l1_pre_topc(A_282) | ~v2_pre_topc(A_282) | v2_struct_0(A_282))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.61/1.57  tff(c_232, plain, (![B_269, A_282]: (v1_tsep_1(B_269, '#skF_4') | ~m1_pre_topc('#skF_4', A_282) | v2_struct_0('#skF_4') | ~m1_pre_topc(B_269, A_282) | ~v1_tsep_1(B_269, A_282) | ~l1_pre_topc(A_282) | ~v2_pre_topc(A_282) | v2_struct_0(A_282) | ~m1_pre_topc(B_269, '#skF_4') | ~m1_pre_topc(B_269, '#skF_2'))), inference(resolution, [status(thm)], [c_179, c_226])).
% 3.61/1.57  tff(c_242, plain, (![B_283, A_284]: (v1_tsep_1(B_283, '#skF_4') | ~m1_pre_topc('#skF_4', A_284) | ~m1_pre_topc(B_283, A_284) | ~v1_tsep_1(B_283, A_284) | ~l1_pre_topc(A_284) | ~v2_pre_topc(A_284) | v2_struct_0(A_284) | ~m1_pre_topc(B_283, '#skF_4') | ~m1_pre_topc(B_283, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_44, c_232])).
% 3.61/1.57  tff(c_244, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_242])).
% 3.61/1.57  tff(c_247, plain, (v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_30, c_52, c_50, c_42, c_244])).
% 3.61/1.57  tff(c_248, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_54, c_247])).
% 3.61/1.57  tff(c_297, plain, (![B_296, E_297, D_294, A_295, C_298]: (k3_tmap_1(A_295, B_296, C_298, D_294, E_297)=k2_partfun1(u1_struct_0(C_298), u1_struct_0(B_296), E_297, u1_struct_0(D_294)) | ~m1_pre_topc(D_294, C_298) | ~m1_subset_1(E_297, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_298), u1_struct_0(B_296)))) | ~v1_funct_2(E_297, u1_struct_0(C_298), u1_struct_0(B_296)) | ~v1_funct_1(E_297) | ~m1_pre_topc(D_294, A_295) | ~m1_pre_topc(C_298, A_295) | ~l1_pre_topc(B_296) | ~v2_pre_topc(B_296) | v2_struct_0(B_296) | ~l1_pre_topc(A_295) | ~v2_pre_topc(A_295) | v2_struct_0(A_295))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.61/1.57  tff(c_299, plain, (![A_295, D_294]: (k3_tmap_1(A_295, '#skF_1', '#skF_4', D_294, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_294)) | ~m1_pre_topc(D_294, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_294, A_295) | ~m1_pre_topc('#skF_4', A_295) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc(A_295) | ~v2_pre_topc(A_295) | v2_struct_0(A_295))), inference(resolution, [status(thm)], [c_36, c_297])).
% 3.61/1.57  tff(c_302, plain, (![A_295, D_294]: (k3_tmap_1(A_295, '#skF_1', '#skF_4', D_294, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_294)) | ~m1_pre_topc(D_294, '#skF_4') | ~m1_pre_topc(D_294, A_295) | ~m1_pre_topc('#skF_4', A_295) | v2_struct_0('#skF_1') | ~l1_pre_topc(A_295) | ~v2_pre_topc(A_295) | v2_struct_0(A_295))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_40, c_38, c_299])).
% 3.61/1.57  tff(c_304, plain, (![A_299, D_300]: (k3_tmap_1(A_299, '#skF_1', '#skF_4', D_300, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_300)) | ~m1_pre_topc(D_300, '#skF_4') | ~m1_pre_topc(D_300, A_299) | ~m1_pre_topc('#skF_4', A_299) | ~l1_pre_topc(A_299) | ~v2_pre_topc(A_299) | v2_struct_0(A_299))), inference(negUnitSimplification, [status(thm)], [c_60, c_302])).
% 3.61/1.57  tff(c_310, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_46, c_304])).
% 3.61/1.57  tff(c_322, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_42, c_30, c_310])).
% 3.61/1.57  tff(c_323, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_54, c_322])).
% 3.61/1.57  tff(c_281, plain, (![A_289, B_290, C_291, D_292]: (k2_partfun1(u1_struct_0(A_289), u1_struct_0(B_290), C_291, u1_struct_0(D_292))=k2_tmap_1(A_289, B_290, C_291, D_292) | ~m1_pre_topc(D_292, A_289) | ~m1_subset_1(C_291, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_289), u1_struct_0(B_290)))) | ~v1_funct_2(C_291, u1_struct_0(A_289), u1_struct_0(B_290)) | ~v1_funct_1(C_291) | ~l1_pre_topc(B_290) | ~v2_pre_topc(B_290) | v2_struct_0(B_290) | ~l1_pre_topc(A_289) | ~v2_pre_topc(A_289) | v2_struct_0(A_289))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.61/1.57  tff(c_283, plain, (![D_292]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_292))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_292) | ~m1_pre_topc(D_292, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_36, c_281])).
% 3.61/1.57  tff(c_286, plain, (![D_292]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_292))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_292) | ~m1_pre_topc(D_292, '#skF_4') | v2_struct_0('#skF_1') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_89, c_58, c_56, c_40, c_38, c_283])).
% 3.61/1.57  tff(c_287, plain, (![D_292]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_292))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_292) | ~m1_pre_topc(D_292, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_44, c_60, c_286])).
% 3.61/1.57  tff(c_332, plain, (k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_323, c_287])).
% 3.61/1.57  tff(c_339, plain, (k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_332])).
% 3.61/1.57  tff(c_344, plain, (r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_339, c_143])).
% 3.61/1.57  tff(c_18, plain, (![C_115, F_129, D_123, B_99, A_67]: (r1_tmap_1(B_99, A_67, C_115, F_129) | ~r1_tmap_1(D_123, A_67, k2_tmap_1(B_99, A_67, C_115, D_123), F_129) | ~m1_subset_1(F_129, u1_struct_0(D_123)) | ~m1_subset_1(F_129, u1_struct_0(B_99)) | ~m1_pre_topc(D_123, B_99) | ~v1_tsep_1(D_123, B_99) | v2_struct_0(D_123) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_99), u1_struct_0(A_67)))) | ~v1_funct_2(C_115, u1_struct_0(B_99), u1_struct_0(A_67)) | ~v1_funct_1(C_115) | ~l1_pre_topc(B_99) | ~v2_pre_topc(B_99) | v2_struct_0(B_99) | ~l1_pre_topc(A_67) | ~v2_pre_topc(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.61/1.57  tff(c_350, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_344, c_18])).
% 3.61/1.57  tff(c_353, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | v2_struct_0('#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_108, c_89, c_40, c_38, c_36, c_248, c_30, c_28, c_72, c_350])).
% 3.61/1.57  tff(c_355, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_44, c_48, c_145, c_353])).
% 3.61/1.57  tff(c_356, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_70])).
% 3.61/1.57  tff(c_585, plain, (![A_342, F_344, C_343, D_341, B_340]: (r1_tmap_1(D_341, A_342, k2_tmap_1(B_340, A_342, C_343, D_341), F_344) | ~r1_tmap_1(B_340, A_342, C_343, F_344) | ~m1_subset_1(F_344, u1_struct_0(D_341)) | ~m1_subset_1(F_344, u1_struct_0(B_340)) | ~m1_pre_topc(D_341, B_340) | ~v1_tsep_1(D_341, B_340) | v2_struct_0(D_341) | ~m1_subset_1(C_343, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_340), u1_struct_0(A_342)))) | ~v1_funct_2(C_343, u1_struct_0(B_340), u1_struct_0(A_342)) | ~v1_funct_1(C_343) | ~l1_pre_topc(B_340) | ~v2_pre_topc(B_340) | v2_struct_0(B_340) | ~l1_pre_topc(A_342) | ~v2_pre_topc(A_342) | v2_struct_0(A_342))), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.61/1.57  tff(c_587, plain, (![D_341, F_344]: (r1_tmap_1(D_341, '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_341), F_344) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', F_344) | ~m1_subset_1(F_344, u1_struct_0(D_341)) | ~m1_subset_1(F_344, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_341, '#skF_4') | ~v1_tsep_1(D_341, '#skF_4') | v2_struct_0(D_341) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_585])).
% 3.61/1.57  tff(c_590, plain, (![D_341, F_344]: (r1_tmap_1(D_341, '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_341), F_344) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', F_344) | ~m1_subset_1(F_344, u1_struct_0(D_341)) | ~m1_subset_1(F_344, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_341, '#skF_4') | ~v1_tsep_1(D_341, '#skF_4') | v2_struct_0(D_341) | v2_struct_0('#skF_4') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_108, c_89, c_40, c_38, c_587])).
% 3.61/1.57  tff(c_601, plain, (![D_346, F_347]: (r1_tmap_1(D_346, '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_346), F_347) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', F_347) | ~m1_subset_1(F_347, u1_struct_0(D_346)) | ~m1_subset_1(F_347, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_346, '#skF_4') | ~v1_tsep_1(D_346, '#skF_4') | v2_struct_0(D_346))), inference(negUnitSimplification, [status(thm)], [c_60, c_44, c_590])).
% 3.61/1.57  tff(c_499, plain, (![A_328, B_329, C_330, D_331]: (k2_partfun1(u1_struct_0(A_328), u1_struct_0(B_329), C_330, u1_struct_0(D_331))=k2_tmap_1(A_328, B_329, C_330, D_331) | ~m1_pre_topc(D_331, A_328) | ~m1_subset_1(C_330, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_328), u1_struct_0(B_329)))) | ~v1_funct_2(C_330, u1_struct_0(A_328), u1_struct_0(B_329)) | ~v1_funct_1(C_330) | ~l1_pre_topc(B_329) | ~v2_pre_topc(B_329) | v2_struct_0(B_329) | ~l1_pre_topc(A_328) | ~v2_pre_topc(A_328) | v2_struct_0(A_328))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.61/1.57  tff(c_501, plain, (![D_331]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_331))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_331) | ~m1_pre_topc(D_331, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_36, c_499])).
% 3.61/1.57  tff(c_504, plain, (![D_331]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_331))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_331) | ~m1_pre_topc(D_331, '#skF_4') | v2_struct_0('#skF_1') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_89, c_58, c_56, c_40, c_38, c_501])).
% 3.61/1.57  tff(c_505, plain, (![D_331]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_331))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_331) | ~m1_pre_topc(D_331, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_44, c_60, c_504])).
% 3.61/1.57  tff(c_506, plain, (![B_334, D_332, E_335, A_333, C_336]: (k3_tmap_1(A_333, B_334, C_336, D_332, E_335)=k2_partfun1(u1_struct_0(C_336), u1_struct_0(B_334), E_335, u1_struct_0(D_332)) | ~m1_pre_topc(D_332, C_336) | ~m1_subset_1(E_335, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_336), u1_struct_0(B_334)))) | ~v1_funct_2(E_335, u1_struct_0(C_336), u1_struct_0(B_334)) | ~v1_funct_1(E_335) | ~m1_pre_topc(D_332, A_333) | ~m1_pre_topc(C_336, A_333) | ~l1_pre_topc(B_334) | ~v2_pre_topc(B_334) | v2_struct_0(B_334) | ~l1_pre_topc(A_333) | ~v2_pre_topc(A_333) | v2_struct_0(A_333))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.61/1.57  tff(c_508, plain, (![A_333, D_332]: (k3_tmap_1(A_333, '#skF_1', '#skF_4', D_332, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_332)) | ~m1_pre_topc(D_332, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_332, A_333) | ~m1_pre_topc('#skF_4', A_333) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc(A_333) | ~v2_pre_topc(A_333) | v2_struct_0(A_333))), inference(resolution, [status(thm)], [c_36, c_506])).
% 3.61/1.57  tff(c_511, plain, (![A_333, D_332]: (k3_tmap_1(A_333, '#skF_1', '#skF_4', D_332, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_332)) | ~m1_pre_topc(D_332, '#skF_4') | ~m1_pre_topc(D_332, A_333) | ~m1_pre_topc('#skF_4', A_333) | v2_struct_0('#skF_1') | ~l1_pre_topc(A_333) | ~v2_pre_topc(A_333) | v2_struct_0(A_333))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_40, c_38, c_508])).
% 3.61/1.57  tff(c_522, plain, (![A_338, D_339]: (k3_tmap_1(A_338, '#skF_1', '#skF_4', D_339, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_339)) | ~m1_pre_topc(D_339, '#skF_4') | ~m1_pre_topc(D_339, A_338) | ~m1_pre_topc('#skF_4', A_338) | ~l1_pre_topc(A_338) | ~v2_pre_topc(A_338) | v2_struct_0(A_338))), inference(negUnitSimplification, [status(thm)], [c_60, c_511])).
% 3.61/1.57  tff(c_528, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_46, c_522])).
% 3.61/1.57  tff(c_540, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_42, c_30, c_528])).
% 3.61/1.57  tff(c_541, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_54, c_540])).
% 3.61/1.57  tff(c_553, plain, (k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_505, c_541])).
% 3.61/1.57  tff(c_559, plain, (k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_553])).
% 3.61/1.57  tff(c_357, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_70])).
% 3.61/1.57  tff(c_563, plain, (~r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_559, c_357])).
% 3.61/1.57  tff(c_604, plain, (~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_601, c_563])).
% 3.61/1.57  tff(c_607, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_466, c_30, c_28, c_72, c_356, c_604])).
% 3.61/1.57  tff(c_609, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_607])).
% 3.61/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.57  
% 3.61/1.57  Inference rules
% 3.61/1.57  ----------------------
% 3.61/1.57  #Ref     : 0
% 3.61/1.57  #Sup     : 100
% 3.61/1.57  #Fact    : 0
% 3.61/1.57  #Define  : 0
% 3.61/1.57  #Split   : 7
% 3.61/1.57  #Chain   : 0
% 3.61/1.57  #Close   : 0
% 3.61/1.57  
% 3.61/1.57  Ordering : KBO
% 3.61/1.57  
% 3.61/1.57  Simplification rules
% 3.61/1.57  ----------------------
% 3.61/1.57  #Subsume      : 19
% 3.61/1.57  #Demod        : 214
% 3.61/1.57  #Tautology    : 42
% 3.61/1.57  #SimpNegUnit  : 32
% 3.61/1.57  #BackRed      : 4
% 3.61/1.57  
% 3.61/1.57  #Partial instantiations: 0
% 3.61/1.57  #Strategies tried      : 1
% 3.61/1.57  
% 3.61/1.57  Timing (in seconds)
% 3.61/1.57  ----------------------
% 3.61/1.57  Preprocessing        : 0.40
% 3.61/1.57  Parsing              : 0.21
% 3.61/1.57  CNF conversion       : 0.05
% 3.61/1.57  Main loop            : 0.33
% 3.61/1.57  Inferencing          : 0.11
% 3.61/1.57  Reduction            : 0.11
% 3.61/1.57  Demodulation         : 0.08
% 3.61/1.57  BG Simplification    : 0.02
% 3.61/1.57  Subsumption          : 0.07
% 3.61/1.57  Abstraction          : 0.01
% 3.61/1.57  MUC search           : 0.00
% 3.61/1.57  Cooper               : 0.00
% 3.61/1.57  Total                : 0.78
% 3.61/1.57  Index Insertion      : 0.00
% 3.61/1.57  Index Deletion       : 0.00
% 3.61/1.57  Index Matching       : 0.00
% 3.61/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
