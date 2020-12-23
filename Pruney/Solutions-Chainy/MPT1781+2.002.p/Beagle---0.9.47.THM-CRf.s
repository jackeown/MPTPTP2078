%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:45 EST 2020

% Result     : Theorem 6.86s
% Output     : CNFRefutation 7.20s
% Verified   : 
% Statistics : Number of formulae       :  279 (6238 expanded)
%              Number of leaves         :   45 (2308 expanded)
%              Depth                    :   30
%              Number of atoms          : 1139 (39600 expanded)
%              Number of equality atoms :  134 (3105 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_funct_2 > k2_tmap_1 > k2_partfun1 > k4_tmap_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k4_tmap_1,type,(
    k4_tmap_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_303,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
               => ( ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r2_hidden(D,u1_struct_0(B))
                       => D = k1_funct_1(C,D) ) )
                 => r2_funct_2(u1_struct_0(B),u1_struct_0(A),k4_tmap_1(A,B),C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_tmap_1)).

tff(f_188,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_funct_1(k4_tmap_1(A,B))
        & v1_funct_2(k4_tmap_1(A,B),u1_struct_0(B),u1_struct_0(A))
        & m1_subset_1(k4_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_tmap_1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_111,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_122,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_209,axiom,(
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

tff(f_115,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_102,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_funct_2)).

tff(f_130,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_195,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_146,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => m1_subset_1(C,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_173,axiom,(
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

tff(f_253,axiom,(
    ! [A] :
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
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,u1_struct_0(B),u1_struct_0(A))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(A))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(A)))) )
                     => ( ! [F] :
                            ( m1_subset_1(F,u1_struct_0(B))
                           => ( r2_hidden(F,u1_struct_0(C))
                             => k3_funct_2(u1_struct_0(B),u1_struct_0(A),D,F) = k1_funct_1(E,F) ) )
                       => r2_funct_2(u1_struct_0(C),u1_struct_0(A),k2_tmap_1(B,A,D,C),E) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tmap_1)).

tff(f_273,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(C,u1_struct_0(B))
               => k1_funct_1(k4_tmap_1(A,B),C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_tmap_1)).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_72,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_70,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_66,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_36,plain,(
    ! [A_107,B_108] :
      ( m1_subset_1(k4_tmap_1(A_107,B_108),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_108),u1_struct_0(A_107))))
      | ~ m1_pre_topc(B_108,A_107)
      | ~ l1_pre_topc(A_107)
      | ~ v2_pre_topc(A_107)
      | v2_struct_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_64,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_62,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_60,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_116,plain,(
    ! [A_222,B_223,D_224] :
      ( r2_funct_2(A_222,B_223,D_224,D_224)
      | ~ m1_subset_1(D_224,k1_zfmisc_1(k2_zfmisc_1(A_222,B_223)))
      | ~ v1_funct_2(D_224,A_222,B_223)
      | ~ v1_funct_1(D_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_118,plain,
    ( r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6','#skF_6')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_116])).

tff(c_121,plain,(
    r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_118])).

tff(c_40,plain,(
    ! [A_107,B_108] :
      ( v1_funct_1(k4_tmap_1(A_107,B_108))
      | ~ m1_pre_topc(B_108,A_107)
      | ~ l1_pre_topc(A_107)
      | ~ v2_pre_topc(A_107)
      | v2_struct_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_99,plain,(
    ! [B_210,A_211] :
      ( v2_pre_topc(B_210)
      | ~ m1_pre_topc(B_210,A_211)
      | ~ l1_pre_topc(A_211)
      | ~ v2_pre_topc(A_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_102,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_99])).

tff(c_105,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_102])).

tff(c_85,plain,(
    ! [B_206,A_207] :
      ( l1_pre_topc(B_206)
      | ~ m1_pre_topc(B_206,A_207)
      | ~ l1_pre_topc(A_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_88,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_85])).

tff(c_91,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_88])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_150,plain,(
    ! [B_230,C_231,A_232] :
      ( m1_pre_topc(B_230,C_231)
      | ~ r1_tarski(u1_struct_0(B_230),u1_struct_0(C_231))
      | ~ m1_pre_topc(C_231,A_232)
      | ~ m1_pre_topc(B_230,A_232)
      | ~ l1_pre_topc(A_232)
      | ~ v2_pre_topc(A_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_158,plain,(
    ! [B_233,A_234] :
      ( m1_pre_topc(B_233,B_233)
      | ~ m1_pre_topc(B_233,A_234)
      | ~ l1_pre_topc(A_234)
      | ~ v2_pre_topc(A_234) ) ),
    inference(resolution,[status(thm)],[c_10,c_150])).

tff(c_160,plain,
    ( m1_pre_topc('#skF_5','#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_158])).

tff(c_163,plain,(
    m1_pre_topc('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_160])).

tff(c_26,plain,(
    ! [A_80] :
      ( l1_struct_0(A_80)
      | ~ l1_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_280,plain,(
    ! [D_268,E_267,B_266,C_269,A_270] :
      ( m1_subset_1('#skF_2'(B_266,E_267,D_268,C_269,A_270),A_270)
      | k2_partfun1(A_270,B_266,C_269,D_268) = E_267
      | ~ m1_subset_1(E_267,k1_zfmisc_1(k2_zfmisc_1(D_268,B_266)))
      | ~ v1_funct_2(E_267,D_268,B_266)
      | ~ v1_funct_1(E_267)
      | ~ m1_subset_1(D_268,k1_zfmisc_1(A_270))
      | v1_xboole_0(D_268)
      | ~ m1_subset_1(C_269,k1_zfmisc_1(k2_zfmisc_1(A_270,B_266)))
      | ~ v1_funct_2(C_269,A_270,B_266)
      | ~ v1_funct_1(C_269)
      | v1_xboole_0(B_266)
      | v1_xboole_0(A_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_284,plain,(
    ! [C_269,A_270] :
      ( m1_subset_1('#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),C_269,A_270),A_270)
      | k2_partfun1(A_270,u1_struct_0('#skF_4'),C_269,u1_struct_0('#skF_5')) = '#skF_6'
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_270))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_269,k1_zfmisc_1(k2_zfmisc_1(A_270,u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_269,A_270,u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_269)
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | v1_xboole_0(A_270) ) ),
    inference(resolution,[status(thm)],[c_60,c_280])).

tff(c_288,plain,(
    ! [C_269,A_270] :
      ( m1_subset_1('#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),C_269,A_270),A_270)
      | k2_partfun1(A_270,u1_struct_0('#skF_4'),C_269,u1_struct_0('#skF_5')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_270))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_269,k1_zfmisc_1(k2_zfmisc_1(A_270,u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_269,A_270,u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_269)
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | v1_xboole_0(A_270) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_284])).

tff(c_289,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_288])).

tff(c_30,plain,(
    ! [A_84] :
      ( ~ v1_xboole_0(u1_struct_0(A_84))
      | ~ l1_struct_0(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_292,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_289,c_30])).

tff(c_295,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_292])).

tff(c_298,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_295])).

tff(c_302,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_298])).

tff(c_303,plain,(
    ! [C_269,A_270] :
      ( v1_xboole_0(u1_struct_0('#skF_5'))
      | m1_subset_1('#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),C_269,A_270),A_270)
      | k2_partfun1(A_270,u1_struct_0('#skF_4'),C_269,u1_struct_0('#skF_5')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_270))
      | ~ m1_subset_1(C_269,k1_zfmisc_1(k2_zfmisc_1(A_270,u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_269,A_270,u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_269)
      | v1_xboole_0(A_270) ) ),
    inference(splitRight,[status(thm)],[c_288])).

tff(c_305,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_303])).

tff(c_308,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_305,c_30])).

tff(c_311,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_308])).

tff(c_324,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_311])).

tff(c_328,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_324])).

tff(c_330,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_303])).

tff(c_304,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_288])).

tff(c_42,plain,(
    ! [B_111,A_109] :
      ( m1_subset_1(u1_struct_0(B_111),k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ m1_pre_topc(B_111,A_109)
      | ~ l1_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_331,plain,(
    ! [C_276,A_277] :
      ( m1_subset_1('#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),C_276,A_277),A_277)
      | k2_partfun1(A_277,u1_struct_0('#skF_4'),C_276,u1_struct_0('#skF_5')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_277))
      | ~ m1_subset_1(C_276,k1_zfmisc_1(k2_zfmisc_1(A_277,u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_276,A_277,u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_276)
      | v1_xboole_0(A_277) ) ),
    inference(splitRight,[status(thm)],[c_303])).

tff(c_32,plain,(
    ! [C_91,A_85,B_89] :
      ( m1_subset_1(C_91,u1_struct_0(A_85))
      | ~ m1_subset_1(C_91,u1_struct_0(B_89))
      | ~ m1_pre_topc(B_89,A_85)
      | v2_struct_0(B_89)
      | ~ l1_pre_topc(A_85)
      | v2_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_354,plain,(
    ! [C_276,B_89,A_85] :
      ( m1_subset_1('#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),C_276,u1_struct_0(B_89)),u1_struct_0(A_85))
      | ~ m1_pre_topc(B_89,A_85)
      | v2_struct_0(B_89)
      | ~ l1_pre_topc(A_85)
      | v2_struct_0(A_85)
      | k2_partfun1(u1_struct_0(B_89),u1_struct_0('#skF_4'),C_276,u1_struct_0('#skF_5')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0(B_89)))
      | ~ m1_subset_1(C_276,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_89),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_276,u1_struct_0(B_89),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_276)
      | v1_xboole_0(u1_struct_0(B_89)) ) ),
    inference(resolution,[status(thm)],[c_331,c_32])).

tff(c_362,plain,(
    ! [A_285,B_281,C_284,E_282,D_283] :
      ( r2_hidden('#skF_2'(B_281,E_282,D_283,C_284,A_285),D_283)
      | k2_partfun1(A_285,B_281,C_284,D_283) = E_282
      | ~ m1_subset_1(E_282,k1_zfmisc_1(k2_zfmisc_1(D_283,B_281)))
      | ~ v1_funct_2(E_282,D_283,B_281)
      | ~ v1_funct_1(E_282)
      | ~ m1_subset_1(D_283,k1_zfmisc_1(A_285))
      | v1_xboole_0(D_283)
      | ~ m1_subset_1(C_284,k1_zfmisc_1(k2_zfmisc_1(A_285,B_281)))
      | ~ v1_funct_2(C_284,A_285,B_281)
      | ~ v1_funct_1(C_284)
      | v1_xboole_0(B_281)
      | v1_xboole_0(A_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_369,plain,(
    ! [C_284,A_285] :
      ( r2_hidden('#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),C_284,A_285),u1_struct_0('#skF_5'))
      | k2_partfun1(A_285,u1_struct_0('#skF_4'),C_284,u1_struct_0('#skF_5')) = '#skF_6'
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_285))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_284,k1_zfmisc_1(k2_zfmisc_1(A_285,u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_284,A_285,u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_284)
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | v1_xboole_0(A_285) ) ),
    inference(resolution,[status(thm)],[c_60,c_362])).

tff(c_374,plain,(
    ! [C_284,A_285] :
      ( r2_hidden('#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),C_284,A_285),u1_struct_0('#skF_5'))
      | k2_partfun1(A_285,u1_struct_0('#skF_4'),C_284,u1_struct_0('#skF_5')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_285))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_284,k1_zfmisc_1(k2_zfmisc_1(A_285,u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_284,A_285,u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_284)
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | v1_xboole_0(A_285) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_369])).

tff(c_376,plain,(
    ! [C_286,A_287] :
      ( r2_hidden('#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),C_286,A_287),u1_struct_0('#skF_5'))
      | k2_partfun1(A_287,u1_struct_0('#skF_4'),C_286,u1_struct_0('#skF_5')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_287))
      | ~ m1_subset_1(C_286,k1_zfmisc_1(k2_zfmisc_1(A_287,u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_286,A_287,u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_286)
      | v1_xboole_0(A_287) ) ),
    inference(negUnitSimplification,[status(thm)],[c_304,c_330,c_374])).

tff(c_58,plain,(
    ! [D_199] :
      ( k1_funct_1('#skF_6',D_199) = D_199
      | ~ r2_hidden(D_199,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(D_199,u1_struct_0('#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_396,plain,(
    ! [C_297,A_298] :
      ( k1_funct_1('#skF_6','#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),C_297,A_298)) = '#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),C_297,A_298)
      | ~ m1_subset_1('#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),C_297,A_298),u1_struct_0('#skF_4'))
      | k2_partfun1(A_298,u1_struct_0('#skF_4'),C_297,u1_struct_0('#skF_5')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_298))
      | ~ m1_subset_1(C_297,k1_zfmisc_1(k2_zfmisc_1(A_298,u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_297,A_298,u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_297)
      | v1_xboole_0(A_298) ) ),
    inference(resolution,[status(thm)],[c_376,c_58])).

tff(c_400,plain,(
    ! [C_276,B_89] :
      ( k1_funct_1('#skF_6','#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),C_276,u1_struct_0(B_89))) = '#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),C_276,u1_struct_0(B_89))
      | ~ m1_pre_topc(B_89,'#skF_4')
      | v2_struct_0(B_89)
      | ~ l1_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | k2_partfun1(u1_struct_0(B_89),u1_struct_0('#skF_4'),C_276,u1_struct_0('#skF_5')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0(B_89)))
      | ~ m1_subset_1(C_276,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_89),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_276,u1_struct_0(B_89),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_276)
      | v1_xboole_0(u1_struct_0(B_89)) ) ),
    inference(resolution,[status(thm)],[c_354,c_396])).

tff(c_407,plain,(
    ! [C_276,B_89] :
      ( k1_funct_1('#skF_6','#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),C_276,u1_struct_0(B_89))) = '#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),C_276,u1_struct_0(B_89))
      | ~ m1_pre_topc(B_89,'#skF_4')
      | v2_struct_0(B_89)
      | v2_struct_0('#skF_4')
      | k2_partfun1(u1_struct_0(B_89),u1_struct_0('#skF_4'),C_276,u1_struct_0('#skF_5')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0(B_89)))
      | ~ m1_subset_1(C_276,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_89),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_276,u1_struct_0(B_89),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_276)
      | v1_xboole_0(u1_struct_0(B_89)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_400])).

tff(c_1374,plain,(
    ! [C_430,B_431] :
      ( k1_funct_1('#skF_6','#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),C_430,u1_struct_0(B_431))) = '#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),C_430,u1_struct_0(B_431))
      | ~ m1_pre_topc(B_431,'#skF_4')
      | v2_struct_0(B_431)
      | k2_partfun1(u1_struct_0(B_431),u1_struct_0('#skF_4'),C_430,u1_struct_0('#skF_5')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0(B_431)))
      | ~ m1_subset_1(C_430,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_431),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_430,u1_struct_0(B_431),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_430)
      | v1_xboole_0(u1_struct_0(B_431)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_407])).

tff(c_1388,plain,
    ( k1_funct_1('#skF_6','#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5'))) = '#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | v2_struct_0('#skF_5')
    | k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_6'
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_60,c_1374])).

tff(c_1400,plain,
    ( k1_funct_1('#skF_6','#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5'))) = '#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_5')
    | k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_6'
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_66,c_1388])).

tff(c_1401,plain,
    ( k1_funct_1('#skF_6','#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5'))) = '#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5'))
    | k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_6'
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_330,c_68,c_1400])).

tff(c_1402,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_1401])).

tff(c_1405,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_1402])).

tff(c_1409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_163,c_1405])).

tff(c_1411,plain,(
    m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_1401])).

tff(c_12,plain,(
    ! [A_7,B_8,C_9,D_10] :
      ( k3_funct_2(A_7,B_8,C_9,D_10) = k1_funct_1(C_9,D_10)
      | ~ m1_subset_1(D_10,A_7)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8)))
      | ~ v1_funct_2(C_9,A_7,B_8)
      | ~ v1_funct_1(C_9)
      | v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1691,plain,(
    ! [A_470,B_471,C_472,C_473] :
      ( k3_funct_2(A_470,B_471,C_472,'#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),C_473,A_470)) = k1_funct_1(C_472,'#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),C_473,A_470))
      | ~ m1_subset_1(C_472,k1_zfmisc_1(k2_zfmisc_1(A_470,B_471)))
      | ~ v1_funct_2(C_472,A_470,B_471)
      | ~ v1_funct_1(C_472)
      | k2_partfun1(A_470,u1_struct_0('#skF_4'),C_473,u1_struct_0('#skF_5')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_470))
      | ~ m1_subset_1(C_473,k1_zfmisc_1(k2_zfmisc_1(A_470,u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_473,A_470,u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_473)
      | v1_xboole_0(A_470) ) ),
    inference(resolution,[status(thm)],[c_331,c_12])).

tff(c_1704,plain,(
    ! [B_471,C_472] :
      ( k3_funct_2(u1_struct_0('#skF_5'),B_471,C_472,'#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5'))) = k1_funct_1(C_472,'#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5')))
      | ~ m1_subset_1(C_472,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),B_471)))
      | ~ v1_funct_2(C_472,u1_struct_0('#skF_5'),B_471)
      | ~ v1_funct_1(C_472)
      | k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_60,c_1691])).

tff(c_1717,plain,(
    ! [B_471,C_472] :
      ( k3_funct_2(u1_struct_0('#skF_5'),B_471,C_472,'#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5'))) = k1_funct_1(C_472,'#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5')))
      | ~ m1_subset_1(C_472,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),B_471)))
      | ~ v1_funct_2(C_472,u1_struct_0('#skF_5'),B_471)
      | ~ v1_funct_1(C_472)
      | k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_6'
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_1411,c_1704])).

tff(c_1718,plain,(
    ! [B_471,C_472] :
      ( k3_funct_2(u1_struct_0('#skF_5'),B_471,C_472,'#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5'))) = k1_funct_1(C_472,'#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5')))
      | ~ m1_subset_1(C_472,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),B_471)))
      | ~ v1_funct_2(C_472,u1_struct_0('#skF_5'),B_471)
      | ~ v1_funct_1(C_472)
      | k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_6' ) ),
    inference(negUnitSimplification,[status(thm)],[c_330,c_1717])).

tff(c_1719,plain,(
    k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1718])).

tff(c_252,plain,(
    ! [A_258,B_259,C_260,D_261] :
      ( k2_partfun1(u1_struct_0(A_258),u1_struct_0(B_259),C_260,u1_struct_0(D_261)) = k2_tmap_1(A_258,B_259,C_260,D_261)
      | ~ m1_pre_topc(D_261,A_258)
      | ~ m1_subset_1(C_260,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_258),u1_struct_0(B_259))))
      | ~ v1_funct_2(C_260,u1_struct_0(A_258),u1_struct_0(B_259))
      | ~ v1_funct_1(C_260)
      | ~ l1_pre_topc(B_259)
      | ~ v2_pre_topc(B_259)
      | v2_struct_0(B_259)
      | ~ l1_pre_topc(A_258)
      | ~ v2_pre_topc(A_258)
      | v2_struct_0(A_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_256,plain,(
    ! [D_261] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',u1_struct_0(D_261)) = k2_tmap_1('#skF_5','#skF_4','#skF_6',D_261)
      | ~ m1_pre_topc(D_261,'#skF_5')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_60,c_252])).

tff(c_260,plain,(
    ! [D_261] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',u1_struct_0(D_261)) = k2_tmap_1('#skF_5','#skF_4','#skF_6',D_261)
      | ~ m1_pre_topc(D_261,'#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_91,c_72,c_70,c_64,c_62,c_256])).

tff(c_261,plain,(
    ! [D_261] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',u1_struct_0(D_261)) = k2_tmap_1('#skF_5','#skF_4','#skF_6',D_261)
      | ~ m1_pre_topc(D_261,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_74,c_260])).

tff(c_1727,plain,
    ( k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_5') = '#skF_6'
    | ~ m1_pre_topc('#skF_5','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1719,c_261])).

tff(c_1734,plain,(
    k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_1727])).

tff(c_960,plain,(
    ! [C_378,B_379] :
      ( k1_funct_1('#skF_6','#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),C_378,u1_struct_0(B_379))) = '#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),C_378,u1_struct_0(B_379))
      | ~ m1_pre_topc(B_379,'#skF_4')
      | v2_struct_0(B_379)
      | k2_partfun1(u1_struct_0(B_379),u1_struct_0('#skF_4'),C_378,u1_struct_0('#skF_5')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0(B_379)))
      | ~ m1_subset_1(C_378,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_379),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_378,u1_struct_0(B_379),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_378)
      | v1_xboole_0(u1_struct_0(B_379)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_407])).

tff(c_971,plain,
    ( k1_funct_1('#skF_6','#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5'))) = '#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | v2_struct_0('#skF_5')
    | k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_6'
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_60,c_960])).

tff(c_979,plain,
    ( k1_funct_1('#skF_6','#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5'))) = '#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_5')
    | k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_6'
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_66,c_971])).

tff(c_980,plain,
    ( k1_funct_1('#skF_6','#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5'))) = '#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5'))
    | k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_6'
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_330,c_68,c_979])).

tff(c_981,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_980])).

tff(c_984,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_981])).

tff(c_988,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_163,c_984])).

tff(c_990,plain,(
    m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_980])).

tff(c_1215,plain,(
    ! [A_412,B_413,C_414,C_415] :
      ( k3_funct_2(A_412,B_413,C_414,'#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),C_415,A_412)) = k1_funct_1(C_414,'#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),C_415,A_412))
      | ~ m1_subset_1(C_414,k1_zfmisc_1(k2_zfmisc_1(A_412,B_413)))
      | ~ v1_funct_2(C_414,A_412,B_413)
      | ~ v1_funct_1(C_414)
      | k2_partfun1(A_412,u1_struct_0('#skF_4'),C_415,u1_struct_0('#skF_5')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_412))
      | ~ m1_subset_1(C_415,k1_zfmisc_1(k2_zfmisc_1(A_412,u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_415,A_412,u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_415)
      | v1_xboole_0(A_412) ) ),
    inference(resolution,[status(thm)],[c_331,c_12])).

tff(c_1226,plain,(
    ! [B_413,C_414] :
      ( k3_funct_2(u1_struct_0('#skF_5'),B_413,C_414,'#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5'))) = k1_funct_1(C_414,'#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5')))
      | ~ m1_subset_1(C_414,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),B_413)))
      | ~ v1_funct_2(C_414,u1_struct_0('#skF_5'),B_413)
      | ~ v1_funct_1(C_414)
      | k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_60,c_1215])).

tff(c_1235,plain,(
    ! [B_413,C_414] :
      ( k3_funct_2(u1_struct_0('#skF_5'),B_413,C_414,'#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5'))) = k1_funct_1(C_414,'#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5')))
      | ~ m1_subset_1(C_414,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),B_413)))
      | ~ v1_funct_2(C_414,u1_struct_0('#skF_5'),B_413)
      | ~ v1_funct_1(C_414)
      | k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_6'
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_990,c_1226])).

tff(c_1236,plain,(
    ! [B_413,C_414] :
      ( k3_funct_2(u1_struct_0('#skF_5'),B_413,C_414,'#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5'))) = k1_funct_1(C_414,'#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5')))
      | ~ m1_subset_1(C_414,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),B_413)))
      | ~ v1_funct_2(C_414,u1_struct_0('#skF_5'),B_413)
      | ~ v1_funct_1(C_414)
      | k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_6' ) ),
    inference(negUnitSimplification,[status(thm)],[c_330,c_1235])).

tff(c_1237,plain,(
    k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1236])).

tff(c_1241,plain,
    ( k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_5') = '#skF_6'
    | ~ m1_pre_topc('#skF_5','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1237,c_261])).

tff(c_1248,plain,(
    k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_1241])).

tff(c_545,plain,(
    ! [C_318,B_319] :
      ( k1_funct_1('#skF_6','#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),C_318,u1_struct_0(B_319))) = '#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),C_318,u1_struct_0(B_319))
      | ~ m1_pre_topc(B_319,'#skF_4')
      | v2_struct_0(B_319)
      | k2_partfun1(u1_struct_0(B_319),u1_struct_0('#skF_4'),C_318,u1_struct_0('#skF_5')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0(B_319)))
      | ~ m1_subset_1(C_318,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_319),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_318,u1_struct_0(B_319),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_318)
      | v1_xboole_0(u1_struct_0(B_319)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_407])).

tff(c_556,plain,
    ( k1_funct_1('#skF_6','#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5'))) = '#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | v2_struct_0('#skF_5')
    | k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_6'
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_60,c_545])).

tff(c_564,plain,
    ( k1_funct_1('#skF_6','#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5'))) = '#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_5')
    | k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_6'
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_66,c_556])).

tff(c_565,plain,
    ( k1_funct_1('#skF_6','#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5'))) = '#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5'))
    | k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_6'
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_330,c_68,c_564])).

tff(c_567,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_565])).

tff(c_570,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_567])).

tff(c_574,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_163,c_570])).

tff(c_576,plain,(
    m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_565])).

tff(c_789,plain,(
    ! [A_355,B_356,C_357,C_358] :
      ( k3_funct_2(A_355,B_356,C_357,'#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),C_358,A_355)) = k1_funct_1(C_357,'#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),C_358,A_355))
      | ~ m1_subset_1(C_357,k1_zfmisc_1(k2_zfmisc_1(A_355,B_356)))
      | ~ v1_funct_2(C_357,A_355,B_356)
      | ~ v1_funct_1(C_357)
      | k2_partfun1(A_355,u1_struct_0('#skF_4'),C_358,u1_struct_0('#skF_5')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_355))
      | ~ m1_subset_1(C_358,k1_zfmisc_1(k2_zfmisc_1(A_355,u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_358,A_355,u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_358)
      | v1_xboole_0(A_355) ) ),
    inference(resolution,[status(thm)],[c_331,c_12])).

tff(c_800,plain,(
    ! [B_356,C_357] :
      ( k3_funct_2(u1_struct_0('#skF_5'),B_356,C_357,'#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5'))) = k1_funct_1(C_357,'#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5')))
      | ~ m1_subset_1(C_357,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),B_356)))
      | ~ v1_funct_2(C_357,u1_struct_0('#skF_5'),B_356)
      | ~ v1_funct_1(C_357)
      | k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_60,c_789])).

tff(c_809,plain,(
    ! [B_356,C_357] :
      ( k3_funct_2(u1_struct_0('#skF_5'),B_356,C_357,'#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5'))) = k1_funct_1(C_357,'#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5')))
      | ~ m1_subset_1(C_357,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),B_356)))
      | ~ v1_funct_2(C_357,u1_struct_0('#skF_5'),B_356)
      | ~ v1_funct_1(C_357)
      | k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_6'
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_576,c_800])).

tff(c_810,plain,(
    ! [B_356,C_357] :
      ( k3_funct_2(u1_struct_0('#skF_5'),B_356,C_357,'#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5'))) = k1_funct_1(C_357,'#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5')))
      | ~ m1_subset_1(C_357,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),B_356)))
      | ~ v1_funct_2(C_357,u1_struct_0('#skF_5'),B_356)
      | ~ v1_funct_1(C_357)
      | k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_6' ) ),
    inference(negUnitSimplification,[status(thm)],[c_330,c_809])).

tff(c_811,plain,(
    k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_810])).

tff(c_815,plain,
    ( k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_5') = '#skF_6'
    | ~ m1_pre_topc('#skF_5','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_811,c_261])).

tff(c_822,plain,(
    k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_815])).

tff(c_412,plain,(
    ! [B_301,C_299,D_303,E_302,A_300] :
      ( m1_subset_1('#skF_3'(C_299,A_300,B_301,E_302,D_303),u1_struct_0(B_301))
      | r2_funct_2(u1_struct_0(C_299),u1_struct_0(A_300),k2_tmap_1(B_301,A_300,D_303,C_299),E_302)
      | ~ m1_subset_1(E_302,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_299),u1_struct_0(A_300))))
      | ~ v1_funct_2(E_302,u1_struct_0(C_299),u1_struct_0(A_300))
      | ~ v1_funct_1(E_302)
      | ~ m1_subset_1(D_303,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_301),u1_struct_0(A_300))))
      | ~ v1_funct_2(D_303,u1_struct_0(B_301),u1_struct_0(A_300))
      | ~ v1_funct_1(D_303)
      | ~ m1_pre_topc(C_299,B_301)
      | v2_struct_0(C_299)
      | ~ l1_pre_topc(B_301)
      | ~ v2_pre_topc(B_301)
      | v2_struct_0(B_301)
      | ~ l1_pre_topc(A_300)
      | ~ v2_pre_topc(A_300)
      | v2_struct_0(A_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_419,plain,(
    ! [B_301,D_303] :
      ( m1_subset_1('#skF_3'('#skF_5','#skF_4',B_301,'#skF_6',D_303),u1_struct_0(B_301))
      | r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1(B_301,'#skF_4',D_303,'#skF_5'),'#skF_6')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(D_303,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_301),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(D_303,u1_struct_0(B_301),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(D_303)
      | ~ m1_pre_topc('#skF_5',B_301)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(B_301)
      | ~ v2_pre_topc(B_301)
      | v2_struct_0(B_301)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_412])).

tff(c_424,plain,(
    ! [B_301,D_303] :
      ( m1_subset_1('#skF_3'('#skF_5','#skF_4',B_301,'#skF_6',D_303),u1_struct_0(B_301))
      | r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1(B_301,'#skF_4',D_303,'#skF_5'),'#skF_6')
      | ~ m1_subset_1(D_303,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_301),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(D_303,u1_struct_0(B_301),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(D_303)
      | ~ m1_pre_topc('#skF_5',B_301)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(B_301)
      | ~ v2_pre_topc(B_301)
      | v2_struct_0(B_301)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_64,c_62,c_419])).

tff(c_426,plain,(
    ! [B_304,D_305] :
      ( m1_subset_1('#skF_3'('#skF_5','#skF_4',B_304,'#skF_6',D_305),u1_struct_0(B_304))
      | r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1(B_304,'#skF_4',D_305,'#skF_5'),'#skF_6')
      | ~ m1_subset_1(D_305,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_304),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(D_305,u1_struct_0(B_304),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(D_305)
      | ~ m1_pre_topc('#skF_5',B_304)
      | ~ l1_pre_topc(B_304)
      | ~ v2_pre_topc(B_304)
      | v2_struct_0(B_304) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_424])).

tff(c_434,plain,
    ( m1_subset_1('#skF_3'('#skF_5','#skF_4','#skF_5','#skF_6','#skF_6'),u1_struct_0('#skF_5'))
    | r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_5'),'#skF_6')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_426])).

tff(c_442,plain,
    ( m1_subset_1('#skF_3'('#skF_5','#skF_4','#skF_5','#skF_6','#skF_6'),u1_struct_0('#skF_5'))
    | r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_5'),'#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_91,c_163,c_64,c_62,c_434])).

tff(c_443,plain,
    ( m1_subset_1('#skF_3'('#skF_5','#skF_4','#skF_5','#skF_6','#skF_6'),u1_struct_0('#skF_5'))
    | r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_442])).

tff(c_444,plain,(
    r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_443])).

tff(c_16,plain,(
    ! [D_14,C_13,A_11,B_12] :
      ( D_14 = C_13
      | ~ r2_funct_2(A_11,B_12,C_13,D_14)
      | ~ m1_subset_1(D_14,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12)))
      | ~ v1_funct_2(D_14,A_11,B_12)
      | ~ v1_funct_1(D_14)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12)))
      | ~ v1_funct_2(C_13,A_11,B_12)
      | ~ v1_funct_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_446,plain,
    ( k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_5') = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1(k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_5')) ),
    inference(resolution,[status(thm)],[c_444,c_16])).

tff(c_449,plain,
    ( k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_5') = '#skF_6'
    | ~ m1_subset_1(k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_446])).

tff(c_462,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_449])).

tff(c_858,plain,(
    ~ v1_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_822,c_462])).

tff(c_862,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_858])).

tff(c_864,plain,(
    k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5')) != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_810])).

tff(c_870,plain,(
    ! [B_362,C_363] :
      ( k3_funct_2(u1_struct_0('#skF_5'),B_362,C_363,'#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5'))) = k1_funct_1(C_363,'#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5')))
      | ~ m1_subset_1(C_363,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),B_362)))
      | ~ v1_funct_2(C_363,u1_struct_0('#skF_5'),B_362)
      | ~ v1_funct_1(C_363) ) ),
    inference(splitRight,[status(thm)],[c_810])).

tff(c_18,plain,(
    ! [A_15,B_47,C_63,E_75,D_71] :
      ( k3_funct_2(A_15,B_47,C_63,'#skF_2'(B_47,E_75,D_71,C_63,A_15)) != k1_funct_1(E_75,'#skF_2'(B_47,E_75,D_71,C_63,A_15))
      | k2_partfun1(A_15,B_47,C_63,D_71) = E_75
      | ~ m1_subset_1(E_75,k1_zfmisc_1(k2_zfmisc_1(D_71,B_47)))
      | ~ v1_funct_2(E_75,D_71,B_47)
      | ~ v1_funct_1(E_75)
      | ~ m1_subset_1(D_71,k1_zfmisc_1(A_15))
      | v1_xboole_0(D_71)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_15,B_47)))
      | ~ v1_funct_2(C_63,A_15,B_47)
      | ~ v1_funct_1(C_63)
      | v1_xboole_0(B_47)
      | v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_876,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_6'
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_870,c_18])).

tff(c_883,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_6'
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_576,c_876])).

tff(c_885,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_330,c_304,c_864,c_883])).

tff(c_886,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ m1_subset_1(k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))))
    | k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_449])).

tff(c_902,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4')))) ),
    inference(splitLeft,[status(thm)],[c_886])).

tff(c_1252,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1248,c_902])).

tff(c_1257,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1252])).

tff(c_1259,plain,(
    k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5')) != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1236])).

tff(c_1275,plain,(
    ! [B_420,C_421] :
      ( k3_funct_2(u1_struct_0('#skF_5'),B_420,C_421,'#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5'))) = k1_funct_1(C_421,'#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5')))
      | ~ m1_subset_1(C_421,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),B_420)))
      | ~ v1_funct_2(C_421,u1_struct_0('#skF_5'),B_420)
      | ~ v1_funct_1(C_421) ) ),
    inference(splitRight,[status(thm)],[c_1236])).

tff(c_1281,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_6'
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1275,c_18])).

tff(c_1288,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_6'
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_990,c_1281])).

tff(c_1290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_330,c_304,c_1259,c_1288])).

tff(c_1291,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_886])).

tff(c_1366,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1291])).

tff(c_1738,plain,(
    ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1734,c_1366])).

tff(c_1744,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1738])).

tff(c_1746,plain,(
    k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5')) != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1718])).

tff(c_1752,plain,(
    ! [B_478,C_479] :
      ( k3_funct_2(u1_struct_0('#skF_5'),B_478,C_479,'#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5'))) = k1_funct_1(C_479,'#skF_2'(u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5')))
      | ~ m1_subset_1(C_479,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),B_478)))
      | ~ v1_funct_2(C_479,u1_struct_0('#skF_5'),B_478)
      | ~ v1_funct_1(C_479) ) ),
    inference(splitRight,[status(thm)],[c_1718])).

tff(c_1758,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_6'
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1752,c_18])).

tff(c_1765,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_6'
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_1411,c_1758])).

tff(c_1767,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_330,c_304,c_1746,c_1765])).

tff(c_1768,plain,(
    k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1291])).

tff(c_888,plain,(
    ! [C_364,D_368,E_367,B_366,A_365] :
      ( r2_hidden('#skF_3'(C_364,A_365,B_366,E_367,D_368),u1_struct_0(C_364))
      | r2_funct_2(u1_struct_0(C_364),u1_struct_0(A_365),k2_tmap_1(B_366,A_365,D_368,C_364),E_367)
      | ~ m1_subset_1(E_367,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_364),u1_struct_0(A_365))))
      | ~ v1_funct_2(E_367,u1_struct_0(C_364),u1_struct_0(A_365))
      | ~ v1_funct_1(E_367)
      | ~ m1_subset_1(D_368,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_366),u1_struct_0(A_365))))
      | ~ v1_funct_2(D_368,u1_struct_0(B_366),u1_struct_0(A_365))
      | ~ v1_funct_1(D_368)
      | ~ m1_pre_topc(C_364,B_366)
      | v2_struct_0(C_364)
      | ~ l1_pre_topc(B_366)
      | ~ v2_pre_topc(B_366)
      | v2_struct_0(B_366)
      | ~ l1_pre_topc(A_365)
      | ~ v2_pre_topc(A_365)
      | v2_struct_0(A_365) ) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_2003,plain,(
    ! [B_508,A_509,B_510,D_511] :
      ( r2_hidden('#skF_3'(B_508,A_509,B_510,k4_tmap_1(A_509,B_508),D_511),u1_struct_0(B_508))
      | r2_funct_2(u1_struct_0(B_508),u1_struct_0(A_509),k2_tmap_1(B_510,A_509,D_511,B_508),k4_tmap_1(A_509,B_508))
      | ~ v1_funct_2(k4_tmap_1(A_509,B_508),u1_struct_0(B_508),u1_struct_0(A_509))
      | ~ v1_funct_1(k4_tmap_1(A_509,B_508))
      | ~ m1_subset_1(D_511,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_510),u1_struct_0(A_509))))
      | ~ v1_funct_2(D_511,u1_struct_0(B_510),u1_struct_0(A_509))
      | ~ v1_funct_1(D_511)
      | ~ m1_pre_topc(B_508,B_510)
      | v2_struct_0(B_508)
      | ~ l1_pre_topc(B_510)
      | ~ v2_pre_topc(B_510)
      | v2_struct_0(B_510)
      | ~ m1_pre_topc(B_508,A_509)
      | ~ l1_pre_topc(A_509)
      | ~ v2_pre_topc(A_509)
      | v2_struct_0(A_509) ) ),
    inference(resolution,[status(thm)],[c_36,c_888])).

tff(c_2008,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6'),u1_struct_0('#skF_5'))
    | r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',k4_tmap_1('#skF_4','#skF_5'))
    | ~ v1_funct_2(k4_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(k4_tmap_1('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1768,c_2003])).

tff(c_2011,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6'),u1_struct_0('#skF_5'))
    | r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',k4_tmap_1('#skF_4','#skF_5'))
    | ~ v1_funct_2(k4_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(k4_tmap_1('#skF_4','#skF_5'))
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_105,c_91,c_163,c_64,c_62,c_60,c_2008])).

tff(c_2012,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6'),u1_struct_0('#skF_5'))
    | r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',k4_tmap_1('#skF_4','#skF_5'))
    | ~ v1_funct_2(k4_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(k4_tmap_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_2011])).

tff(c_2013,plain,(
    ~ v1_funct_1(k4_tmap_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_2012])).

tff(c_2016,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_2013])).

tff(c_2019,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_2016])).

tff(c_2021,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2019])).

tff(c_2023,plain,(
    v1_funct_1(k4_tmap_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_2012])).

tff(c_38,plain,(
    ! [A_107,B_108] :
      ( v1_funct_2(k4_tmap_1(A_107,B_108),u1_struct_0(B_108),u1_struct_0(A_107))
      | ~ m1_pre_topc(B_108,A_107)
      | ~ l1_pre_topc(A_107)
      | ~ v2_pre_topc(A_107)
      | v2_struct_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_2022,plain,
    ( ~ v1_funct_2(k4_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',k4_tmap_1('#skF_4','#skF_5'))
    | r2_hidden('#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_2012])).

tff(c_2039,plain,(
    ~ v1_funct_2(k4_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2022])).

tff(c_2042,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_2039])).

tff(c_2045,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_2042])).

tff(c_2047,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2045])).

tff(c_2049,plain,(
    v1_funct_2(k4_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2022])).

tff(c_2048,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6'),u1_struct_0('#skF_5'))
    | r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',k4_tmap_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_2022])).

tff(c_2050,plain,(
    r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',k4_tmap_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_2048])).

tff(c_2052,plain,
    ( k4_tmap_1('#skF_4','#skF_5') = '#skF_6'
    | ~ m1_subset_1(k4_tmap_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2(k4_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(k4_tmap_1('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2050,c_16])).

tff(c_2055,plain,
    ( k4_tmap_1('#skF_4','#skF_5') = '#skF_6'
    | ~ m1_subset_1(k4_tmap_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_2023,c_2049,c_2052])).

tff(c_2072,plain,(
    ~ m1_subset_1(k4_tmap_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4')))) ),
    inference(splitLeft,[status(thm)],[c_2055])).

tff(c_2075,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_2072])).

tff(c_2078,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_2075])).

tff(c_2080,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2078])).

tff(c_2081,plain,(
    k4_tmap_1('#skF_4','#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2055])).

tff(c_56,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k4_tmap_1('#skF_4','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_2086,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2081,c_56])).

tff(c_2092,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_2086])).

tff(c_2094,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',k4_tmap_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_2048])).

tff(c_2125,plain,(
    ! [B_523,A_524,B_525,D_526] :
      ( m1_subset_1('#skF_3'(B_523,A_524,B_525,k4_tmap_1(A_524,B_523),D_526),u1_struct_0(B_525))
      | r2_funct_2(u1_struct_0(B_523),u1_struct_0(A_524),k2_tmap_1(B_525,A_524,D_526,B_523),k4_tmap_1(A_524,B_523))
      | ~ v1_funct_2(k4_tmap_1(A_524,B_523),u1_struct_0(B_523),u1_struct_0(A_524))
      | ~ v1_funct_1(k4_tmap_1(A_524,B_523))
      | ~ m1_subset_1(D_526,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_525),u1_struct_0(A_524))))
      | ~ v1_funct_2(D_526,u1_struct_0(B_525),u1_struct_0(A_524))
      | ~ v1_funct_1(D_526)
      | ~ m1_pre_topc(B_523,B_525)
      | v2_struct_0(B_523)
      | ~ l1_pre_topc(B_525)
      | ~ v2_pre_topc(B_525)
      | v2_struct_0(B_525)
      | ~ m1_pre_topc(B_523,A_524)
      | ~ l1_pre_topc(A_524)
      | ~ v2_pre_topc(A_524)
      | v2_struct_0(A_524) ) ),
    inference(resolution,[status(thm)],[c_36,c_412])).

tff(c_2136,plain,
    ( m1_subset_1('#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6'),u1_struct_0('#skF_5'))
    | r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',k4_tmap_1('#skF_4','#skF_5'))
    | ~ v1_funct_2(k4_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(k4_tmap_1('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1768,c_2125])).

tff(c_2141,plain,
    ( m1_subset_1('#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6'),u1_struct_0('#skF_5'))
    | r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',k4_tmap_1('#skF_4','#skF_5'))
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_105,c_91,c_163,c_64,c_62,c_60,c_2023,c_2049,c_2136])).

tff(c_2142,plain,(
    m1_subset_1('#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_2094,c_2141])).

tff(c_2149,plain,(
    ! [A_85] :
      ( m1_subset_1('#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6'),u1_struct_0(A_85))
      | ~ m1_pre_topc('#skF_5',A_85)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(A_85)
      | v2_struct_0(A_85) ) ),
    inference(resolution,[status(thm)],[c_2142,c_32])).

tff(c_2160,plain,(
    ! [A_527] :
      ( m1_subset_1('#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6'),u1_struct_0(A_527))
      | ~ m1_pre_topc('#skF_5',A_527)
      | ~ l1_pre_topc(A_527)
      | v2_struct_0(A_527) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2149])).

tff(c_2093,plain,(
    r2_hidden('#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_2048])).

tff(c_2121,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6')) = '#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6')
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2093,c_58])).

tff(c_2123,plain,(
    ~ m1_subset_1('#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2121])).

tff(c_2166,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_2160,c_2123])).

tff(c_2174,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_2166])).

tff(c_2176,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2174])).

tff(c_2178,plain,(
    m1_subset_1('#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6'),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2121])).

tff(c_54,plain,(
    ! [A_181,B_185,C_187] :
      ( k1_funct_1(k4_tmap_1(A_181,B_185),C_187) = C_187
      | ~ r2_hidden(C_187,u1_struct_0(B_185))
      | ~ m1_subset_1(C_187,u1_struct_0(A_181))
      | ~ m1_pre_topc(B_185,A_181)
      | v2_struct_0(B_185)
      | ~ l1_pre_topc(A_181)
      | ~ v2_pre_topc(A_181)
      | v2_struct_0(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_2111,plain,(
    ! [A_181] :
      ( k1_funct_1(k4_tmap_1(A_181,'#skF_5'),'#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6')) = '#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6')
      | ~ m1_subset_1('#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6'),u1_struct_0(A_181))
      | ~ m1_pre_topc('#skF_5',A_181)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(A_181)
      | ~ v2_pre_topc(A_181)
      | v2_struct_0(A_181) ) ),
    inference(resolution,[status(thm)],[c_2093,c_54])).

tff(c_2276,plain,(
    ! [A_540] :
      ( k1_funct_1(k4_tmap_1(A_540,'#skF_5'),'#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6')) = '#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6')
      | ~ m1_subset_1('#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6'),u1_struct_0(A_540))
      | ~ m1_pre_topc('#skF_5',A_540)
      | ~ l1_pre_topc(A_540)
      | ~ v2_pre_topc(A_540)
      | v2_struct_0(A_540) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2111])).

tff(c_2290,plain,
    ( k1_funct_1(k4_tmap_1('#skF_4','#skF_5'),'#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6')) = '#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_2178,c_2276])).

tff(c_2299,plain,
    ( k1_funct_1(k4_tmap_1('#skF_4','#skF_5'),'#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6')) = '#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_2290])).

tff(c_2300,plain,(
    k1_funct_1(k4_tmap_1('#skF_4','#skF_5'),'#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6')) = '#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2299])).

tff(c_2177,plain,(
    k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6')) = '#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_2121])).

tff(c_2230,plain,(
    ! [B_533,A_534,B_535,D_536] :
      ( m1_subset_1('#skF_3'(B_533,A_534,B_535,k4_tmap_1(A_534,B_533),D_536),u1_struct_0(B_535))
      | r2_funct_2(u1_struct_0(B_533),u1_struct_0(A_534),k2_tmap_1(B_535,A_534,D_536,B_533),k4_tmap_1(A_534,B_533))
      | ~ v1_funct_2(k4_tmap_1(A_534,B_533),u1_struct_0(B_533),u1_struct_0(A_534))
      | ~ v1_funct_1(k4_tmap_1(A_534,B_533))
      | ~ m1_subset_1(D_536,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_535),u1_struct_0(A_534))))
      | ~ v1_funct_2(D_536,u1_struct_0(B_535),u1_struct_0(A_534))
      | ~ v1_funct_1(D_536)
      | ~ m1_pre_topc(B_533,B_535)
      | v2_struct_0(B_533)
      | ~ l1_pre_topc(B_535)
      | ~ v2_pre_topc(B_535)
      | v2_struct_0(B_535)
      | ~ m1_pre_topc(B_533,A_534)
      | ~ l1_pre_topc(A_534)
      | ~ v2_pre_topc(A_534)
      | v2_struct_0(A_534) ) ),
    inference(resolution,[status(thm)],[c_36,c_412])).

tff(c_2239,plain,
    ( m1_subset_1('#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6'),u1_struct_0('#skF_5'))
    | r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',k4_tmap_1('#skF_4','#skF_5'))
    | ~ v1_funct_2(k4_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(k4_tmap_1('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1768,c_2230])).

tff(c_2244,plain,
    ( m1_subset_1('#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6'),u1_struct_0('#skF_5'))
    | r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',k4_tmap_1('#skF_4','#skF_5'))
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_105,c_91,c_163,c_64,c_62,c_60,c_2023,c_2049,c_2239])).

tff(c_2245,plain,(
    m1_subset_1('#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_2094,c_2244])).

tff(c_2247,plain,(
    ! [B_8,C_9] :
      ( k3_funct_2(u1_struct_0('#skF_5'),B_8,C_9,'#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6')) = k1_funct_1(C_9,'#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6'))
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),B_8)))
      | ~ v1_funct_2(C_9,u1_struct_0('#skF_5'),B_8)
      | ~ v1_funct_1(C_9)
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_2245,c_12])).

tff(c_2346,plain,(
    ! [B_542,C_543] :
      ( k3_funct_2(u1_struct_0('#skF_5'),B_542,C_543,'#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6')) = k1_funct_1(C_543,'#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6'))
      | ~ m1_subset_1(C_543,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),B_542)))
      | ~ v1_funct_2(C_543,u1_struct_0('#skF_5'),B_542)
      | ~ v1_funct_1(C_543) ) ),
    inference(negUnitSimplification,[status(thm)],[c_330,c_2247])).

tff(c_2361,plain,
    ( k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6','#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6')) = k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6'))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_2346])).

tff(c_2367,plain,(
    k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6','#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6')) = '#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_2177,c_2361])).

tff(c_48,plain,(
    ! [A_119,D_175,C_167,B_151,E_179] :
      ( k3_funct_2(u1_struct_0(B_151),u1_struct_0(A_119),D_175,'#skF_3'(C_167,A_119,B_151,E_179,D_175)) != k1_funct_1(E_179,'#skF_3'(C_167,A_119,B_151,E_179,D_175))
      | r2_funct_2(u1_struct_0(C_167),u1_struct_0(A_119),k2_tmap_1(B_151,A_119,D_175,C_167),E_179)
      | ~ m1_subset_1(E_179,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_167),u1_struct_0(A_119))))
      | ~ v1_funct_2(E_179,u1_struct_0(C_167),u1_struct_0(A_119))
      | ~ v1_funct_1(E_179)
      | ~ m1_subset_1(D_175,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_151),u1_struct_0(A_119))))
      | ~ v1_funct_2(D_175,u1_struct_0(B_151),u1_struct_0(A_119))
      | ~ v1_funct_1(D_175)
      | ~ m1_pre_topc(C_167,B_151)
      | v2_struct_0(C_167)
      | ~ l1_pre_topc(B_151)
      | ~ v2_pre_topc(B_151)
      | v2_struct_0(B_151)
      | ~ l1_pre_topc(A_119)
      | ~ v2_pre_topc(A_119)
      | v2_struct_0(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_2392,plain,
    ( k1_funct_1(k4_tmap_1('#skF_4','#skF_5'),'#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6')) != '#skF_3'('#skF_5','#skF_4','#skF_5',k4_tmap_1('#skF_4','#skF_5'),'#skF_6')
    | r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_5'),k4_tmap_1('#skF_4','#skF_5'))
    | ~ m1_subset_1(k4_tmap_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2(k4_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(k4_tmap_1('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2367,c_48])).

tff(c_2396,plain,
    ( r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6',k4_tmap_1('#skF_4','#skF_5'))
    | ~ m1_subset_1(k4_tmap_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))))
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_105,c_91,c_163,c_64,c_62,c_60,c_2023,c_2049,c_1768,c_2300,c_2392])).

tff(c_2397,plain,(
    ~ m1_subset_1(k4_tmap_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4')))) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_2094,c_2396])).

tff(c_2401,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_2397])).

tff(c_2404,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_2401])).

tff(c_2406,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2404])).

tff(c_2408,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_443])).

tff(c_2407,plain,(
    m1_subset_1('#skF_3'('#skF_5','#skF_4','#skF_5','#skF_6','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_443])).

tff(c_2412,plain,(
    ! [A_85] :
      ( m1_subset_1('#skF_3'('#skF_5','#skF_4','#skF_5','#skF_6','#skF_6'),u1_struct_0(A_85))
      | ~ m1_pre_topc('#skF_5',A_85)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(A_85)
      | v2_struct_0(A_85) ) ),
    inference(resolution,[status(thm)],[c_2407,c_32])).

tff(c_2419,plain,(
    ! [A_548] :
      ( m1_subset_1('#skF_3'('#skF_5','#skF_4','#skF_5','#skF_6','#skF_6'),u1_struct_0(A_548))
      | ~ m1_pre_topc('#skF_5',A_548)
      | ~ l1_pre_topc(A_548)
      | v2_struct_0(A_548) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2412])).

tff(c_2426,plain,(
    ! [A_549,A_550] :
      ( m1_subset_1('#skF_3'('#skF_5','#skF_4','#skF_5','#skF_6','#skF_6'),u1_struct_0(A_549))
      | ~ m1_pre_topc(A_550,A_549)
      | ~ l1_pre_topc(A_549)
      | v2_struct_0(A_549)
      | ~ m1_pre_topc('#skF_5',A_550)
      | ~ l1_pre_topc(A_550)
      | v2_struct_0(A_550) ) ),
    inference(resolution,[status(thm)],[c_2419,c_32])).

tff(c_2430,plain,
    ( m1_subset_1('#skF_3'('#skF_5','#skF_4','#skF_5','#skF_6','#skF_6'),u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_2426])).

tff(c_2437,plain,
    ( m1_subset_1('#skF_3'('#skF_5','#skF_4','#skF_5','#skF_6','#skF_6'),u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_163,c_70,c_2430])).

tff(c_2438,plain,(
    m1_subset_1('#skF_3'('#skF_5','#skF_4','#skF_5','#skF_6','#skF_6'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_74,c_2437])).

tff(c_2469,plain,(
    ! [A_555,C_554,D_558,B_556,E_557] :
      ( r2_hidden('#skF_3'(C_554,A_555,B_556,E_557,D_558),u1_struct_0(C_554))
      | r2_funct_2(u1_struct_0(C_554),u1_struct_0(A_555),k2_tmap_1(B_556,A_555,D_558,C_554),E_557)
      | ~ m1_subset_1(E_557,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_554),u1_struct_0(A_555))))
      | ~ v1_funct_2(E_557,u1_struct_0(C_554),u1_struct_0(A_555))
      | ~ v1_funct_1(E_557)
      | ~ m1_subset_1(D_558,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_556),u1_struct_0(A_555))))
      | ~ v1_funct_2(D_558,u1_struct_0(B_556),u1_struct_0(A_555))
      | ~ v1_funct_1(D_558)
      | ~ m1_pre_topc(C_554,B_556)
      | v2_struct_0(C_554)
      | ~ l1_pre_topc(B_556)
      | ~ v2_pre_topc(B_556)
      | v2_struct_0(B_556)
      | ~ l1_pre_topc(A_555)
      | ~ v2_pre_topc(A_555)
      | v2_struct_0(A_555) ) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_2476,plain,(
    ! [B_556,D_558] :
      ( r2_hidden('#skF_3'('#skF_5','#skF_4',B_556,'#skF_6',D_558),u1_struct_0('#skF_5'))
      | r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1(B_556,'#skF_4',D_558,'#skF_5'),'#skF_6')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(D_558,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_556),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(D_558,u1_struct_0(B_556),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(D_558)
      | ~ m1_pre_topc('#skF_5',B_556)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(B_556)
      | ~ v2_pre_topc(B_556)
      | v2_struct_0(B_556)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_2469])).

tff(c_2481,plain,(
    ! [B_556,D_558] :
      ( r2_hidden('#skF_3'('#skF_5','#skF_4',B_556,'#skF_6',D_558),u1_struct_0('#skF_5'))
      | r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1(B_556,'#skF_4',D_558,'#skF_5'),'#skF_6')
      | ~ m1_subset_1(D_558,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_556),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(D_558,u1_struct_0(B_556),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(D_558)
      | ~ m1_pre_topc('#skF_5',B_556)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(B_556)
      | ~ v2_pre_topc(B_556)
      | v2_struct_0(B_556)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_64,c_62,c_2476])).

tff(c_2515,plain,(
    ! [B_563,D_564] :
      ( r2_hidden('#skF_3'('#skF_5','#skF_4',B_563,'#skF_6',D_564),u1_struct_0('#skF_5'))
      | r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1(B_563,'#skF_4',D_564,'#skF_5'),'#skF_6')
      | ~ m1_subset_1(D_564,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_563),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(D_564,u1_struct_0(B_563),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(D_564)
      | ~ m1_pre_topc('#skF_5',B_563)
      | ~ l1_pre_topc(B_563)
      | ~ v2_pre_topc(B_563)
      | v2_struct_0(B_563) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_2481])).

tff(c_2526,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_4','#skF_5','#skF_6','#skF_6'),u1_struct_0('#skF_5'))
    | r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_5'),'#skF_6')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_2515])).

tff(c_2534,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_4','#skF_5','#skF_6','#skF_6'),u1_struct_0('#skF_5'))
    | r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_5'),'#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_91,c_163,c_64,c_62,c_2526])).

tff(c_2535,plain,(
    r2_hidden('#skF_3'('#skF_5','#skF_4','#skF_5','#skF_6','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2408,c_2534])).

tff(c_2540,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_4','#skF_5','#skF_6','#skF_6')) = '#skF_3'('#skF_5','#skF_4','#skF_5','#skF_6','#skF_6')
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_4','#skF_5','#skF_6','#skF_6'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2535,c_58])).

tff(c_2549,plain,(
    k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_4','#skF_5','#skF_6','#skF_6')) = '#skF_3'('#skF_5','#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2438,c_2540])).

tff(c_2410,plain,(
    ! [B_8,C_9] :
      ( k3_funct_2(u1_struct_0('#skF_5'),B_8,C_9,'#skF_3'('#skF_5','#skF_4','#skF_5','#skF_6','#skF_6')) = k1_funct_1(C_9,'#skF_3'('#skF_5','#skF_4','#skF_5','#skF_6','#skF_6'))
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),B_8)))
      | ~ v1_funct_2(C_9,u1_struct_0('#skF_5'),B_8)
      | ~ v1_funct_1(C_9)
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_2407,c_12])).

tff(c_2483,plain,(
    ! [B_559,C_560] :
      ( k3_funct_2(u1_struct_0('#skF_5'),B_559,C_560,'#skF_3'('#skF_5','#skF_4','#skF_5','#skF_6','#skF_6')) = k1_funct_1(C_560,'#skF_3'('#skF_5','#skF_4','#skF_5','#skF_6','#skF_6'))
      | ~ m1_subset_1(C_560,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),B_559)))
      | ~ v1_funct_2(C_560,u1_struct_0('#skF_5'),B_559)
      | ~ v1_funct_1(C_560) ) ),
    inference(negUnitSimplification,[status(thm)],[c_330,c_2410])).

tff(c_2494,plain,
    ( k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6','#skF_3'('#skF_5','#skF_4','#skF_5','#skF_6','#skF_6')) = k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_4','#skF_5','#skF_6','#skF_6'))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_2483])).

tff(c_2499,plain,(
    k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6','#skF_3'('#skF_5','#skF_4','#skF_5','#skF_6','#skF_6')) = k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_4','#skF_5','#skF_6','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_2494])).

tff(c_2551,plain,(
    k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6','#skF_3'('#skF_5','#skF_4','#skF_5','#skF_6','#skF_6')) = '#skF_3'('#skF_5','#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2549,c_2499])).

tff(c_2587,plain,(
    ! [E_569,B_568,C_566,A_567,D_570] :
      ( k3_funct_2(u1_struct_0(B_568),u1_struct_0(A_567),D_570,'#skF_3'(C_566,A_567,B_568,E_569,D_570)) != k1_funct_1(E_569,'#skF_3'(C_566,A_567,B_568,E_569,D_570))
      | r2_funct_2(u1_struct_0(C_566),u1_struct_0(A_567),k2_tmap_1(B_568,A_567,D_570,C_566),E_569)
      | ~ m1_subset_1(E_569,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_566),u1_struct_0(A_567))))
      | ~ v1_funct_2(E_569,u1_struct_0(C_566),u1_struct_0(A_567))
      | ~ v1_funct_1(E_569)
      | ~ m1_subset_1(D_570,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_568),u1_struct_0(A_567))))
      | ~ v1_funct_2(D_570,u1_struct_0(B_568),u1_struct_0(A_567))
      | ~ v1_funct_1(D_570)
      | ~ m1_pre_topc(C_566,B_568)
      | v2_struct_0(C_566)
      | ~ l1_pre_topc(B_568)
      | ~ v2_pre_topc(B_568)
      | v2_struct_0(B_568)
      | ~ l1_pre_topc(A_567)
      | ~ v2_pre_topc(A_567)
      | v2_struct_0(A_567) ) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_2589,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_4','#skF_5','#skF_6','#skF_6')) != '#skF_3'('#skF_5','#skF_4','#skF_5','#skF_6','#skF_6')
    | r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_5'),'#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2551,c_2587])).

tff(c_2591,plain,
    ( r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_5'),'#skF_6')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_105,c_91,c_163,c_64,c_62,c_60,c_64,c_62,c_60,c_2549,c_2589])).

tff(c_2593,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_2408,c_2591])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:45:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.86/2.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.86/2.35  
% 6.86/2.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.86/2.36  %$ r2_funct_2 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_funct_2 > k2_tmap_1 > k2_partfun1 > k4_tmap_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 6.86/2.36  
% 6.86/2.36  %Foreground sorts:
% 6.86/2.36  
% 6.86/2.36  
% 6.86/2.36  %Background operators:
% 6.86/2.36  
% 6.86/2.36  
% 6.86/2.36  %Foreground operators:
% 6.86/2.36  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.86/2.36  tff(k4_tmap_1, type, k4_tmap_1: ($i * $i) > $i).
% 6.86/2.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.86/2.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.86/2.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.86/2.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 6.86/2.36  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.86/2.36  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.86/2.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.86/2.36  tff('#skF_5', type, '#skF_5': $i).
% 6.86/2.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.86/2.36  tff('#skF_6', type, '#skF_6': $i).
% 6.86/2.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.86/2.36  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.86/2.36  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.86/2.36  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 6.86/2.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.86/2.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.86/2.36  tff('#skF_4', type, '#skF_4': $i).
% 6.86/2.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.86/2.36  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.86/2.36  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 6.86/2.36  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.86/2.36  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 6.86/2.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.86/2.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.86/2.36  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 6.86/2.36  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 6.86/2.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.86/2.36  
% 7.20/2.39  tff(f_303, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, u1_struct_0(B)) => (D = k1_funct_1(C, D))))) => r2_funct_2(u1_struct_0(B), u1_struct_0(A), k4_tmap_1(A, B), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_tmap_1)).
% 7.20/2.39  tff(f_188, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_funct_1(k4_tmap_1(A, B)) & v1_funct_2(k4_tmap_1(A, B), u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(k4_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_tmap_1)).
% 7.20/2.39  tff(f_66, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 7.20/2.39  tff(f_111, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 7.20/2.39  tff(f_122, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 7.20/2.39  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.20/2.39  tff(f_209, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 7.20/2.39  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 7.20/2.39  tff(f_102, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, D, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((![F]: (m1_subset_1(F, A) => (r2_hidden(F, D) => (k3_funct_2(A, B, C, F) = k1_funct_1(E, F))))) => (k2_partfun1(A, B, C, D) = E)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_funct_2)).
% 7.20/2.39  tff(f_130, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 7.20/2.39  tff(f_195, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 7.20/2.39  tff(f_146, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_pre_topc)).
% 7.20/2.39  tff(f_50, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 7.20/2.39  tff(f_173, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 7.20/2.39  tff(f_253, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(A))))) => ((![F]: (m1_subset_1(F, u1_struct_0(B)) => (r2_hidden(F, u1_struct_0(C)) => (k3_funct_2(u1_struct_0(B), u1_struct_0(A), D, F) = k1_funct_1(E, F))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(A), k2_tmap_1(B, A, D, C), E)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_tmap_1)).
% 7.20/2.39  tff(f_273, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, u1_struct_0(B)) => (k1_funct_1(k4_tmap_1(A, B), C) = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_tmap_1)).
% 7.20/2.39  tff(c_74, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_303])).
% 7.20/2.39  tff(c_68, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_303])).
% 7.20/2.39  tff(c_72, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_303])).
% 7.20/2.39  tff(c_70, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_303])).
% 7.20/2.39  tff(c_66, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_303])).
% 7.20/2.39  tff(c_36, plain, (![A_107, B_108]: (m1_subset_1(k4_tmap_1(A_107, B_108), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_108), u1_struct_0(A_107)))) | ~m1_pre_topc(B_108, A_107) | ~l1_pre_topc(A_107) | ~v2_pre_topc(A_107) | v2_struct_0(A_107))), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.20/2.39  tff(c_64, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_303])).
% 7.20/2.39  tff(c_62, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_303])).
% 7.20/2.39  tff(c_60, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_303])).
% 7.20/2.39  tff(c_116, plain, (![A_222, B_223, D_224]: (r2_funct_2(A_222, B_223, D_224, D_224) | ~m1_subset_1(D_224, k1_zfmisc_1(k2_zfmisc_1(A_222, B_223))) | ~v1_funct_2(D_224, A_222, B_223) | ~v1_funct_1(D_224))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.20/2.39  tff(c_118, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', '#skF_6') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_60, c_116])).
% 7.20/2.39  tff(c_121, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_118])).
% 7.20/2.39  tff(c_40, plain, (![A_107, B_108]: (v1_funct_1(k4_tmap_1(A_107, B_108)) | ~m1_pre_topc(B_108, A_107) | ~l1_pre_topc(A_107) | ~v2_pre_topc(A_107) | v2_struct_0(A_107))), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.20/2.39  tff(c_99, plain, (![B_210, A_211]: (v2_pre_topc(B_210) | ~m1_pre_topc(B_210, A_211) | ~l1_pre_topc(A_211) | ~v2_pre_topc(A_211))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.20/2.39  tff(c_102, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_66, c_99])).
% 7.20/2.39  tff(c_105, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_102])).
% 7.20/2.39  tff(c_85, plain, (![B_206, A_207]: (l1_pre_topc(B_206) | ~m1_pre_topc(B_206, A_207) | ~l1_pre_topc(A_207))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.20/2.39  tff(c_88, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_66, c_85])).
% 7.20/2.39  tff(c_91, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_88])).
% 7.20/2.39  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.20/2.39  tff(c_150, plain, (![B_230, C_231, A_232]: (m1_pre_topc(B_230, C_231) | ~r1_tarski(u1_struct_0(B_230), u1_struct_0(C_231)) | ~m1_pre_topc(C_231, A_232) | ~m1_pre_topc(B_230, A_232) | ~l1_pre_topc(A_232) | ~v2_pre_topc(A_232))), inference(cnfTransformation, [status(thm)], [f_209])).
% 7.20/2.39  tff(c_158, plain, (![B_233, A_234]: (m1_pre_topc(B_233, B_233) | ~m1_pre_topc(B_233, A_234) | ~l1_pre_topc(A_234) | ~v2_pre_topc(A_234))), inference(resolution, [status(thm)], [c_10, c_150])).
% 7.20/2.39  tff(c_160, plain, (m1_pre_topc('#skF_5', '#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_66, c_158])).
% 7.20/2.39  tff(c_163, plain, (m1_pre_topc('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_160])).
% 7.20/2.39  tff(c_26, plain, (![A_80]: (l1_struct_0(A_80) | ~l1_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.20/2.39  tff(c_280, plain, (![D_268, E_267, B_266, C_269, A_270]: (m1_subset_1('#skF_2'(B_266, E_267, D_268, C_269, A_270), A_270) | k2_partfun1(A_270, B_266, C_269, D_268)=E_267 | ~m1_subset_1(E_267, k1_zfmisc_1(k2_zfmisc_1(D_268, B_266))) | ~v1_funct_2(E_267, D_268, B_266) | ~v1_funct_1(E_267) | ~m1_subset_1(D_268, k1_zfmisc_1(A_270)) | v1_xboole_0(D_268) | ~m1_subset_1(C_269, k1_zfmisc_1(k2_zfmisc_1(A_270, B_266))) | ~v1_funct_2(C_269, A_270, B_266) | ~v1_funct_1(C_269) | v1_xboole_0(B_266) | v1_xboole_0(A_270))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.20/2.39  tff(c_284, plain, (![C_269, A_270]: (m1_subset_1('#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), C_269, A_270), A_270) | k2_partfun1(A_270, u1_struct_0('#skF_4'), C_269, u1_struct_0('#skF_5'))='#skF_6' | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_270)) | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1(C_269, k1_zfmisc_1(k2_zfmisc_1(A_270, u1_struct_0('#skF_4')))) | ~v1_funct_2(C_269, A_270, u1_struct_0('#skF_4')) | ~v1_funct_1(C_269) | v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0(A_270))), inference(resolution, [status(thm)], [c_60, c_280])).
% 7.20/2.39  tff(c_288, plain, (![C_269, A_270]: (m1_subset_1('#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), C_269, A_270), A_270) | k2_partfun1(A_270, u1_struct_0('#skF_4'), C_269, u1_struct_0('#skF_5'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_270)) | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1(C_269, k1_zfmisc_1(k2_zfmisc_1(A_270, u1_struct_0('#skF_4')))) | ~v1_funct_2(C_269, A_270, u1_struct_0('#skF_4')) | ~v1_funct_1(C_269) | v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0(A_270))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_284])).
% 7.20/2.39  tff(c_289, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_288])).
% 7.20/2.39  tff(c_30, plain, (![A_84]: (~v1_xboole_0(u1_struct_0(A_84)) | ~l1_struct_0(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.20/2.40  tff(c_292, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_289, c_30])).
% 7.20/2.40  tff(c_295, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_74, c_292])).
% 7.20/2.40  tff(c_298, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_26, c_295])).
% 7.20/2.40  tff(c_302, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_298])).
% 7.20/2.40  tff(c_303, plain, (![C_269, A_270]: (v1_xboole_0(u1_struct_0('#skF_5')) | m1_subset_1('#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), C_269, A_270), A_270) | k2_partfun1(A_270, u1_struct_0('#skF_4'), C_269, u1_struct_0('#skF_5'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_270)) | ~m1_subset_1(C_269, k1_zfmisc_1(k2_zfmisc_1(A_270, u1_struct_0('#skF_4')))) | ~v1_funct_2(C_269, A_270, u1_struct_0('#skF_4')) | ~v1_funct_1(C_269) | v1_xboole_0(A_270))), inference(splitRight, [status(thm)], [c_288])).
% 7.20/2.40  tff(c_305, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_303])).
% 7.20/2.40  tff(c_308, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_305, c_30])).
% 7.20/2.40  tff(c_311, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_68, c_308])).
% 7.20/2.40  tff(c_324, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_26, c_311])).
% 7.20/2.40  tff(c_328, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_324])).
% 7.20/2.40  tff(c_330, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_303])).
% 7.20/2.40  tff(c_304, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_288])).
% 7.20/2.40  tff(c_42, plain, (![B_111, A_109]: (m1_subset_1(u1_struct_0(B_111), k1_zfmisc_1(u1_struct_0(A_109))) | ~m1_pre_topc(B_111, A_109) | ~l1_pre_topc(A_109))), inference(cnfTransformation, [status(thm)], [f_195])).
% 7.20/2.40  tff(c_331, plain, (![C_276, A_277]: (m1_subset_1('#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), C_276, A_277), A_277) | k2_partfun1(A_277, u1_struct_0('#skF_4'), C_276, u1_struct_0('#skF_5'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_277)) | ~m1_subset_1(C_276, k1_zfmisc_1(k2_zfmisc_1(A_277, u1_struct_0('#skF_4')))) | ~v1_funct_2(C_276, A_277, u1_struct_0('#skF_4')) | ~v1_funct_1(C_276) | v1_xboole_0(A_277))), inference(splitRight, [status(thm)], [c_303])).
% 7.20/2.40  tff(c_32, plain, (![C_91, A_85, B_89]: (m1_subset_1(C_91, u1_struct_0(A_85)) | ~m1_subset_1(C_91, u1_struct_0(B_89)) | ~m1_pre_topc(B_89, A_85) | v2_struct_0(B_89) | ~l1_pre_topc(A_85) | v2_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.20/2.40  tff(c_354, plain, (![C_276, B_89, A_85]: (m1_subset_1('#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), C_276, u1_struct_0(B_89)), u1_struct_0(A_85)) | ~m1_pre_topc(B_89, A_85) | v2_struct_0(B_89) | ~l1_pre_topc(A_85) | v2_struct_0(A_85) | k2_partfun1(u1_struct_0(B_89), u1_struct_0('#skF_4'), C_276, u1_struct_0('#skF_5'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0(B_89))) | ~m1_subset_1(C_276, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_89), u1_struct_0('#skF_4')))) | ~v1_funct_2(C_276, u1_struct_0(B_89), u1_struct_0('#skF_4')) | ~v1_funct_1(C_276) | v1_xboole_0(u1_struct_0(B_89)))), inference(resolution, [status(thm)], [c_331, c_32])).
% 7.20/2.40  tff(c_362, plain, (![A_285, B_281, C_284, E_282, D_283]: (r2_hidden('#skF_2'(B_281, E_282, D_283, C_284, A_285), D_283) | k2_partfun1(A_285, B_281, C_284, D_283)=E_282 | ~m1_subset_1(E_282, k1_zfmisc_1(k2_zfmisc_1(D_283, B_281))) | ~v1_funct_2(E_282, D_283, B_281) | ~v1_funct_1(E_282) | ~m1_subset_1(D_283, k1_zfmisc_1(A_285)) | v1_xboole_0(D_283) | ~m1_subset_1(C_284, k1_zfmisc_1(k2_zfmisc_1(A_285, B_281))) | ~v1_funct_2(C_284, A_285, B_281) | ~v1_funct_1(C_284) | v1_xboole_0(B_281) | v1_xboole_0(A_285))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.20/2.40  tff(c_369, plain, (![C_284, A_285]: (r2_hidden('#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), C_284, A_285), u1_struct_0('#skF_5')) | k2_partfun1(A_285, u1_struct_0('#skF_4'), C_284, u1_struct_0('#skF_5'))='#skF_6' | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_285)) | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1(C_284, k1_zfmisc_1(k2_zfmisc_1(A_285, u1_struct_0('#skF_4')))) | ~v1_funct_2(C_284, A_285, u1_struct_0('#skF_4')) | ~v1_funct_1(C_284) | v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0(A_285))), inference(resolution, [status(thm)], [c_60, c_362])).
% 7.20/2.40  tff(c_374, plain, (![C_284, A_285]: (r2_hidden('#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), C_284, A_285), u1_struct_0('#skF_5')) | k2_partfun1(A_285, u1_struct_0('#skF_4'), C_284, u1_struct_0('#skF_5'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_285)) | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1(C_284, k1_zfmisc_1(k2_zfmisc_1(A_285, u1_struct_0('#skF_4')))) | ~v1_funct_2(C_284, A_285, u1_struct_0('#skF_4')) | ~v1_funct_1(C_284) | v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0(A_285))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_369])).
% 7.20/2.40  tff(c_376, plain, (![C_286, A_287]: (r2_hidden('#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), C_286, A_287), u1_struct_0('#skF_5')) | k2_partfun1(A_287, u1_struct_0('#skF_4'), C_286, u1_struct_0('#skF_5'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_287)) | ~m1_subset_1(C_286, k1_zfmisc_1(k2_zfmisc_1(A_287, u1_struct_0('#skF_4')))) | ~v1_funct_2(C_286, A_287, u1_struct_0('#skF_4')) | ~v1_funct_1(C_286) | v1_xboole_0(A_287))), inference(negUnitSimplification, [status(thm)], [c_304, c_330, c_374])).
% 7.20/2.40  tff(c_58, plain, (![D_199]: (k1_funct_1('#skF_6', D_199)=D_199 | ~r2_hidden(D_199, u1_struct_0('#skF_5')) | ~m1_subset_1(D_199, u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_303])).
% 7.20/2.40  tff(c_396, plain, (![C_297, A_298]: (k1_funct_1('#skF_6', '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), C_297, A_298))='#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), C_297, A_298) | ~m1_subset_1('#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), C_297, A_298), u1_struct_0('#skF_4')) | k2_partfun1(A_298, u1_struct_0('#skF_4'), C_297, u1_struct_0('#skF_5'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_298)) | ~m1_subset_1(C_297, k1_zfmisc_1(k2_zfmisc_1(A_298, u1_struct_0('#skF_4')))) | ~v1_funct_2(C_297, A_298, u1_struct_0('#skF_4')) | ~v1_funct_1(C_297) | v1_xboole_0(A_298))), inference(resolution, [status(thm)], [c_376, c_58])).
% 7.20/2.40  tff(c_400, plain, (![C_276, B_89]: (k1_funct_1('#skF_6', '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), C_276, u1_struct_0(B_89)))='#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), C_276, u1_struct_0(B_89)) | ~m1_pre_topc(B_89, '#skF_4') | v2_struct_0(B_89) | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4') | k2_partfun1(u1_struct_0(B_89), u1_struct_0('#skF_4'), C_276, u1_struct_0('#skF_5'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0(B_89))) | ~m1_subset_1(C_276, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_89), u1_struct_0('#skF_4')))) | ~v1_funct_2(C_276, u1_struct_0(B_89), u1_struct_0('#skF_4')) | ~v1_funct_1(C_276) | v1_xboole_0(u1_struct_0(B_89)))), inference(resolution, [status(thm)], [c_354, c_396])).
% 7.20/2.40  tff(c_407, plain, (![C_276, B_89]: (k1_funct_1('#skF_6', '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), C_276, u1_struct_0(B_89)))='#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), C_276, u1_struct_0(B_89)) | ~m1_pre_topc(B_89, '#skF_4') | v2_struct_0(B_89) | v2_struct_0('#skF_4') | k2_partfun1(u1_struct_0(B_89), u1_struct_0('#skF_4'), C_276, u1_struct_0('#skF_5'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0(B_89))) | ~m1_subset_1(C_276, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_89), u1_struct_0('#skF_4')))) | ~v1_funct_2(C_276, u1_struct_0(B_89), u1_struct_0('#skF_4')) | ~v1_funct_1(C_276) | v1_xboole_0(u1_struct_0(B_89)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_400])).
% 7.20/2.40  tff(c_1374, plain, (![C_430, B_431]: (k1_funct_1('#skF_6', '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), C_430, u1_struct_0(B_431)))='#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), C_430, u1_struct_0(B_431)) | ~m1_pre_topc(B_431, '#skF_4') | v2_struct_0(B_431) | k2_partfun1(u1_struct_0(B_431), u1_struct_0('#skF_4'), C_430, u1_struct_0('#skF_5'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0(B_431))) | ~m1_subset_1(C_430, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_431), u1_struct_0('#skF_4')))) | ~v1_funct_2(C_430, u1_struct_0(B_431), u1_struct_0('#skF_4')) | ~v1_funct_1(C_430) | v1_xboole_0(u1_struct_0(B_431)))), inference(negUnitSimplification, [status(thm)], [c_74, c_407])).
% 7.20/2.40  tff(c_1388, plain, (k1_funct_1('#skF_6', '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5')))='#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5')) | ~m1_pre_topc('#skF_5', '#skF_4') | v2_struct_0('#skF_5') | k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_60, c_1374])).
% 7.20/2.40  tff(c_1400, plain, (k1_funct_1('#skF_6', '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5')))='#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5')) | v2_struct_0('#skF_5') | k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_66, c_1388])).
% 7.20/2.40  tff(c_1401, plain, (k1_funct_1('#skF_6', '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5')))='#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5')) | k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_330, c_68, c_1400])).
% 7.20/2.40  tff(c_1402, plain, (~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_1401])).
% 7.20/2.40  tff(c_1405, plain, (~m1_pre_topc('#skF_5', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_42, c_1402])).
% 7.20/2.40  tff(c_1409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_163, c_1405])).
% 7.20/2.40  tff(c_1411, plain, (m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_1401])).
% 7.20/2.40  tff(c_12, plain, (![A_7, B_8, C_9, D_10]: (k3_funct_2(A_7, B_8, C_9, D_10)=k1_funct_1(C_9, D_10) | ~m1_subset_1(D_10, A_7) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))) | ~v1_funct_2(C_9, A_7, B_8) | ~v1_funct_1(C_9) | v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.20/2.40  tff(c_1691, plain, (![A_470, B_471, C_472, C_473]: (k3_funct_2(A_470, B_471, C_472, '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), C_473, A_470))=k1_funct_1(C_472, '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), C_473, A_470)) | ~m1_subset_1(C_472, k1_zfmisc_1(k2_zfmisc_1(A_470, B_471))) | ~v1_funct_2(C_472, A_470, B_471) | ~v1_funct_1(C_472) | k2_partfun1(A_470, u1_struct_0('#skF_4'), C_473, u1_struct_0('#skF_5'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_470)) | ~m1_subset_1(C_473, k1_zfmisc_1(k2_zfmisc_1(A_470, u1_struct_0('#skF_4')))) | ~v1_funct_2(C_473, A_470, u1_struct_0('#skF_4')) | ~v1_funct_1(C_473) | v1_xboole_0(A_470))), inference(resolution, [status(thm)], [c_331, c_12])).
% 7.20/2.40  tff(c_1704, plain, (![B_471, C_472]: (k3_funct_2(u1_struct_0('#skF_5'), B_471, C_472, '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5')))=k1_funct_1(C_472, '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5'))) | ~m1_subset_1(C_472, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), B_471))) | ~v1_funct_2(C_472, u1_struct_0('#skF_5'), B_471) | ~v1_funct_1(C_472) | k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | v1_xboole_0(u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_60, c_1691])).
% 7.20/2.40  tff(c_1717, plain, (![B_471, C_472]: (k3_funct_2(u1_struct_0('#skF_5'), B_471, C_472, '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5')))=k1_funct_1(C_472, '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5'))) | ~m1_subset_1(C_472, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), B_471))) | ~v1_funct_2(C_472, u1_struct_0('#skF_5'), B_471) | ~v1_funct_1(C_472) | k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'))='#skF_6' | v1_xboole_0(u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_1411, c_1704])).
% 7.20/2.40  tff(c_1718, plain, (![B_471, C_472]: (k3_funct_2(u1_struct_0('#skF_5'), B_471, C_472, '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5')))=k1_funct_1(C_472, '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5'))) | ~m1_subset_1(C_472, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), B_471))) | ~v1_funct_2(C_472, u1_struct_0('#skF_5'), B_471) | ~v1_funct_1(C_472) | k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'))='#skF_6')), inference(negUnitSimplification, [status(thm)], [c_330, c_1717])).
% 7.20/2.40  tff(c_1719, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'))='#skF_6'), inference(splitLeft, [status(thm)], [c_1718])).
% 7.20/2.40  tff(c_252, plain, (![A_258, B_259, C_260, D_261]: (k2_partfun1(u1_struct_0(A_258), u1_struct_0(B_259), C_260, u1_struct_0(D_261))=k2_tmap_1(A_258, B_259, C_260, D_261) | ~m1_pre_topc(D_261, A_258) | ~m1_subset_1(C_260, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_258), u1_struct_0(B_259)))) | ~v1_funct_2(C_260, u1_struct_0(A_258), u1_struct_0(B_259)) | ~v1_funct_1(C_260) | ~l1_pre_topc(B_259) | ~v2_pre_topc(B_259) | v2_struct_0(B_259) | ~l1_pre_topc(A_258) | ~v2_pre_topc(A_258) | v2_struct_0(A_258))), inference(cnfTransformation, [status(thm)], [f_173])).
% 7.20/2.40  tff(c_256, plain, (![D_261]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', u1_struct_0(D_261))=k2_tmap_1('#skF_5', '#skF_4', '#skF_6', D_261) | ~m1_pre_topc(D_261, '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_60, c_252])).
% 7.20/2.40  tff(c_260, plain, (![D_261]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', u1_struct_0(D_261))=k2_tmap_1('#skF_5', '#skF_4', '#skF_6', D_261) | ~m1_pre_topc(D_261, '#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_91, c_72, c_70, c_64, c_62, c_256])).
% 7.20/2.40  tff(c_261, plain, (![D_261]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', u1_struct_0(D_261))=k2_tmap_1('#skF_5', '#skF_4', '#skF_6', D_261) | ~m1_pre_topc(D_261, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_68, c_74, c_260])).
% 7.20/2.40  tff(c_1727, plain, (k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_5')='#skF_6' | ~m1_pre_topc('#skF_5', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1719, c_261])).
% 7.20/2.40  tff(c_1734, plain, (k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_163, c_1727])).
% 7.20/2.40  tff(c_960, plain, (![C_378, B_379]: (k1_funct_1('#skF_6', '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), C_378, u1_struct_0(B_379)))='#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), C_378, u1_struct_0(B_379)) | ~m1_pre_topc(B_379, '#skF_4') | v2_struct_0(B_379) | k2_partfun1(u1_struct_0(B_379), u1_struct_0('#skF_4'), C_378, u1_struct_0('#skF_5'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0(B_379))) | ~m1_subset_1(C_378, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_379), u1_struct_0('#skF_4')))) | ~v1_funct_2(C_378, u1_struct_0(B_379), u1_struct_0('#skF_4')) | ~v1_funct_1(C_378) | v1_xboole_0(u1_struct_0(B_379)))), inference(negUnitSimplification, [status(thm)], [c_74, c_407])).
% 7.20/2.40  tff(c_971, plain, (k1_funct_1('#skF_6', '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5')))='#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5')) | ~m1_pre_topc('#skF_5', '#skF_4') | v2_struct_0('#skF_5') | k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_60, c_960])).
% 7.20/2.40  tff(c_979, plain, (k1_funct_1('#skF_6', '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5')))='#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5')) | v2_struct_0('#skF_5') | k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_66, c_971])).
% 7.20/2.40  tff(c_980, plain, (k1_funct_1('#skF_6', '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5')))='#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5')) | k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_330, c_68, c_979])).
% 7.20/2.40  tff(c_981, plain, (~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_980])).
% 7.20/2.40  tff(c_984, plain, (~m1_pre_topc('#skF_5', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_42, c_981])).
% 7.20/2.40  tff(c_988, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_163, c_984])).
% 7.20/2.40  tff(c_990, plain, (m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_980])).
% 7.20/2.40  tff(c_1215, plain, (![A_412, B_413, C_414, C_415]: (k3_funct_2(A_412, B_413, C_414, '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), C_415, A_412))=k1_funct_1(C_414, '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), C_415, A_412)) | ~m1_subset_1(C_414, k1_zfmisc_1(k2_zfmisc_1(A_412, B_413))) | ~v1_funct_2(C_414, A_412, B_413) | ~v1_funct_1(C_414) | k2_partfun1(A_412, u1_struct_0('#skF_4'), C_415, u1_struct_0('#skF_5'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_412)) | ~m1_subset_1(C_415, k1_zfmisc_1(k2_zfmisc_1(A_412, u1_struct_0('#skF_4')))) | ~v1_funct_2(C_415, A_412, u1_struct_0('#skF_4')) | ~v1_funct_1(C_415) | v1_xboole_0(A_412))), inference(resolution, [status(thm)], [c_331, c_12])).
% 7.20/2.40  tff(c_1226, plain, (![B_413, C_414]: (k3_funct_2(u1_struct_0('#skF_5'), B_413, C_414, '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5')))=k1_funct_1(C_414, '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5'))) | ~m1_subset_1(C_414, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), B_413))) | ~v1_funct_2(C_414, u1_struct_0('#skF_5'), B_413) | ~v1_funct_1(C_414) | k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | v1_xboole_0(u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_60, c_1215])).
% 7.20/2.40  tff(c_1235, plain, (![B_413, C_414]: (k3_funct_2(u1_struct_0('#skF_5'), B_413, C_414, '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5')))=k1_funct_1(C_414, '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5'))) | ~m1_subset_1(C_414, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), B_413))) | ~v1_funct_2(C_414, u1_struct_0('#skF_5'), B_413) | ~v1_funct_1(C_414) | k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'))='#skF_6' | v1_xboole_0(u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_990, c_1226])).
% 7.20/2.40  tff(c_1236, plain, (![B_413, C_414]: (k3_funct_2(u1_struct_0('#skF_5'), B_413, C_414, '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5')))=k1_funct_1(C_414, '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5'))) | ~m1_subset_1(C_414, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), B_413))) | ~v1_funct_2(C_414, u1_struct_0('#skF_5'), B_413) | ~v1_funct_1(C_414) | k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'))='#skF_6')), inference(negUnitSimplification, [status(thm)], [c_330, c_1235])).
% 7.20/2.40  tff(c_1237, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'))='#skF_6'), inference(splitLeft, [status(thm)], [c_1236])).
% 7.20/2.40  tff(c_1241, plain, (k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_5')='#skF_6' | ~m1_pre_topc('#skF_5', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1237, c_261])).
% 7.20/2.40  tff(c_1248, plain, (k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_163, c_1241])).
% 7.20/2.40  tff(c_545, plain, (![C_318, B_319]: (k1_funct_1('#skF_6', '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), C_318, u1_struct_0(B_319)))='#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), C_318, u1_struct_0(B_319)) | ~m1_pre_topc(B_319, '#skF_4') | v2_struct_0(B_319) | k2_partfun1(u1_struct_0(B_319), u1_struct_0('#skF_4'), C_318, u1_struct_0('#skF_5'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0(B_319))) | ~m1_subset_1(C_318, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_319), u1_struct_0('#skF_4')))) | ~v1_funct_2(C_318, u1_struct_0(B_319), u1_struct_0('#skF_4')) | ~v1_funct_1(C_318) | v1_xboole_0(u1_struct_0(B_319)))), inference(negUnitSimplification, [status(thm)], [c_74, c_407])).
% 7.20/2.40  tff(c_556, plain, (k1_funct_1('#skF_6', '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5')))='#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5')) | ~m1_pre_topc('#skF_5', '#skF_4') | v2_struct_0('#skF_5') | k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_60, c_545])).
% 7.20/2.40  tff(c_564, plain, (k1_funct_1('#skF_6', '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5')))='#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5')) | v2_struct_0('#skF_5') | k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_66, c_556])).
% 7.20/2.40  tff(c_565, plain, (k1_funct_1('#skF_6', '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5')))='#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5')) | k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_330, c_68, c_564])).
% 7.20/2.40  tff(c_567, plain, (~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_565])).
% 7.20/2.40  tff(c_570, plain, (~m1_pre_topc('#skF_5', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_42, c_567])).
% 7.20/2.40  tff(c_574, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_163, c_570])).
% 7.20/2.40  tff(c_576, plain, (m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_565])).
% 7.20/2.40  tff(c_789, plain, (![A_355, B_356, C_357, C_358]: (k3_funct_2(A_355, B_356, C_357, '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), C_358, A_355))=k1_funct_1(C_357, '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), C_358, A_355)) | ~m1_subset_1(C_357, k1_zfmisc_1(k2_zfmisc_1(A_355, B_356))) | ~v1_funct_2(C_357, A_355, B_356) | ~v1_funct_1(C_357) | k2_partfun1(A_355, u1_struct_0('#skF_4'), C_358, u1_struct_0('#skF_5'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_355)) | ~m1_subset_1(C_358, k1_zfmisc_1(k2_zfmisc_1(A_355, u1_struct_0('#skF_4')))) | ~v1_funct_2(C_358, A_355, u1_struct_0('#skF_4')) | ~v1_funct_1(C_358) | v1_xboole_0(A_355))), inference(resolution, [status(thm)], [c_331, c_12])).
% 7.20/2.40  tff(c_800, plain, (![B_356, C_357]: (k3_funct_2(u1_struct_0('#skF_5'), B_356, C_357, '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5')))=k1_funct_1(C_357, '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5'))) | ~m1_subset_1(C_357, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), B_356))) | ~v1_funct_2(C_357, u1_struct_0('#skF_5'), B_356) | ~v1_funct_1(C_357) | k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | v1_xboole_0(u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_60, c_789])).
% 7.20/2.40  tff(c_809, plain, (![B_356, C_357]: (k3_funct_2(u1_struct_0('#skF_5'), B_356, C_357, '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5')))=k1_funct_1(C_357, '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5'))) | ~m1_subset_1(C_357, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), B_356))) | ~v1_funct_2(C_357, u1_struct_0('#skF_5'), B_356) | ~v1_funct_1(C_357) | k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'))='#skF_6' | v1_xboole_0(u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_576, c_800])).
% 7.20/2.40  tff(c_810, plain, (![B_356, C_357]: (k3_funct_2(u1_struct_0('#skF_5'), B_356, C_357, '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5')))=k1_funct_1(C_357, '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5'))) | ~m1_subset_1(C_357, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), B_356))) | ~v1_funct_2(C_357, u1_struct_0('#skF_5'), B_356) | ~v1_funct_1(C_357) | k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'))='#skF_6')), inference(negUnitSimplification, [status(thm)], [c_330, c_809])).
% 7.20/2.40  tff(c_811, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'))='#skF_6'), inference(splitLeft, [status(thm)], [c_810])).
% 7.20/2.40  tff(c_815, plain, (k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_5')='#skF_6' | ~m1_pre_topc('#skF_5', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_811, c_261])).
% 7.20/2.40  tff(c_822, plain, (k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_163, c_815])).
% 7.20/2.40  tff(c_412, plain, (![B_301, C_299, D_303, E_302, A_300]: (m1_subset_1('#skF_3'(C_299, A_300, B_301, E_302, D_303), u1_struct_0(B_301)) | r2_funct_2(u1_struct_0(C_299), u1_struct_0(A_300), k2_tmap_1(B_301, A_300, D_303, C_299), E_302) | ~m1_subset_1(E_302, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_299), u1_struct_0(A_300)))) | ~v1_funct_2(E_302, u1_struct_0(C_299), u1_struct_0(A_300)) | ~v1_funct_1(E_302) | ~m1_subset_1(D_303, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_301), u1_struct_0(A_300)))) | ~v1_funct_2(D_303, u1_struct_0(B_301), u1_struct_0(A_300)) | ~v1_funct_1(D_303) | ~m1_pre_topc(C_299, B_301) | v2_struct_0(C_299) | ~l1_pre_topc(B_301) | ~v2_pre_topc(B_301) | v2_struct_0(B_301) | ~l1_pre_topc(A_300) | ~v2_pre_topc(A_300) | v2_struct_0(A_300))), inference(cnfTransformation, [status(thm)], [f_253])).
% 7.20/2.40  tff(c_419, plain, (![B_301, D_303]: (m1_subset_1('#skF_3'('#skF_5', '#skF_4', B_301, '#skF_6', D_303), u1_struct_0(B_301)) | r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1(B_301, '#skF_4', D_303, '#skF_5'), '#skF_6') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(D_303, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_301), u1_struct_0('#skF_4')))) | ~v1_funct_2(D_303, u1_struct_0(B_301), u1_struct_0('#skF_4')) | ~v1_funct_1(D_303) | ~m1_pre_topc('#skF_5', B_301) | v2_struct_0('#skF_5') | ~l1_pre_topc(B_301) | ~v2_pre_topc(B_301) | v2_struct_0(B_301) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_60, c_412])).
% 7.20/2.40  tff(c_424, plain, (![B_301, D_303]: (m1_subset_1('#skF_3'('#skF_5', '#skF_4', B_301, '#skF_6', D_303), u1_struct_0(B_301)) | r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1(B_301, '#skF_4', D_303, '#skF_5'), '#skF_6') | ~m1_subset_1(D_303, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_301), u1_struct_0('#skF_4')))) | ~v1_funct_2(D_303, u1_struct_0(B_301), u1_struct_0('#skF_4')) | ~v1_funct_1(D_303) | ~m1_pre_topc('#skF_5', B_301) | v2_struct_0('#skF_5') | ~l1_pre_topc(B_301) | ~v2_pre_topc(B_301) | v2_struct_0(B_301) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_64, c_62, c_419])).
% 7.20/2.40  tff(c_426, plain, (![B_304, D_305]: (m1_subset_1('#skF_3'('#skF_5', '#skF_4', B_304, '#skF_6', D_305), u1_struct_0(B_304)) | r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1(B_304, '#skF_4', D_305, '#skF_5'), '#skF_6') | ~m1_subset_1(D_305, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_304), u1_struct_0('#skF_4')))) | ~v1_funct_2(D_305, u1_struct_0(B_304), u1_struct_0('#skF_4')) | ~v1_funct_1(D_305) | ~m1_pre_topc('#skF_5', B_304) | ~l1_pre_topc(B_304) | ~v2_pre_topc(B_304) | v2_struct_0(B_304))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_424])).
% 7.20/2.40  tff(c_434, plain, (m1_subset_1('#skF_3'('#skF_5', '#skF_4', '#skF_5', '#skF_6', '#skF_6'), u1_struct_0('#skF_5')) | r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_5'), '#skF_6') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_60, c_426])).
% 7.20/2.40  tff(c_442, plain, (m1_subset_1('#skF_3'('#skF_5', '#skF_4', '#skF_5', '#skF_6', '#skF_6'), u1_struct_0('#skF_5')) | r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_5'), '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_91, c_163, c_64, c_62, c_434])).
% 7.20/2.40  tff(c_443, plain, (m1_subset_1('#skF_3'('#skF_5', '#skF_4', '#skF_5', '#skF_6', '#skF_6'), u1_struct_0('#skF_5')) | r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_68, c_442])).
% 7.20/2.40  tff(c_444, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_443])).
% 7.20/2.40  tff(c_16, plain, (![D_14, C_13, A_11, B_12]: (D_14=C_13 | ~r2_funct_2(A_11, B_12, C_13, D_14) | ~m1_subset_1(D_14, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))) | ~v1_funct_2(D_14, A_11, B_12) | ~v1_funct_1(D_14) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))) | ~v1_funct_2(C_13, A_11, B_12) | ~v1_funct_1(C_13))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.20/2.40  tff(c_446, plain, (k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_5')='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4')))) | ~v1_funct_2(k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1(k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_5'))), inference(resolution, [status(thm)], [c_444, c_16])).
% 7.20/2.40  tff(c_449, plain, (k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_5')='#skF_6' | ~m1_subset_1(k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4')))) | ~v1_funct_2(k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1(k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_446])).
% 7.20/2.40  tff(c_462, plain, (~v1_funct_1(k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_449])).
% 7.20/2.40  tff(c_858, plain, (~v1_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_822, c_462])).
% 7.20/2.40  tff(c_862, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_858])).
% 7.20/2.40  tff(c_864, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'))!='#skF_6'), inference(splitRight, [status(thm)], [c_810])).
% 7.20/2.40  tff(c_870, plain, (![B_362, C_363]: (k3_funct_2(u1_struct_0('#skF_5'), B_362, C_363, '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5')))=k1_funct_1(C_363, '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5'))) | ~m1_subset_1(C_363, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), B_362))) | ~v1_funct_2(C_363, u1_struct_0('#skF_5'), B_362) | ~v1_funct_1(C_363))), inference(splitRight, [status(thm)], [c_810])).
% 7.20/2.40  tff(c_18, plain, (![A_15, B_47, C_63, E_75, D_71]: (k3_funct_2(A_15, B_47, C_63, '#skF_2'(B_47, E_75, D_71, C_63, A_15))!=k1_funct_1(E_75, '#skF_2'(B_47, E_75, D_71, C_63, A_15)) | k2_partfun1(A_15, B_47, C_63, D_71)=E_75 | ~m1_subset_1(E_75, k1_zfmisc_1(k2_zfmisc_1(D_71, B_47))) | ~v1_funct_2(E_75, D_71, B_47) | ~v1_funct_1(E_75) | ~m1_subset_1(D_71, k1_zfmisc_1(A_15)) | v1_xboole_0(D_71) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_15, B_47))) | ~v1_funct_2(C_63, A_15, B_47) | ~v1_funct_1(C_63) | v1_xboole_0(B_47) | v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.20/2.40  tff(c_876, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_870, c_18])).
% 7.20/2.40  tff(c_883, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'))='#skF_6' | v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_576, c_876])).
% 7.20/2.40  tff(c_885, plain, $false, inference(negUnitSimplification, [status(thm)], [c_330, c_304, c_864, c_883])).
% 7.20/2.40  tff(c_886, plain, (~v1_funct_2(k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~m1_subset_1(k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4')))) | k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_449])).
% 7.20/2.40  tff(c_902, plain, (~m1_subset_1(k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))))), inference(splitLeft, [status(thm)], [c_886])).
% 7.20/2.40  tff(c_1252, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_1248, c_902])).
% 7.20/2.40  tff(c_1257, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_1252])).
% 7.20/2.40  tff(c_1259, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'))!='#skF_6'), inference(splitRight, [status(thm)], [c_1236])).
% 7.20/2.40  tff(c_1275, plain, (![B_420, C_421]: (k3_funct_2(u1_struct_0('#skF_5'), B_420, C_421, '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5')))=k1_funct_1(C_421, '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5'))) | ~m1_subset_1(C_421, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), B_420))) | ~v1_funct_2(C_421, u1_struct_0('#skF_5'), B_420) | ~v1_funct_1(C_421))), inference(splitRight, [status(thm)], [c_1236])).
% 7.20/2.40  tff(c_1281, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1275, c_18])).
% 7.20/2.40  tff(c_1288, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'))='#skF_6' | v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_990, c_1281])).
% 7.20/2.40  tff(c_1290, plain, $false, inference(negUnitSimplification, [status(thm)], [c_330, c_304, c_1259, c_1288])).
% 7.20/2.40  tff(c_1291, plain, (~v1_funct_2(k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_886])).
% 7.20/2.40  tff(c_1366, plain, (~v1_funct_2(k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_1291])).
% 7.20/2.40  tff(c_1738, plain, (~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1734, c_1366])).
% 7.20/2.40  tff(c_1744, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_1738])).
% 7.20/2.40  tff(c_1746, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'))!='#skF_6'), inference(splitRight, [status(thm)], [c_1718])).
% 7.20/2.40  tff(c_1752, plain, (![B_478, C_479]: (k3_funct_2(u1_struct_0('#skF_5'), B_478, C_479, '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5')))=k1_funct_1(C_479, '#skF_2'(u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5'))) | ~m1_subset_1(C_479, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), B_478))) | ~v1_funct_2(C_479, u1_struct_0('#skF_5'), B_478) | ~v1_funct_1(C_479))), inference(splitRight, [status(thm)], [c_1718])).
% 7.20/2.40  tff(c_1758, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1752, c_18])).
% 7.20/2.40  tff(c_1765, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', u1_struct_0('#skF_5'))='#skF_6' | v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_1411, c_1758])).
% 7.20/2.40  tff(c_1767, plain, $false, inference(negUnitSimplification, [status(thm)], [c_330, c_304, c_1746, c_1765])).
% 7.20/2.40  tff(c_1768, plain, (k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_1291])).
% 7.20/2.40  tff(c_888, plain, (![C_364, D_368, E_367, B_366, A_365]: (r2_hidden('#skF_3'(C_364, A_365, B_366, E_367, D_368), u1_struct_0(C_364)) | r2_funct_2(u1_struct_0(C_364), u1_struct_0(A_365), k2_tmap_1(B_366, A_365, D_368, C_364), E_367) | ~m1_subset_1(E_367, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_364), u1_struct_0(A_365)))) | ~v1_funct_2(E_367, u1_struct_0(C_364), u1_struct_0(A_365)) | ~v1_funct_1(E_367) | ~m1_subset_1(D_368, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_366), u1_struct_0(A_365)))) | ~v1_funct_2(D_368, u1_struct_0(B_366), u1_struct_0(A_365)) | ~v1_funct_1(D_368) | ~m1_pre_topc(C_364, B_366) | v2_struct_0(C_364) | ~l1_pre_topc(B_366) | ~v2_pre_topc(B_366) | v2_struct_0(B_366) | ~l1_pre_topc(A_365) | ~v2_pre_topc(A_365) | v2_struct_0(A_365))), inference(cnfTransformation, [status(thm)], [f_253])).
% 7.20/2.40  tff(c_2003, plain, (![B_508, A_509, B_510, D_511]: (r2_hidden('#skF_3'(B_508, A_509, B_510, k4_tmap_1(A_509, B_508), D_511), u1_struct_0(B_508)) | r2_funct_2(u1_struct_0(B_508), u1_struct_0(A_509), k2_tmap_1(B_510, A_509, D_511, B_508), k4_tmap_1(A_509, B_508)) | ~v1_funct_2(k4_tmap_1(A_509, B_508), u1_struct_0(B_508), u1_struct_0(A_509)) | ~v1_funct_1(k4_tmap_1(A_509, B_508)) | ~m1_subset_1(D_511, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_510), u1_struct_0(A_509)))) | ~v1_funct_2(D_511, u1_struct_0(B_510), u1_struct_0(A_509)) | ~v1_funct_1(D_511) | ~m1_pre_topc(B_508, B_510) | v2_struct_0(B_508) | ~l1_pre_topc(B_510) | ~v2_pre_topc(B_510) | v2_struct_0(B_510) | ~m1_pre_topc(B_508, A_509) | ~l1_pre_topc(A_509) | ~v2_pre_topc(A_509) | v2_struct_0(A_509))), inference(resolution, [status(thm)], [c_36, c_888])).
% 7.20/2.40  tff(c_2008, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6'), u1_struct_0('#skF_5')) | r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', k4_tmap_1('#skF_4', '#skF_5')) | ~v1_funct_2(k4_tmap_1('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1(k4_tmap_1('#skF_4', '#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1768, c_2003])).
% 7.20/2.40  tff(c_2011, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6'), u1_struct_0('#skF_5')) | r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', k4_tmap_1('#skF_4', '#skF_5')) | ~v1_funct_2(k4_tmap_1('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1(k4_tmap_1('#skF_4', '#skF_5')) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_105, c_91, c_163, c_64, c_62, c_60, c_2008])).
% 7.20/2.40  tff(c_2012, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6'), u1_struct_0('#skF_5')) | r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', k4_tmap_1('#skF_4', '#skF_5')) | ~v1_funct_2(k4_tmap_1('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1(k4_tmap_1('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_2011])).
% 7.20/2.40  tff(c_2013, plain, (~v1_funct_1(k4_tmap_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_2012])).
% 7.20/2.40  tff(c_2016, plain, (~m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_40, c_2013])).
% 7.20/2.40  tff(c_2019, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_2016])).
% 7.20/2.40  tff(c_2021, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_2019])).
% 7.20/2.40  tff(c_2023, plain, (v1_funct_1(k4_tmap_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_2012])).
% 7.20/2.40  tff(c_38, plain, (![A_107, B_108]: (v1_funct_2(k4_tmap_1(A_107, B_108), u1_struct_0(B_108), u1_struct_0(A_107)) | ~m1_pre_topc(B_108, A_107) | ~l1_pre_topc(A_107) | ~v2_pre_topc(A_107) | v2_struct_0(A_107))), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.20/2.40  tff(c_2022, plain, (~v1_funct_2(k4_tmap_1('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', k4_tmap_1('#skF_4', '#skF_5')) | r2_hidden('#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6'), u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_2012])).
% 7.20/2.40  tff(c_2039, plain, (~v1_funct_2(k4_tmap_1('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_2022])).
% 7.20/2.40  tff(c_2042, plain, (~m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_38, c_2039])).
% 7.20/2.40  tff(c_2045, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_2042])).
% 7.20/2.40  tff(c_2047, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_2045])).
% 7.20/2.40  tff(c_2049, plain, (v1_funct_2(k4_tmap_1('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_2022])).
% 7.20/2.40  tff(c_2048, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6'), u1_struct_0('#skF_5')) | r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', k4_tmap_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_2022])).
% 7.20/2.40  tff(c_2050, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', k4_tmap_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_2048])).
% 7.20/2.40  tff(c_2052, plain, (k4_tmap_1('#skF_4', '#skF_5')='#skF_6' | ~m1_subset_1(k4_tmap_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4')))) | ~v1_funct_2(k4_tmap_1('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1(k4_tmap_1('#skF_4', '#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_2050, c_16])).
% 7.20/2.40  tff(c_2055, plain, (k4_tmap_1('#skF_4', '#skF_5')='#skF_6' | ~m1_subset_1(k4_tmap_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_2023, c_2049, c_2052])).
% 7.20/2.40  tff(c_2072, plain, (~m1_subset_1(k4_tmap_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))))), inference(splitLeft, [status(thm)], [c_2055])).
% 7.20/2.40  tff(c_2075, plain, (~m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_2072])).
% 7.20/2.40  tff(c_2078, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_2075])).
% 7.20/2.40  tff(c_2080, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_2078])).
% 7.20/2.40  tff(c_2081, plain, (k4_tmap_1('#skF_4', '#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_2055])).
% 7.20/2.40  tff(c_56, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k4_tmap_1('#skF_4', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_303])).
% 7.20/2.40  tff(c_2086, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2081, c_56])).
% 7.20/2.40  tff(c_2092, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_121, c_2086])).
% 7.20/2.40  tff(c_2094, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', k4_tmap_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_2048])).
% 7.20/2.40  tff(c_2125, plain, (![B_523, A_524, B_525, D_526]: (m1_subset_1('#skF_3'(B_523, A_524, B_525, k4_tmap_1(A_524, B_523), D_526), u1_struct_0(B_525)) | r2_funct_2(u1_struct_0(B_523), u1_struct_0(A_524), k2_tmap_1(B_525, A_524, D_526, B_523), k4_tmap_1(A_524, B_523)) | ~v1_funct_2(k4_tmap_1(A_524, B_523), u1_struct_0(B_523), u1_struct_0(A_524)) | ~v1_funct_1(k4_tmap_1(A_524, B_523)) | ~m1_subset_1(D_526, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_525), u1_struct_0(A_524)))) | ~v1_funct_2(D_526, u1_struct_0(B_525), u1_struct_0(A_524)) | ~v1_funct_1(D_526) | ~m1_pre_topc(B_523, B_525) | v2_struct_0(B_523) | ~l1_pre_topc(B_525) | ~v2_pre_topc(B_525) | v2_struct_0(B_525) | ~m1_pre_topc(B_523, A_524) | ~l1_pre_topc(A_524) | ~v2_pre_topc(A_524) | v2_struct_0(A_524))), inference(resolution, [status(thm)], [c_36, c_412])).
% 7.20/2.40  tff(c_2136, plain, (m1_subset_1('#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6'), u1_struct_0('#skF_5')) | r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', k4_tmap_1('#skF_4', '#skF_5')) | ~v1_funct_2(k4_tmap_1('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1(k4_tmap_1('#skF_4', '#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1768, c_2125])).
% 7.20/2.40  tff(c_2141, plain, (m1_subset_1('#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6'), u1_struct_0('#skF_5')) | r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', k4_tmap_1('#skF_4', '#skF_5')) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_105, c_91, c_163, c_64, c_62, c_60, c_2023, c_2049, c_2136])).
% 7.20/2.40  tff(c_2142, plain, (m1_subset_1('#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_2094, c_2141])).
% 7.20/2.40  tff(c_2149, plain, (![A_85]: (m1_subset_1('#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6'), u1_struct_0(A_85)) | ~m1_pre_topc('#skF_5', A_85) | v2_struct_0('#skF_5') | ~l1_pre_topc(A_85) | v2_struct_0(A_85))), inference(resolution, [status(thm)], [c_2142, c_32])).
% 7.20/2.40  tff(c_2160, plain, (![A_527]: (m1_subset_1('#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6'), u1_struct_0(A_527)) | ~m1_pre_topc('#skF_5', A_527) | ~l1_pre_topc(A_527) | v2_struct_0(A_527))), inference(negUnitSimplification, [status(thm)], [c_68, c_2149])).
% 7.20/2.40  tff(c_2093, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6'), u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_2048])).
% 7.20/2.40  tff(c_2121, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6'))='#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6') | ~m1_subset_1('#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_2093, c_58])).
% 7.20/2.40  tff(c_2123, plain, (~m1_subset_1('#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6'), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_2121])).
% 7.20/2.40  tff(c_2166, plain, (~m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_2160, c_2123])).
% 7.20/2.40  tff(c_2174, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_2166])).
% 7.20/2.40  tff(c_2176, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_2174])).
% 7.20/2.40  tff(c_2178, plain, (m1_subset_1('#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6'), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_2121])).
% 7.20/2.40  tff(c_54, plain, (![A_181, B_185, C_187]: (k1_funct_1(k4_tmap_1(A_181, B_185), C_187)=C_187 | ~r2_hidden(C_187, u1_struct_0(B_185)) | ~m1_subset_1(C_187, u1_struct_0(A_181)) | ~m1_pre_topc(B_185, A_181) | v2_struct_0(B_185) | ~l1_pre_topc(A_181) | ~v2_pre_topc(A_181) | v2_struct_0(A_181))), inference(cnfTransformation, [status(thm)], [f_273])).
% 7.20/2.40  tff(c_2111, plain, (![A_181]: (k1_funct_1(k4_tmap_1(A_181, '#skF_5'), '#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6'))='#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6') | ~m1_subset_1('#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6'), u1_struct_0(A_181)) | ~m1_pre_topc('#skF_5', A_181) | v2_struct_0('#skF_5') | ~l1_pre_topc(A_181) | ~v2_pre_topc(A_181) | v2_struct_0(A_181))), inference(resolution, [status(thm)], [c_2093, c_54])).
% 7.20/2.40  tff(c_2276, plain, (![A_540]: (k1_funct_1(k4_tmap_1(A_540, '#skF_5'), '#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6'))='#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6') | ~m1_subset_1('#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6'), u1_struct_0(A_540)) | ~m1_pre_topc('#skF_5', A_540) | ~l1_pre_topc(A_540) | ~v2_pre_topc(A_540) | v2_struct_0(A_540))), inference(negUnitSimplification, [status(thm)], [c_68, c_2111])).
% 7.20/2.40  tff(c_2290, plain, (k1_funct_1(k4_tmap_1('#skF_4', '#skF_5'), '#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6'))='#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6') | ~m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_2178, c_2276])).
% 7.20/2.40  tff(c_2299, plain, (k1_funct_1(k4_tmap_1('#skF_4', '#skF_5'), '#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6'))='#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_2290])).
% 7.20/2.40  tff(c_2300, plain, (k1_funct_1(k4_tmap_1('#skF_4', '#skF_5'), '#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6'))='#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_74, c_2299])).
% 7.20/2.40  tff(c_2177, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6'))='#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_2121])).
% 7.20/2.40  tff(c_2230, plain, (![B_533, A_534, B_535, D_536]: (m1_subset_1('#skF_3'(B_533, A_534, B_535, k4_tmap_1(A_534, B_533), D_536), u1_struct_0(B_535)) | r2_funct_2(u1_struct_0(B_533), u1_struct_0(A_534), k2_tmap_1(B_535, A_534, D_536, B_533), k4_tmap_1(A_534, B_533)) | ~v1_funct_2(k4_tmap_1(A_534, B_533), u1_struct_0(B_533), u1_struct_0(A_534)) | ~v1_funct_1(k4_tmap_1(A_534, B_533)) | ~m1_subset_1(D_536, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_535), u1_struct_0(A_534)))) | ~v1_funct_2(D_536, u1_struct_0(B_535), u1_struct_0(A_534)) | ~v1_funct_1(D_536) | ~m1_pre_topc(B_533, B_535) | v2_struct_0(B_533) | ~l1_pre_topc(B_535) | ~v2_pre_topc(B_535) | v2_struct_0(B_535) | ~m1_pre_topc(B_533, A_534) | ~l1_pre_topc(A_534) | ~v2_pre_topc(A_534) | v2_struct_0(A_534))), inference(resolution, [status(thm)], [c_36, c_412])).
% 7.20/2.40  tff(c_2239, plain, (m1_subset_1('#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6'), u1_struct_0('#skF_5')) | r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', k4_tmap_1('#skF_4', '#skF_5')) | ~v1_funct_2(k4_tmap_1('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1(k4_tmap_1('#skF_4', '#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1768, c_2230])).
% 7.20/2.40  tff(c_2244, plain, (m1_subset_1('#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6'), u1_struct_0('#skF_5')) | r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', k4_tmap_1('#skF_4', '#skF_5')) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_105, c_91, c_163, c_64, c_62, c_60, c_2023, c_2049, c_2239])).
% 7.20/2.40  tff(c_2245, plain, (m1_subset_1('#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_2094, c_2244])).
% 7.20/2.40  tff(c_2247, plain, (![B_8, C_9]: (k3_funct_2(u1_struct_0('#skF_5'), B_8, C_9, '#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6'))=k1_funct_1(C_9, '#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6')) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), B_8))) | ~v1_funct_2(C_9, u1_struct_0('#skF_5'), B_8) | ~v1_funct_1(C_9) | v1_xboole_0(u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_2245, c_12])).
% 7.20/2.40  tff(c_2346, plain, (![B_542, C_543]: (k3_funct_2(u1_struct_0('#skF_5'), B_542, C_543, '#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6'))=k1_funct_1(C_543, '#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6')) | ~m1_subset_1(C_543, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), B_542))) | ~v1_funct_2(C_543, u1_struct_0('#skF_5'), B_542) | ~v1_funct_1(C_543))), inference(negUnitSimplification, [status(thm)], [c_330, c_2247])).
% 7.20/2.40  tff(c_2361, plain, (k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', '#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6'))=k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_60, c_2346])).
% 7.20/2.40  tff(c_2367, plain, (k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', '#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6'))='#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_2177, c_2361])).
% 7.20/2.40  tff(c_48, plain, (![A_119, D_175, C_167, B_151, E_179]: (k3_funct_2(u1_struct_0(B_151), u1_struct_0(A_119), D_175, '#skF_3'(C_167, A_119, B_151, E_179, D_175))!=k1_funct_1(E_179, '#skF_3'(C_167, A_119, B_151, E_179, D_175)) | r2_funct_2(u1_struct_0(C_167), u1_struct_0(A_119), k2_tmap_1(B_151, A_119, D_175, C_167), E_179) | ~m1_subset_1(E_179, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_167), u1_struct_0(A_119)))) | ~v1_funct_2(E_179, u1_struct_0(C_167), u1_struct_0(A_119)) | ~v1_funct_1(E_179) | ~m1_subset_1(D_175, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_151), u1_struct_0(A_119)))) | ~v1_funct_2(D_175, u1_struct_0(B_151), u1_struct_0(A_119)) | ~v1_funct_1(D_175) | ~m1_pre_topc(C_167, B_151) | v2_struct_0(C_167) | ~l1_pre_topc(B_151) | ~v2_pre_topc(B_151) | v2_struct_0(B_151) | ~l1_pre_topc(A_119) | ~v2_pre_topc(A_119) | v2_struct_0(A_119))), inference(cnfTransformation, [status(thm)], [f_253])).
% 7.20/2.40  tff(c_2392, plain, (k1_funct_1(k4_tmap_1('#skF_4', '#skF_5'), '#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6'))!='#skF_3'('#skF_5', '#skF_4', '#skF_5', k4_tmap_1('#skF_4', '#skF_5'), '#skF_6') | r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_5'), k4_tmap_1('#skF_4', '#skF_5')) | ~m1_subset_1(k4_tmap_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4')))) | ~v1_funct_2(k4_tmap_1('#skF_4', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1(k4_tmap_1('#skF_4', '#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2367, c_48])).
% 7.20/2.40  tff(c_2396, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', k4_tmap_1('#skF_4', '#skF_5')) | ~m1_subset_1(k4_tmap_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4')))) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_105, c_91, c_163, c_64, c_62, c_60, c_2023, c_2049, c_1768, c_2300, c_2392])).
% 7.20/2.40  tff(c_2397, plain, (~m1_subset_1(k4_tmap_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_2094, c_2396])).
% 7.20/2.40  tff(c_2401, plain, (~m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_2397])).
% 7.20/2.40  tff(c_2404, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_2401])).
% 7.20/2.40  tff(c_2406, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_2404])).
% 7.20/2.40  tff(c_2408, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_443])).
% 7.20/2.40  tff(c_2407, plain, (m1_subset_1('#skF_3'('#skF_5', '#skF_4', '#skF_5', '#skF_6', '#skF_6'), u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_443])).
% 7.20/2.40  tff(c_2412, plain, (![A_85]: (m1_subset_1('#skF_3'('#skF_5', '#skF_4', '#skF_5', '#skF_6', '#skF_6'), u1_struct_0(A_85)) | ~m1_pre_topc('#skF_5', A_85) | v2_struct_0('#skF_5') | ~l1_pre_topc(A_85) | v2_struct_0(A_85))), inference(resolution, [status(thm)], [c_2407, c_32])).
% 7.20/2.40  tff(c_2419, plain, (![A_548]: (m1_subset_1('#skF_3'('#skF_5', '#skF_4', '#skF_5', '#skF_6', '#skF_6'), u1_struct_0(A_548)) | ~m1_pre_topc('#skF_5', A_548) | ~l1_pre_topc(A_548) | v2_struct_0(A_548))), inference(negUnitSimplification, [status(thm)], [c_68, c_2412])).
% 7.20/2.40  tff(c_2426, plain, (![A_549, A_550]: (m1_subset_1('#skF_3'('#skF_5', '#skF_4', '#skF_5', '#skF_6', '#skF_6'), u1_struct_0(A_549)) | ~m1_pre_topc(A_550, A_549) | ~l1_pre_topc(A_549) | v2_struct_0(A_549) | ~m1_pre_topc('#skF_5', A_550) | ~l1_pre_topc(A_550) | v2_struct_0(A_550))), inference(resolution, [status(thm)], [c_2419, c_32])).
% 7.20/2.40  tff(c_2430, plain, (m1_subset_1('#skF_3'('#skF_5', '#skF_4', '#skF_5', '#skF_6', '#skF_6'), u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_5', '#skF_5') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_66, c_2426])).
% 7.20/2.40  tff(c_2437, plain, (m1_subset_1('#skF_3'('#skF_5', '#skF_4', '#skF_5', '#skF_6', '#skF_6'), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_163, c_70, c_2430])).
% 7.20/2.40  tff(c_2438, plain, (m1_subset_1('#skF_3'('#skF_5', '#skF_4', '#skF_5', '#skF_6', '#skF_6'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_68, c_74, c_2437])).
% 7.20/2.40  tff(c_2469, plain, (![A_555, C_554, D_558, B_556, E_557]: (r2_hidden('#skF_3'(C_554, A_555, B_556, E_557, D_558), u1_struct_0(C_554)) | r2_funct_2(u1_struct_0(C_554), u1_struct_0(A_555), k2_tmap_1(B_556, A_555, D_558, C_554), E_557) | ~m1_subset_1(E_557, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_554), u1_struct_0(A_555)))) | ~v1_funct_2(E_557, u1_struct_0(C_554), u1_struct_0(A_555)) | ~v1_funct_1(E_557) | ~m1_subset_1(D_558, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_556), u1_struct_0(A_555)))) | ~v1_funct_2(D_558, u1_struct_0(B_556), u1_struct_0(A_555)) | ~v1_funct_1(D_558) | ~m1_pre_topc(C_554, B_556) | v2_struct_0(C_554) | ~l1_pre_topc(B_556) | ~v2_pre_topc(B_556) | v2_struct_0(B_556) | ~l1_pre_topc(A_555) | ~v2_pre_topc(A_555) | v2_struct_0(A_555))), inference(cnfTransformation, [status(thm)], [f_253])).
% 7.20/2.40  tff(c_2476, plain, (![B_556, D_558]: (r2_hidden('#skF_3'('#skF_5', '#skF_4', B_556, '#skF_6', D_558), u1_struct_0('#skF_5')) | r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1(B_556, '#skF_4', D_558, '#skF_5'), '#skF_6') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(D_558, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_556), u1_struct_0('#skF_4')))) | ~v1_funct_2(D_558, u1_struct_0(B_556), u1_struct_0('#skF_4')) | ~v1_funct_1(D_558) | ~m1_pre_topc('#skF_5', B_556) | v2_struct_0('#skF_5') | ~l1_pre_topc(B_556) | ~v2_pre_topc(B_556) | v2_struct_0(B_556) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_60, c_2469])).
% 7.20/2.40  tff(c_2481, plain, (![B_556, D_558]: (r2_hidden('#skF_3'('#skF_5', '#skF_4', B_556, '#skF_6', D_558), u1_struct_0('#skF_5')) | r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1(B_556, '#skF_4', D_558, '#skF_5'), '#skF_6') | ~m1_subset_1(D_558, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_556), u1_struct_0('#skF_4')))) | ~v1_funct_2(D_558, u1_struct_0(B_556), u1_struct_0('#skF_4')) | ~v1_funct_1(D_558) | ~m1_pre_topc('#skF_5', B_556) | v2_struct_0('#skF_5') | ~l1_pre_topc(B_556) | ~v2_pre_topc(B_556) | v2_struct_0(B_556) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_64, c_62, c_2476])).
% 7.20/2.40  tff(c_2515, plain, (![B_563, D_564]: (r2_hidden('#skF_3'('#skF_5', '#skF_4', B_563, '#skF_6', D_564), u1_struct_0('#skF_5')) | r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1(B_563, '#skF_4', D_564, '#skF_5'), '#skF_6') | ~m1_subset_1(D_564, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_563), u1_struct_0('#skF_4')))) | ~v1_funct_2(D_564, u1_struct_0(B_563), u1_struct_0('#skF_4')) | ~v1_funct_1(D_564) | ~m1_pre_topc('#skF_5', B_563) | ~l1_pre_topc(B_563) | ~v2_pre_topc(B_563) | v2_struct_0(B_563))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_2481])).
% 7.20/2.40  tff(c_2526, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_4', '#skF_5', '#skF_6', '#skF_6'), u1_struct_0('#skF_5')) | r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_5'), '#skF_6') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_60, c_2515])).
% 7.20/2.40  tff(c_2534, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_4', '#skF_5', '#skF_6', '#skF_6'), u1_struct_0('#skF_5')) | r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_5'), '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_91, c_163, c_64, c_62, c_2526])).
% 7.20/2.40  tff(c_2535, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_4', '#skF_5', '#skF_6', '#skF_6'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_68, c_2408, c_2534])).
% 7.20/2.40  tff(c_2540, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_4', '#skF_5', '#skF_6', '#skF_6'))='#skF_3'('#skF_5', '#skF_4', '#skF_5', '#skF_6', '#skF_6') | ~m1_subset_1('#skF_3'('#skF_5', '#skF_4', '#skF_5', '#skF_6', '#skF_6'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_2535, c_58])).
% 7.20/2.40  tff(c_2549, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_4', '#skF_5', '#skF_6', '#skF_6'))='#skF_3'('#skF_5', '#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2438, c_2540])).
% 7.20/2.40  tff(c_2410, plain, (![B_8, C_9]: (k3_funct_2(u1_struct_0('#skF_5'), B_8, C_9, '#skF_3'('#skF_5', '#skF_4', '#skF_5', '#skF_6', '#skF_6'))=k1_funct_1(C_9, '#skF_3'('#skF_5', '#skF_4', '#skF_5', '#skF_6', '#skF_6')) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), B_8))) | ~v1_funct_2(C_9, u1_struct_0('#skF_5'), B_8) | ~v1_funct_1(C_9) | v1_xboole_0(u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_2407, c_12])).
% 7.20/2.40  tff(c_2483, plain, (![B_559, C_560]: (k3_funct_2(u1_struct_0('#skF_5'), B_559, C_560, '#skF_3'('#skF_5', '#skF_4', '#skF_5', '#skF_6', '#skF_6'))=k1_funct_1(C_560, '#skF_3'('#skF_5', '#skF_4', '#skF_5', '#skF_6', '#skF_6')) | ~m1_subset_1(C_560, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), B_559))) | ~v1_funct_2(C_560, u1_struct_0('#skF_5'), B_559) | ~v1_funct_1(C_560))), inference(negUnitSimplification, [status(thm)], [c_330, c_2410])).
% 7.20/2.40  tff(c_2494, plain, (k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', '#skF_3'('#skF_5', '#skF_4', '#skF_5', '#skF_6', '#skF_6'))=k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_4', '#skF_5', '#skF_6', '#skF_6')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_60, c_2483])).
% 7.20/2.40  tff(c_2499, plain, (k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', '#skF_3'('#skF_5', '#skF_4', '#skF_5', '#skF_6', '#skF_6'))=k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_4', '#skF_5', '#skF_6', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_2494])).
% 7.20/2.40  tff(c_2551, plain, (k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_6', '#skF_3'('#skF_5', '#skF_4', '#skF_5', '#skF_6', '#skF_6'))='#skF_3'('#skF_5', '#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2549, c_2499])).
% 7.20/2.40  tff(c_2587, plain, (![E_569, B_568, C_566, A_567, D_570]: (k3_funct_2(u1_struct_0(B_568), u1_struct_0(A_567), D_570, '#skF_3'(C_566, A_567, B_568, E_569, D_570))!=k1_funct_1(E_569, '#skF_3'(C_566, A_567, B_568, E_569, D_570)) | r2_funct_2(u1_struct_0(C_566), u1_struct_0(A_567), k2_tmap_1(B_568, A_567, D_570, C_566), E_569) | ~m1_subset_1(E_569, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_566), u1_struct_0(A_567)))) | ~v1_funct_2(E_569, u1_struct_0(C_566), u1_struct_0(A_567)) | ~v1_funct_1(E_569) | ~m1_subset_1(D_570, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_568), u1_struct_0(A_567)))) | ~v1_funct_2(D_570, u1_struct_0(B_568), u1_struct_0(A_567)) | ~v1_funct_1(D_570) | ~m1_pre_topc(C_566, B_568) | v2_struct_0(C_566) | ~l1_pre_topc(B_568) | ~v2_pre_topc(B_568) | v2_struct_0(B_568) | ~l1_pre_topc(A_567) | ~v2_pre_topc(A_567) | v2_struct_0(A_567))), inference(cnfTransformation, [status(thm)], [f_253])).
% 7.20/2.40  tff(c_2589, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_4', '#skF_5', '#skF_6', '#skF_6'))!='#skF_3'('#skF_5', '#skF_4', '#skF_5', '#skF_6', '#skF_6') | r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_5'), '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2551, c_2587])).
% 7.20/2.40  tff(c_2591, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_5'), '#skF_6') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_105, c_91, c_163, c_64, c_62, c_60, c_64, c_62, c_60, c_2549, c_2589])).
% 7.20/2.40  tff(c_2593, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_2408, c_2591])).
% 7.20/2.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.20/2.40  
% 7.20/2.40  Inference rules
% 7.20/2.40  ----------------------
% 7.20/2.40  #Ref     : 0
% 7.20/2.40  #Sup     : 472
% 7.20/2.40  #Fact    : 0
% 7.20/2.40  #Define  : 0
% 7.20/2.40  #Split   : 41
% 7.20/2.40  #Chain   : 0
% 7.20/2.40  #Close   : 0
% 7.20/2.40  
% 7.20/2.40  Ordering : KBO
% 7.20/2.40  
% 7.20/2.40  Simplification rules
% 7.20/2.40  ----------------------
% 7.20/2.40  #Subsume      : 30
% 7.20/2.40  #Demod        : 522
% 7.20/2.40  #Tautology    : 99
% 7.20/2.40  #SimpNegUnit  : 145
% 7.20/2.40  #BackRed      : 17
% 7.20/2.40  
% 7.20/2.40  #Partial instantiations: 0
% 7.20/2.40  #Strategies tried      : 1
% 7.20/2.40  
% 7.20/2.40  Timing (in seconds)
% 7.20/2.40  ----------------------
% 7.20/2.40  Preprocessing        : 0.43
% 7.20/2.40  Parsing              : 0.21
% 7.20/2.40  CNF conversion       : 0.05
% 7.20/2.40  Main loop            : 1.15
% 7.20/2.40  Inferencing          : 0.40
% 7.20/2.40  Reduction            : 0.33
% 7.20/2.40  Demodulation         : 0.23
% 7.20/2.40  BG Simplification    : 0.06
% 7.20/2.40  Subsumption          : 0.29
% 7.20/2.40  Abstraction          : 0.08
% 7.20/2.40  MUC search           : 0.00
% 7.20/2.40  Cooper               : 0.00
% 7.20/2.40  Total                : 1.67
% 7.20/2.40  Index Insertion      : 0.00
% 7.20/2.40  Index Deletion       : 0.00
% 7.20/2.40  Index Matching       : 0.00
% 7.20/2.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
